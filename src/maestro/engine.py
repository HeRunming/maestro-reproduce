"""Asynchronous workers and persistent global coordinator."""
import asyncio
import json
from pathlib import Path
import uuid
from .agent import Budget, BudgetExceeded, Session, interact
from .contracts import Contract
from .lean import Lean
from .models import Decision, Diagnosis, Event, Result, Status
from pydantic import ValidationError
from .prompts import prompt
from .tools import Tools
from .workspace import Workspace


class Engine:
    def __init__(self, config, session_factory=None):
        self.config = config
        self.budget = Budget(config.output_budget)
        self.factory = session_factory or (lambda role: Session(config.provider, prompt(role), self.budget))
        self.events = asyncio.Queue()
        self.running = {}
        self.sessions = []
        self.gate = asyncio.Semaphore(config.concurrency)
        self.certificate = None
        self.mcp = None
        self.explorers = {}

    def session(self, role):
        s = self.factory(role)
        self.sessions.append(s)
        return s

    def dispatch(self, role, goal, guidance='', cohort_id=None):
        wid = uuid.uuid4().hex
        task = asyncio.create_task(self.worker(wid, role, goal, guidance, cohort_id))
        self.running[wid] = (task, role, goal)

    async def worker(self, wid, role, goal, guidance, cohort_id):
        ws = self.ws
        revision, source = ws.revision, ws.source
        async def progress(text):
            await self.events.put(Event(kind='progress', worker_id=wid, goal=goal,
                revision=revision, payload={'detail': text}))
        tools = Tools(ws, source, ws.directory / 'workers' / wid, progress, mcp=self.mcp)
        try:
            async with self.gate:
                request = json.dumps({'goal': goal, 'guidance': guidance, 'source': source})
                if role == 'planner':
                    proposer, judge = self.session('proposer'), self.session('judge')
                    read = Tools(ws, source, tools.directory, readonly=True, mcp=self.mcp)
                    accepted = False
                    for _ in range(self.config.planner_rounds):
                        plan = await interact(proposer, request, read, self.config.max_turns)
                        verdict = await interact(judge, json.dumps(plan), read, self.config.max_turns)
                        if verdict.get('direction_gate_pass') is True and verdict.get('layering_gate_pass') is True and not verdict.get('blockers'):
                            accepted = True
                            break
                        request = json.dumps({'plan': plan, 'feedback': verdict})
                    if not accepted:
                        raise ValueError('planner judge rejected plan: ' + json.dumps(verdict))
                    output = await interact(self.session('translator'), json.dumps({'plan': plan, 'source': source}), tools, self.config.max_turns)
                    output['plan'] = plan
                elif role == 'explorer':
                    output = await interact(self.session(role), request, tools, self.config.max_turns)
                    if cohort_id:
                        self.explorers.setdefault(cohort_id, []).append({'worker_id': wid, 'output': output, 'source': tools.source})
                else:
                    output = await interact(self.session(role), request, tools, self.config.max_turns)
                if role == 'prover' and output.get('outcome') != 'proved':
                    Diagnosis.model_validate(output)
                await self.events.put(Event(kind=role, worker_id=wid, goal=goal, revision=revision,
                    payload={'output': output, 'source': tools.source, 'cohort_id': cohort_id}))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            await self.events.put(Event(kind='worker_error', worker_id=wid, goal=goal,
                revision=revision, payload={'error': type(exc).__name__, 'detail': str(exc)}))

    async def falsify(self, event):
        proof = event.payload['output'].get('negation_proof')
        if not proof:
            return
        # Derive the fully quantified proposition from Lean's elaborated type.
        root = self.ws.contract.root.name
        # Use exact suffix match with namespace separator to avoid name collisions
        # (e.g. root "zero" must not match helper "add_nonzero").
        candidates = [i for i in self.ws.check_result.inspections
                      if i.name == root or i.name.endswith('.' + root)]
        if not candidates:
            self.ws.journal.record('falsify_no_root', root=root,
                                   available=[i.name for i in self.ws.check_result.inspections])
            return
        info = candidates[0]
        from .models import Goal
        neg = Goal(name='maestro_root_negation', signature=f'theorem maestro_root_negation : ¬ ({info.type})')
        contract = Contract(self.ws.contract.prefix, self.ws.contract.suffix, neg)
        source = contract.render(neg.signature + ' := ' + proof)
        result = await self.ws.lean.check(contract, source, self.ws.directory / 'falsification')
        if result.ok and not result.open:
            self.certificate = source
            (self.ws.directory / 'falsification.lean').write_text(source)

    async def actions(self, decision):
        ws = self.ws
        for action in decision.actions:
            target = ws.contract.root.name if action.target == 'root' else action.target
            if action.op in ('KEEP',):
                continue
            if action.op in ('ADD_HELPER', 'RESTATE', 'REPAIR_PROOF', 'ABANDON'):
                if not action.source:
                    raise ValueError('source mutation requires full candidate source')
                await ws.commit(action.source, ws.revision)
            elif action.op == 'RETRACT':
                await ws.commit(ws.replace_proof(target, 'by\n  sorry'), ws.revision)
            elif action.op.startswith('REPROVE'):
                self.dispatch('prover', target, action.guidance)
            elif action.op.startswith('DECOMPOSE'):
                if action.op == 'DECOMPOSE_JOINT':
                    # Joint planning: coordinator supplies shared scaffold source.
                    if not action.source:
                        raise ValueError('joint decomposition requires coordinator-supplied scaffold')
                    await ws.commit(action.source, ws.revision)
                    for name in ws.open_goals:
                        self.dispatch('prover', name, action.guidance)
                else:
                    self.dispatch('planner', target, action.guidance)
            elif action.op == 'EXPLORE_ALTERNATIVES':
                cohort_id = uuid.uuid4().hex
                for _ in range(min(action.explorer_count, self.config.explorer_cohort)):
                    self.dispatch('explorer', target, cohort_id=cohort_id)
            elif action.op == 'FALSIFY':
                self.dispatch('falsifier', ws.contract.root.name)
            else:
                raise ValueError('unsupported operation: ' + action.op)

    async def run(self, task: Path, directory: Path):
        cfg = self.config
        self.ws = Workspace(Contract.load(task), Lean(cfg.project, cfg.compile_seconds), directory)
        ws = self.ws
        status, detail = Status.ERROR, ''
        coordinator = None
        if cfg.mcp.enabled:
            from .mcp import LoogleClient
            self.mcp = LoogleClient()
            ws.journal.record('mcp_enabled', client='LoogleClient')
        try:
            await ws.initialize()
            if not ws.check_result.ok:
                raise ValueError('initial task failed validation')
            if cfg.mode == 'maestro':
                coordinator = self.session('coordinator')
            self.dispatch('prover', ws.contract.root.name)
            async with asyncio.timeout(cfg.wall_seconds):
                for _ in range(cfg.max_events):
                    event = await self.events.get()
                    ws.journal.record('event', event=event.model_dump())
                    if event.kind != 'progress':
                        self.running.pop(event.worker_id, None)
                    try:
                        if event.kind == 'prover' and event.payload['output'].get('outcome') == 'proved':
                            await ws.merge_proof(event.goal, event.payload['source'], event.revision)
                        elif event.kind == 'planner':
                            await ws.commit(event.payload['source'], event.revision)
                            for name in ws.open_goals:
                                self.dispatch('prover', name)
                        elif event.kind == 'explorer':
                            cohort_id = event.payload.get('cohort_id')
                            if cohort_id and cohort_id in self.explorers and len(self.explorers[cohort_id]) == cfg.explorer_cohort:
                                ws.journal.record('explorer_cohort_complete', cohort_id=cohort_id, count=len(self.explorers[cohort_id]))
                        elif event.kind == 'falsifier':
                            await self.falsify(event)
                    except (ValueError, TimeoutError) as exc:
                        event.payload['validation_error'] = str(exc)
                    if not ws.open_goals:
                        status = Status.PROVED
                        (directory / 'final.lean').write_text(ws.source)
                        break
                    if self.certificate:
                        status = Status.FALSIFIED
                        break
                    if cfg.mode == 'plain':
                        if not self.running:
                            status, detail = Status.BUDGET, 'plain attempt ended without proof'
                            break
                        continue
                    if cfg.mode == 'naive':
                        if not self.running:
                            self.dispatch('planner', event.goal)
                        continue
                    state = {'source': ws.source, 'revision': ws.revision, 'open': ws.open_goals,
                             'event': event.model_dump(), 'active': [(k, r, g) for k, (_, r, g) in self.running.items()]}
                    raw = await interact(coordinator, json.dumps(state), None, cfg.max_turns)
                    try:
                        decision = Decision.model_validate(raw)
                    except ValidationError as exc:
                        # A malformed decision is a coordinator error, not a run failure.
                        ws.journal.record('decision_rejected', detail=str(exc))
                        decision = None
                    if decision:
                        ws.journal.record('decision', **decision.model_dump())
                        try:
                            if decision.decision in ('PREPARE_DECOMPOSITION', 'SWITCH_TO_DECOMPOSITION') and not decision.actions:
                                self.dispatch('planner', event.goal)
                            else:
                                await self.actions(decision)
                        except ValueError as exc:
                            ws.journal.record('action_rejected', detail=str(exc))
                    # Coordinator source transactions can close the last goal.
                    if not ws.open_goals:
                        status = Status.PROVED
                        (directory / 'final.lean').write_text(ws.source)
                        break
                    if not self.running and ws.open_goals:
                        self.dispatch('prover', ws.open_goals[0])
                else:
                    status, detail = Status.BUDGET, 'event limit reached'
        except (BudgetExceeded, TimeoutError) as exc:
            status, detail = Status.BUDGET, str(exc)
        except asyncio.CancelledError:
            status, detail = Status.CANCELLED, 'cancelled'
        except Exception as exc:
            status, detail = Status.ERROR, f'{type(exc).__name__}: {exc}'
        finally:
            for running_task, _, _ in self.running.values():
                running_task.cancel()
            await asyncio.gather(*(t for t, _, _ in self.running.values()), return_exceptions=True)
            for session in self.sessions:
                await session.close()
            if self.mcp:
                await self.mcp.close()
        result = Result(status=status, run_dir=str(directory), revision=ws.revision,
                        output_tokens=self.budget.used, detail=detail)
        (directory / 'result.json').write_text(result.model_dump_json(indent=2))
        return result
