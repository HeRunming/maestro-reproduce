"""Asynchronous workers and persistent global coordinator."""
import asyncio
import json
from pathlib import Path
import uuid
from pydantic import ValidationError
from .agent import Budget, BudgetExceeded, Session, interact
from .contracts import Contract
from .lean import Lean
from .models import Decision, Diagnosis, Event, Result, Status
from .prompts import prompt
from .tools import Tools
from .workspace import Workspace

TRUE = (True, 'true', 'True', 'yes', 1)


def passed(verdict):
    return (verdict.get('direction_gate_pass') in TRUE and verdict.get('layering_gate_pass') in TRUE
            and not verdict.get('blockers'))


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
        self.cohorts = {}
        self.sent_revision = None

    def session(self, role):
        s = self.factory(role)
        self.sessions.append(s)
        return s

    def dispatch(self, role, goal, guidance='', cohort_id=None):
        wid = uuid.uuid4().hex
        task = asyncio.create_task(self.worker(wid, role, goal, guidance, cohort_id))
        self.running[wid] = (task, role, goal)
        self.ws.journal.record('dispatch', worker_id=wid, role=role, goal=goal, guidance=guidance)
        return wid

    def busy(self, role='prover'):
        return {g for _, r, g in self.running.values() if r == role}

    def dispatch_frontier(self, guidance=''):
        """One prover per frontier goal that has no prover yet."""
        taken = self.busy()
        started = [g for g in self.ws.frontier if g not in taken]
        for name in started:
            self.dispatch('prover', name, guidance)
        return started

    async def worker(self, wid, role, goal, guidance, cohort_id):
        ws = self.ws
        revision, source = ws.revision, ws.source
        async def progress(text):
            await self.events.put(Event(kind='progress', worker_id=wid, goal=goal,
                revision=revision, payload={'detail': text}))
        tools = Tools(ws, source, ws.directory / 'workers' / wid, progress, mcp=self.mcp,
                      negation=role == 'falsifier')
        try:
            async with self.gate:
                request = json.dumps({'goal': goal, 'guidance': guidance, 'source': source})
                if role == 'planner':
                    output = await self.plan(goal, guidance, source, tools)
                else:
                    output = await interact(self.session(role), request, tools, self.config.max_turns)
                if role == 'prover' and output.get('outcome') != 'proved':
                    output = {**output, **Diagnosis.model_validate(output).model_dump()}
                await self.events.put(Event(kind=role, worker_id=wid, goal=goal, revision=revision,
                    payload={'output': output, 'source': tools.source, 'cohort_id': cohort_id}))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            await self.events.put(Event(kind='worker_error', worker_id=wid, goal=goal, revision=revision,
                payload={'role': role, 'error': type(exc).__name__, 'detail': str(exc)[:2000],
                         'cohort_id': cohort_id}))

    async def plan(self, goal, guidance, source, tools):
        """Proposer → judge (up to planner_rounds revisions) → translator."""
        proposer, judge = self.session('proposer'), self.session('judge')
        read = Tools(self.ws, source, tools.directory, readonly=True, mcp=self.mcp)
        request = json.dumps({'goal': goal, 'guidance': guidance, 'source': source})
        plan = verdict = None
        for round_ in range(1, self.config.planner_rounds + 1):
            plan = await interact(proposer, request, read, self.config.max_turns)
            verdict = await interact(judge, json.dumps({'goal': goal, 'source': source, 'plan': plan}),
                                     read, self.config.max_turns)
            self.ws.journal.record('planner_round', goal=goal, round=round_, passed=passed(verdict),
                                   plan=plan, verdict=verdict)
            if passed(verdict):
                break
            request = json.dumps({'goal': goal, 'source': source, 'plan': plan, 'feedback': verdict})
        else:
            raise ValueError('planner judge rejected plan: ' + json.dumps(verdict)[:1500])
        output = await interact(self.session('translator'),
                                json.dumps({'goal': goal, 'source': source, 'plan': plan}),
                                tools, self.config.max_turns)
        return {**output, 'plan': plan, 'verdict': verdict}

    async def falsify(self, event):
        proof = event.payload['output'].get('negation_proof')
        if not proof or not str(proof).strip():
            return
        certified, source, result = await self.ws.check_negation(str(proof))
        event.payload['negation_check'] = {'certified': certified, 'ok': result.ok,
                                           'output': result.output[-2000:]}
        if certified:
            self.certificate = source
            (self.ws.directory / 'falsification.lean').write_text(source)

    def target(self, action):
        ws = self.ws
        name = ws.contract.root.name if action.target in ('root', '') else action.target
        if name not in {g.name for g in ws.goals}:
            raise ValueError(f'{action.op}: unknown target {name}')
        return name

    async def actions(self, decision):
        ws = self.ws
        for action in decision.actions:
            op = action.op
            # One rejected action must not discard the rest of the decision.
            try:
                if op == 'KEEP':
                    continue
                if op in ('ADD_HELPER', 'RESTATE', 'REPAIR_PROOF', 'ABANDON'):
                    if not action.source:
                        raise ValueError(f'{op} requires complete candidate source')
                    await ws.commit(action.source, ws.revision)
                elif op == 'RETRACT':
                    await ws.commit(ws.replace_proof(self.target(action), 'by\n  sorry'), ws.revision)
                elif op.startswith('REPROVE'):
                    name = self.target(action)
                    if name not in ws.open_goals:
                        raise ValueError(f'{op}: {name} is already closed')
                    self.dispatch('prover', name, action.guidance)
                elif op == 'DECOMPOSE_JOINT':
                    # Joint planning: the coordinator supplies the shared scaffold source.
                    if not action.source:
                        raise ValueError('DECOMPOSE_JOINT requires coordinator-supplied scaffold')
                    await ws.commit(action.source, ws.revision)
                    self.dispatch_frontier(action.guidance)
                elif op.startswith('DECOMPOSE'):
                    name = self.target(action)
                    if name not in ws.open_goals:
                        raise ValueError(f'{op}: {name} is already closed')
                    self.dispatch('planner', name, action.guidance)
                elif op == 'EXPLORE_ALTERNATIVES':
                    cohort_id = uuid.uuid4().hex
                    size = min(action.explorer_count, self.config.explorer_cohort)
                    self.cohorts[cohort_id] = {'size': size, 'results': []}
                    for _ in range(size):
                        self.dispatch('explorer', self.target(action), action.guidance, cohort_id)
                elif op == 'FALSIFY':
                    self.dispatch('falsifier', ws.contract.root.name, action.guidance)
                else:
                    raise ValueError('unsupported operation: ' + op)
            except ValueError as exc:
                ws.journal.record('action_rejected', op=op, target=action.target, detail=str(exc)[:2000])

    async def apply(self, event):
        """Fold one worker result into the workspace. Lean, not the worker, decides closure."""
        ws, out = self.ws, event.payload.get('output') or {}
        if event.kind == 'prover' and out.get('outcome') == 'proved':
            result, added = await ws.merge(event.goal, event.payload['source'], event.revision)
            event.payload['merge'] = {'closed': event.goal in result.closed, 'added': added}
            if event.goal not in result.closed:
                ws.journal.record('proof_claim_open', goal=event.goal, added=added)
        elif event.kind == 'planner':
            _, added = await ws.merge(event.goal, event.payload['source'], event.revision,
                                      require_change=True)
            event.payload['merge'] = {'added': added, 'dispatched': self.dispatch_frontier()}
        elif event.kind == 'falsifier':
            await self.falsify(event)
        cohort_id = event.payload.get('cohort_id')
        if cohort_id in self.cohorts and event.kind in ('explorer', 'worker_error'):
            cohort = self.cohorts[cohort_id]
            cohort['results'].append({'worker_id': event.worker_id, 'kind': event.kind, 'output': out})
            if len(cohort['results']) == cohort['size']:
                ws.journal.record('explorer_cohort_complete', cohort_id=cohort_id, count=cohort['size'])
                event.payload['cohort_complete'] = cohort['results']

    async def consult(self, coordinator, event):
        ws = self.ws
        state = {'revision': ws.revision, 'open': ws.open_goals, 'frontier': ws.frontier,
                 'event': event.model_dump(),
                 'active': [{'worker_id': k, 'role': r, 'goal': g} for k, (_, r, g) in self.running.items()]}
        # The coordinator session keeps history; resend source only when it changed.
        if ws.revision != self.sent_revision:
            state['source'] = ws.source
        else:
            state['source_unchanged_since_revision'] = ws.revision
        if event.payload.get('source') == ws.source:
            state['event']['payload'] = {k: v for k, v in event.payload.items() if k != 'source'}
        self.sent_revision = ws.revision
        try:
            raw = await interact(coordinator, json.dumps(state, default=str), None, self.config.max_turns)
            decision = Decision.model_validate(raw)
        except (BudgetExceeded, asyncio.CancelledError):
            raise
        except (ValidationError, ValueError, TypeError) as exc:
            ws.journal.record('decision_rejected', detail=str(exc)[:2000])
            return
        except Exception as exc:  # transport failure after retries: keep the run alive
            ws.journal.record('coordinator_error', error=type(exc).__name__, detail=str(exc)[:2000])
            return
        ws.journal.record('decision', **decision.model_dump())
        if decision.decision in ('PREPARE_DECOMPOSITION', 'SWITCH_TO_DECOMPOSITION') and not decision.actions:
            if event.goal in ws.open_goals:
                self.dispatch('planner', event.goal)
        else:
            await self.actions(decision)

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
            if cfg.mode == 'maestro':
                coordinator = self.session('coordinator')
            self.dispatch(cfg.initial_role if cfg.mode != 'plain' else 'prover', ws.contract.root.name)
            async with asyncio.timeout(cfg.wall_seconds):
                for _ in range(cfg.max_events):
                    event = await self.events.get()
                    if event.kind != 'progress':
                        self.running.pop(event.worker_id, None)
                    try:
                        await self.apply(event)
                    except (ValueError, TimeoutError) as exc:
                        event.payload['rejected'] = str(exc)[:2000]
                        ws.journal.record('event_rejected', worker_id=event.worker_id,
                                          kind=event.kind, goal=event.goal, detail=str(exc)[:2000])
                    ws.journal.record('event', event=event.model_dump())
                    if ws.proved or self.certificate:
                        break
                    if cfg.mode == 'plain':
                        if not self.running:
                            status, detail = Status.BUDGET, 'plain attempt ended without proof'
                            break
                        continue
                    if cfg.mode == 'naive':
                        if not self.running:
                            self.dispatch('planner', ws.frontier[0])
                        continue
                    await self.consult(coordinator, event)
                    if ws.proved:  # coordinator source transactions can close the last goal
                        break
                    if not self.running:
                        # Nothing live and the coordinator dispatched nothing: attack the frontier.
                        self.dispatch_frontier()
                else:
                    status, detail = Status.BUDGET, f'event limit reached ({cfg.max_events})'
            if ws.proved:
                status, detail = Status.PROVED, ''
                (directory / 'final.lean').write_text(ws.source)
            elif self.certificate:
                status, detail = Status.FALSIFIED, ''
        except TimeoutError as exc:
            status, detail = Status.BUDGET, str(exc) or f'wall-clock limit reached ({cfg.wall_seconds}s)'
        except BudgetExceeded as exc:
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
