"""Decomposition path: planner rounds, frontier dispatch, concurrent siblings, rebase."""
import json
from pathlib import Path
from types import SimpleNamespace
import pytest
from maestro.agent import Reply, ScriptedSession
from maestro.config import Config
from maestro.contracts import Contract
from maestro.engine import Engine
from maestro.lean import Lean
from maestro.workspace import Workspace

PROJECT = Path('/data/hrm/lean_workspace')
TASK = PROJECT / 'examples/two_part.lean'
C = Contract.load(TASK)
LEFT = 'theorem left_part (n : ℕ) : n + 0 = n := by\n  sorry'
RIGHT = 'theorem right_part (n : ℕ) : 0 + n = n := by\n  sorry'
SCAFFOLD = C.render('\n\n'.join([LEFT, RIGHT, C.root.signature + ' := ⟨left_part n, right_part n⟩']))


def reply(obj):
    return Reply(json.dumps(obj), [], 0, 'end_turn')


def write(source, then):
    return [Reply('', [('w', 'write_proof', {'text': source})], 0, 'tool_use'), reply(then)]


def solved(name, source=SCAFFOLD):
    """`source` with `name` proved by simp (replace_proof only needs contract/source)."""
    return Workspace.replace_proof(SimpleNamespace(contract=C, source=source), name, 'by simp')


class GoalSession(ScriptedSession):
    """Replies depend on the goal in the first request, like a real worker would."""
    def __init__(self, respond):
        super().__init__([])
        self.respond, self.replies = respond, None

    async def request(self, user, tools):
        self.history.append({'user': user})
        if self.replies is None:
            self.replies = iter(self.respond(json.loads(user)))
        return next(self.replies)


def journal(run):
    return [json.loads(line) for line in (run / 'events.jsonl').read_text().splitlines()]


def continue_forever(first):
    def gen():
        yield from first
        while True:
            yield reply({'decision': 'CONTINUE'})
    return gen()


@pytest.mark.lean
async def test_frontier_excludes_assembled_parent(tmp_path):
    check = await Lean(PROJECT).check(C, SCAFFOLD, tmp_path)
    assert check.ok
    assert set(check.open) == {'left_part', 'right_part', 'two_part_demo'}
    assert set(check.frontier) == {'left_part', 'right_part'}
    assert check.root_type_hash


@pytest.mark.lean
async def test_concurrent_sibling_proofs_both_survive(tmp_path):
    """Two provers start from the same scaffold revision; the second merge must not
    revert the first (it used to commit its whole stale snapshot)."""
    def factory(role):
        if role == 'coordinator':
            s = ScriptedSession([])
            s.replies = continue_forever([reply({'decision': 'ACT', 'actions': [
                {'op': 'decompose', 'target': 'two_part_demo', 'explorer_count': 0}]}),
                reply({'decision': 'CONTINUE'})])
            return s
        if role == 'proposer':
            return ScriptedSession([reply({'strategy': 'split'}), reply({'strategy': 'split, typed'})])
        if role == 'judge':
            return ScriptedSession([reply({'direction_gate_pass': True, 'layering_gate_pass': False,
                                           'blockers': ['children untyped']}),
                                    reply({'direction_gate_pass': 'true', 'layering_gate_pass': True,
                                           'blockers': []})])
        if role == 'translator':
            return ScriptedSession(write(SCAFFOLD, {'translated': True}))
        def prover(req):
            if req['goal'] == 'two_part_demo':
                return [reply({'outcome': 'stuck_hard', 'detail': 'needs split', 'extra_field': 1,
                               'approaches_tried': 'simp'})]
            # Both children prove from the scaffold snapshot they were given.
            return write(solved(req['goal'], req['source']), {'outcome': 'proved'})
        return GoalSession(prover)
    run = tmp_path / 'run'
    result = await Engine(Config(concurrency=3), factory).run(TASK, run)
    assert result.status == 'proved', result.detail
    final = (run / 'final.lean').read_text()
    assert final.count('by simp') == 2 and 'sorry' not in final
    events = journal(run)
    dispatched = [e['goal'] for e in events if e['kind'] == 'dispatch' and e['role'] == 'prover']
    assert sorted(dispatched) == ['left_part', 'right_part', 'two_part_demo']
    assert any(e['kind'] == 'stale_rebase' for e in events)
    assert [e['role'] for e in events if e['kind'] == 'dispatch'].count('planner') == 1


@pytest.mark.lean
async def test_stale_planner_result_is_rebased(tmp_path):
    ws = Workspace(C, Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    await ws.commit(SCAFFOLD, ws.revision)
    stale = ws.revision
    await ws.merge('left_part', solved('left_part'), stale)
    assert 'left_part' in ws.check_result.closed
    # Planner worked from the old snapshot: it still has left_part as sorry, and it
    # decomposes right_part through a new helper placed after the root by mistake.
    candidate = C.render('\n\n'.join([
        'theorem left_part (n : ℕ) : n + 0 = n := by\n  omega',
        'theorem right_part (n : ℕ) : 0 + n = n := by\n  exact right_helper n',
        C.root.signature + ' := ⟨left_part n, right_part n⟩',
        'theorem right_helper (n : ℕ) : 0 + n = n := by\n  sorry']))
    result, added = await ws.merge('right_part', candidate, stale, require_change=True)
    assert added == ['right_helper']
    assert 'left_part' in result.closed  # the sibling's proof survived
    assert result.frontier == ['right_helper']
    src = ws.source
    assert src.index('right_helper') < src.index('theorem right_part')
    assert 'by simp' in src and 'omega' not in src  # unrelated edit discarded
    kinds = [e['kind'] for e in journal(tmp_path / 'run')]
    assert 'stale_rebase' in kinds and 'merge_ignored_edits' in kinds


@pytest.mark.lean
async def test_merge_rejections(tmp_path):
    ws = Workspace(C, Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    await ws.commit(SCAFFOLD, ws.revision)
    with pytest.raises(ValueError, match='does not change'):
        await ws.merge('right_part', SCAFFOLD, ws.revision, require_change=True)
    resigned = SCAFFOLD.replace('theorem left_part (n : ℕ) : n + 0 = n', 'theorem left_part (n : ℕ) : True')
    with pytest.raises(ValueError, match='signature'):
        await ws.merge('left_part', resigned, ws.revision)
    await ws.merge('left_part', solved('left_part'), ws.revision)
    with pytest.raises(ValueError, match='already closed'):
        await ws.merge('left_part', solved('left_part'), ws.revision)
    with pytest.raises(ValueError, match='unknown target'):
        ws.rebase('nope', SCAFFOLD)


@pytest.mark.lean
async def test_root_meaning_is_pinned(tmp_path):
    """Same signature text, different meaning: `open Pin in` rebinds an auto-bound `c`."""
    task = tmp_path / 'pin.lean'
    task.write_text('import Mathlib\n\nnamespace Pin\ndef c : ℕ := 1\nend Pin\n\n'
                    'theorem pin_demo (n : ℕ) : c + n = 1 + n := by\n  sorry\n')
    c = Contract.load(task)
    exploit = c.render('theorem helper : True := by\n  trivial\nopen Pin in\n\n'
                       + c.root.signature + ' := by\n  rfl')
    c.validate(exploit)  # the text-level boundary alone does not catch this
    ws = Workspace(c, Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    with pytest.raises(ValueError, match='different type'):
        await ws.commit(exploit, ws.revision)
    assert not ws.proved


@pytest.mark.lean
async def test_negation_must_not_use_root(tmp_path):
    task = tmp_path / 'false.lean'
    task.write_text('import Mathlib\n\ntheorem all_zero (n : ℕ) : n = 0 := by\n  sorry\n')
    ws = Workspace(Contract.load(task), Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    cheat, _, _ = await ws.check_negation('by\n  intro h\n  exact absurd (all_zero 1) (by norm_num)')
    assert not cheat
    real, source, _ = await ws.check_negation('by\n  intro h\n  exact absurd (h 1) (by norm_num)')
    assert real and 'type_of% @all_zero' in source


@pytest.mark.lean
async def test_coordinator_failure_does_not_end_run(tmp_path):
    class Broken(ScriptedSession):
        async def request(self, user, tools):
            raise RuntimeError('provider failed after 4 attempts')
    proof = C.render(C.root.signature + ' := ⟨by simp, by simp⟩')
    attempts = 0
    def factory(role):
        nonlocal attempts
        if role == 'coordinator':
            return Broken([])
        attempts += 1
        if attempts == 1:
            return ScriptedSession([Reply('not json', [], 0, 'end_turn'), Reply('still not', [], 0, 'end_turn')])
        return ScriptedSession(write(proof, {'outcome': 'proved'}))
    run = tmp_path / 'run'
    result = await Engine(Config(), factory).run(TASK, run)
    assert result.status == 'proved', result.detail
    kinds = [e['kind'] for e in journal(run)]
    assert 'coordinator_error' in kinds and kinds.count('dispatch') == 2
