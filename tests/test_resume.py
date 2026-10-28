"""Resuming a run from an earlier revision's complete source."""
import json
from pathlib import Path
import pytest
from maestro.agent import Reply, ScriptedSession
from maestro.config import Config
from maestro.contracts import Contract
from maestro.engine import Engine

PROJECT = Path('/data/hrm/lean_workspace')
TASK = PROJECT / 'examples/two_part.lean'
C = Contract.load(TASK)
PARTIAL = C.render('theorem left_part (n : ℕ) : n + 0 = n := by\n  simp\n\n'
                   'theorem right_part (n : ℕ) : 0 + n = n := by\n  sorry\n\n'
                   + C.root.signature + ' := ⟨left_part n, right_part n⟩')
COMPLETE = PARTIAL.replace('by\n  sorry', 'by\n  simp')


def journal(run):
    return [json.loads(line) for line in (run / 'events.jsonl').read_text().splitlines()]


@pytest.mark.lean
async def test_resume_dispatches_only_remaining_frontier(tmp_path):
    (tmp_path / 'old.lean').write_text(PARTIAL)
    goals = []
    def factory(role):
        if role == 'coordinator':
            return ScriptedSession([Reply('{"decision":"CONTINUE"}', [], 0, 'end_turn')] * 3)
        class Prover(ScriptedSession):
            async def request(self, user, tools):
                if user is not None:
                    goals.append(json.loads(user)['goal'])
                return await super().request(user, tools)
        return Prover([Reply('', [('w', 'write_proof', {'text': COMPLETE})], 0, 'tool_use'),
                       Reply('{"outcome":"proved"}', [], 0, 'end_turn')])
    run = tmp_path / 'run'
    result = await Engine(Config(), factory).run(TASK, run, tmp_path / 'old.lean')
    assert result.status == 'proved', result.detail
    assert goals == ['right_part']  # neither the proved sibling nor the assembled root
    resumed = [e for e in journal(run) if e['kind'] == 'resumed'][0]
    assert resumed['frontier'] == ['right_part'] and resumed['closed'] == 1


@pytest.mark.lean
async def test_resume_from_complete_source_needs_no_workers(tmp_path):
    (tmp_path / 'old.lean').write_text(COMPLETE)
    def factory(role):
        raise AssertionError(f'no session expected, got {role}')
    cfg = Config(mode='plain')  # plain mode creates no coordinator session
    result = await Engine(cfg, factory).run(TASK, tmp_path / 'run', tmp_path / 'old.lean')
    assert result.status == 'proved', result.detail
    assert (tmp_path / 'run' / 'final.lean').read_text() == COMPLETE


@pytest.mark.lean
@pytest.mark.parametrize('bad', [
    PARTIAL.replace('n + 0 = n ∧ 0 + n = n', 'True ∧ True'),   # root signature changed
    PARTIAL.replace('import Mathlib', 'import Mathlib\naxiom cheat : False'),  # frozen region
    PARTIAL.replace('by\n  sorry', 'by\n  exact absurd rfl (by decide : (0:ℕ) ≠ 0)'),  # does not compile
])
async def test_resume_rejects_invalid_source(tmp_path, bad):
    (tmp_path / 'old.lean').write_text(bad)
    def factory(role):
        return ScriptedSession([])
    result = await Engine(Config(), factory).run(TASK, tmp_path / 'run', tmp_path / 'old.lean')
    assert result.status == 'infrastructure_error'
    assert not any(e['kind'] == 'dispatch' for e in journal(tmp_path / 'run'))
