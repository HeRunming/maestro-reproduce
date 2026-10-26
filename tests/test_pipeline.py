from pathlib import Path
import pytest
from maestro.agent import Reply, ScriptedSession
from maestro.config import Config
from maestro.contracts import Contract
from maestro.engine import Engine
from maestro.lean import Lean
from maestro.workspace import Workspace

PROJECT = Path('/data/hrm/lean_workspace')


@pytest.mark.lean
async def test_decomposition_pipeline(tmp_path):
    task = PROJECT / 'examples/add_zero.lean'
    c = Contract.load(task)
    scaffold = c.render('theorem helper (n : ℕ) : n + 0 = n := by sorry\n\n'
                        + c.root.signature + ' := by exact helper n')
    finished = scaffold.replace(':= by sorry', ':= by simp')
    prover_count = 0
    def factory(role):
        nonlocal prover_count
        if role == 'prover':
            prover_count += 1
            if prover_count == 1:
                return ScriptedSession([Reply('{"outcome":"stuck_hard","detail":"need helper","failure_scope":"local"}', [], 0, 'end_turn')])
            return ScriptedSession([Reply('', [('w', 'write_proof', {'text': finished})], 0, 'tool_use'),
                                    Reply('{"outcome":"proved"}', [], 0, 'end_turn')])
        if role == 'coordinator':
            return ScriptedSession([Reply('{"actions":[{"op":"DECOMPOSE","target":"add_zero_demo"}]}', [], 0, 'end_turn'),
                                    Reply('{"decision":"CONTINUE"}', [], 0, 'end_turn')])
        if role == 'proposer':
            return ScriptedSession([Reply('{"strategy":"helper","lemmas":[]}', [], 0, 'end_turn')])
        if role == 'judge':
            return ScriptedSession([Reply('{"direction_gate_pass":true,"layering_gate_pass":true,"blockers":[]}', [], 0, 'end_turn')])
        return ScriptedSession([Reply('', [('w', 'write_proof', {'text': scaffold})], 0, 'tool_use'),
                                Reply('{"translated":true}', [], 0, 'end_turn')])
    result = await Engine(Config(), factory).run(task, tmp_path / 'run')
    assert result.status == 'proved', result.detail


@pytest.mark.lean
async def test_transaction_rollback_and_stale_merge(tmp_path):
    c = Contract.load(PROJECT / 'examples/add_zero.lean')
    ws = Workspace(c, Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    base, original = ws.revision, ws.source
    with pytest.raises(ValueError):
        await ws.commit(original.replace('n + 0 = n', 'False'), base)
    assert ws.source == original and ws.revision == base
    candidate = ws.replace_proof(c.root.name, 'by simp')
    await ws.commit(original, base)
    result = await ws.merge_proof(c.root.name, candidate, base)
    assert result.ok and not result.open
