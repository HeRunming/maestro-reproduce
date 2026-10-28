"""Generated `def` declarations: allowed as data, never goals, and unable to move the root."""
import json
from pathlib import Path
import pytest
from maestro.agent import Reply, ScriptedSession
from maestro.config import Config
from maestro.contracts import Contract
from maestro.engine import Engine
from maestro.lean import Lean
from maestro.workspace import Workspace

PROJECT = Path('/data/hrm/lean_workspace')
C = Contract.load(PROJECT / 'examples/add_zero.lean')
ROOT = C.root.signature


def region(*decls):
    return C.render('\n\n'.join(decls))


def test_defs_parse_as_non_goals():
    goals = C.validate(region('def k : ℕ := 0', 'noncomputable def f (n : ℕ) : ℕ := n + k',
                              'lemma helper (n : ℕ) : n + k = n := by simp [k]',
                              ROOT + ' := by simpa [k] using helper n'))
    assert [(g.name, g.kind) for g in goals] == [('k', 'def'), ('f', 'def'),
                                                 ('helper', 'theorem'), ('add_zero_demo', 'theorem')]
    assert goals[1].signature.startswith('noncomputable def f')


@pytest.mark.parametrize('code', [
    'theorem t : True := trivial\n\n  def k : ℕ := 0',  # indented: not a top-level declaration
    'theorem t : True := by\n  trivial\n  def k : ℕ := 0',
    'abbrev k : ℕ := 0', 'partial def k : ℕ → ℕ := fun n => n', 'unsafe def k : ℕ := 0',
    '@[simp] def k : ℕ := 0', 'instance : Inhabited ℕ := ⟨0⟩', 'noncomputable section',
    'private def k : ℕ := 0', 'protected def k : ℕ := 0', 'def k : ℕ := 0 #eval k',
    'def k : ℕ := 0\n#exit', 'def k : ℕ := by exact (Lean.Elab.Term.elabTerm)',
    'def k : ℕ\n  | _ => 0',                         # no ':=': equation compiler form
])
def test_unsafe_def_forms_rejected(code):
    with pytest.raises(ValueError):
        C.validate(region(code, ROOT + ' := by simp'))


def test_card_notation_allowed():
    C.validate(region('theorem t (s : Finset ℕ) : #(s) = s.card := rfl', ROOT + ' := by simp'))


@pytest.mark.lean
async def test_def_shadowing_cannot_change_root(tmp_path):
    """`c` is auto-bound (so the root is ∀ c n, c + n = 1 + n, false); a generated `def c`
    before the root makes the same text mean 1 + n = 1 + n."""
    task = tmp_path / 'shadow.lean'
    task.write_text('import Mathlib\n\ntheorem shadow_demo (n : ℕ) : c + n = 1 + n := by\n  sorry\n')
    c = Contract.load(task)
    exploit = c.render('def c : ℕ := 1\n\n' + c.root.signature + ' := by\n  rfl')
    c.validate(exploit)
    check = await Lean(PROJECT).check(c, exploit, tmp_path / 'probe')
    assert check.ok and not check.open  # Lean alone would accept it
    ws = Workspace(c, Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    with pytest.raises(ValueError, match='different type'):
        await ws.commit(exploit, ws.revision)
    assert not ws.proved


@pytest.mark.lean
async def test_sorry_in_def_keeps_consumers_open(tmp_path):
    ws = Workspace(C, Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    source = region('def k : ℕ := by\n  sorry', 'theorem uses_k : k = k := rfl',
                    ROOT + ' := by simp')
    result = await ws.commit(source, ws.revision)
    assert result.ok and 'uses_k' in result.open and 'add_zero_demo' in result.closed
    assert 'k' not in result.open + result.closed + result.frontier
    assert not ws.proved


@pytest.mark.lean
async def test_planner_defs_merge_and_are_not_redefined(tmp_path):
    ws = Workspace(C, Lean(PROJECT), tmp_path / 'run')
    await ws.initialize()
    plan = region('def zero_nat : ℕ := 0',
                  'theorem helper (n : ℕ) : n + zero_nat = n := by\n  sorry',
                  ROOT + ' := by simpa [zero_nat] using helper n')
    result, added = await ws.merge('add_zero_demo', plan, ws.revision, require_change=True)
    assert added == ['zero_nat', 'helper'] and result.frontier == ['helper']
    # A prover may not redefine an existing def to make its target easier.
    cheat = plan.replace('def zero_nat : ℕ := 0', 'def zero_nat : ℕ := 0 * 7').replace(
        'n + zero_nat = n := by\n  sorry', 'n + zero_nat = n := by simp [zero_nat]')
    await ws.merge('helper', cheat, ws.revision)
    assert 'def zero_nat : ℕ := 0\n' in ws.source and '0 * 7' not in ws.source
    assert ws.proved
    with pytest.raises(ValueError, match='unknown target'):
        ws.rebase('zero_nat', plan)


@pytest.mark.lean
async def test_coordinator_gets_outline_and_rotates(tmp_path):
    seen = []
    class Recording(ScriptedSession):
        async def request(self, user, tools):
            seen.append(json.loads(user))
            return Reply(json.dumps({'decision': 'CONTINUE'}), [], 0, 'end_turn')
    task = tmp_path / 'padded.lean'
    task.write_text('import Mathlib\n\n/-! ' + 'frozen commentary ' * 100 + '-/\n\n'
                    'theorem padded_demo (n : ℕ) : n + 0 = n := by\n  sorry\n')
    c = Contract.load(task)
    proof = c.render(c.root.signature + ' := by simp')
    attempts = 0
    def factory(role):
        nonlocal attempts
        if role == 'coordinator':
            return Recording([])
        attempts += 1
        if attempts < 3:
            return ScriptedSession([Reply('', [('p', 'report_progress', {'text': 'x' * 6000})], 0,
                                          'tool_use'),
                                    Reply('{"outcome":"stuck_hard","detail":"no"}', [], 0, 'end_turn')])
        return ScriptedSession([Reply('', [('w', 'write_proof', {'text': proof})], 0, 'tool_use'),
                                Reply('{"outcome":"proved"}', [], 0, 'end_turn')])
    cfg = Config(coordinator_source_chars=1000, coordinator_context_chars=10000)
    run = tmp_path / 'run'
    result = await Engine(cfg, factory).run(task, run)
    assert result.status == 'proved', result.detail
    assert 'outline' in seen[0] and 'source' not in seen[0]
    assert seen[0]['outline'][0]['name'] == 'padded_demo'
    assert any('context_reset' in s for s in seen)
    kinds = [json.loads(line)['kind'] for line in (run / 'events.jsonl').read_text().splitlines()]
    assert 'coordinator_rotated' in kinds
