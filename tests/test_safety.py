from pathlib import Path
import pytest
from maestro.agent import Reply, ScriptedSession, interact
from maestro.config import Config
from maestro.contracts import Contract
from maestro.engine import Engine
from maestro.lean import Lean
from maestro.models import Decision

PROJECT = Path('/data/hrm/lean_workspace')


@pytest.mark.parametrize('code', ['axiom bad : False', 'abbrev x : Nat := 0',
    'instance : Inhabited Nat := ⟨0⟩', '@[simp] theorem t : True := by trivial'])
def test_generated_region_blocks_trust_or_global_effects(code):
    c = Contract.load(PROJECT / 'examples/add_zero.lean')
    with pytest.raises(ValueError):
        c.validate(c.render(code + '\n' + c.root.signature + ' := by simp'))


@pytest.mark.lean
async def test_sorry_and_wrong_type_are_not_proof(tmp_path):
    c = Contract.load(PROJECT / 'examples/add_zero.lean')
    lean = Lean(PROJECT)
    result = await lean.check(c, c.render(c.root.signature + ' := by exact (sorry : True)'), tmp_path)
    assert not result.ok or result.open
    result = await lean.check(c, c.render(c.root.signature + ' := by exact trivial'), tmp_path)
    assert not result.ok


async def test_tool_errors_return_to_model():
    class BadTools:
        schemas = []
        async def call(self, name, args):
            raise ValueError('frozen context was modified')
    session = ScriptedSession([Reply('', [('x', 'write_proof', {'text': 'bad'})], 0, 'tool_use'),
                               Reply('{"decision":"CONTINUE"}', [], 0, 'end_turn')])
    assert Decision.model_validate(await interact(session, 'state', BadTools(), 2)).decision == 'CONTINUE'
    assert session.history[1]['results'][0][2] is True


@pytest.mark.lean
async def test_full_negation_certificate(tmp_path):
    task = tmp_path / 'false.lean'
    task.write_text('import Mathlib\n\ntheorem false_claim : (2 : ℕ) + 2 = 5 := by\n  sorry\n')
    def factory(role):
        if role == 'prover':
            return ScriptedSession([Reply('{"outcome":"suspect_false","detail":"arithmetic","failure_scope":"global","witness":"norm_num"}', [], 0, 'end_turn')])
        if role == 'coordinator':
            return ScriptedSession([Reply('{"actions":[{"op":"FALSIFY"}]}', [], 0, 'end_turn')])
        return ScriptedSession([Reply('{"negation_proof":"by norm_num","detail":"2+2=4"}', [], 0, 'end_turn')])
    result = await Engine(Config(), factory).run(task, tmp_path / 'run')
    assert result.status == 'falsified', result.detail


HIDDEN = '#check Nat\nset_option debug.skipKernelTC true in\n'
SMUGGLE = {
    # A char literal containing `"` desynchronized the old string matcher.
    'char-literal quote': "def q : Char := '\"'\ndef s : String := \"/-\"\n" + HIDDEN + 'def t : String := "-/"\n',
    # A `"` inside a block comment used to swallow the real `-/`.
    'quote in comment': '/- " -/\n' + HIDDEN + '/- " -/\n',
    'apostrophe in comment': "/- don't -/\n" + HIDDEN + "/- isn't -/\n",
    'quoted name': 'theorem «x/-» : True := trivial\n' + HIDDEN + 'theorem «-/» : True := trivial\n',
    'raw string': 'def s : String := r#"/-"#\n' + HIDDEN + 'def t : String := r#"-/"#\n',
    'interpolated string': 'def s : String := s!"{"/-"}"\n' + HIDDEN + 'def t : String := "-/"\n',
    'escaped quote': 'def s : String := "\\"/-"\n' + HIDDEN + 'def t : String := "-/"\n',
}


@pytest.mark.parametrize('name', list(SMUGGLE))
def test_scanner_cannot_be_desynchronized(name):
    c = Contract.load(PROJECT / 'examples/add_zero.lean')
    with pytest.raises(ValueError):
        c.validate(c.render(SMUGGLE[name] + c.root.signature + ' := by simp'))


@pytest.mark.parametrize('code', [
    "theorem t (h' : 1 = 1) : h' = h' := rfl",                # primes in identifiers
    "theorem t : ('a' : Char) ≠ 'b' := by decide",           # char literals
    "theorem t : \"a -- /- b\".length = 9 := by decide",     # comment markers inside a string
    "/- nested /- comment -/ with \" and ' inside -/\ntheorem t : True := trivial",
])
def test_scanner_accepts_ordinary_lean(code):  # «quoted» theorem names are rejected (safe)
    c = Contract.load(PROJECT / 'examples/add_zero.lean')
    c.validate(c.render(code + '\n\n' + c.root.signature + ' := by simp'))
