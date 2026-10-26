from pathlib import Path
import pytest
from maestro.contracts import Contract
from maestro.agent import Budget, BudgetExceeded
from maestro.config import Config
from maestro.lean import Lean
from maestro.cli import demo

PROJECT = Path('/data/hrm/lean_workspace')


def test_frozen_signature():
    c = Contract.load(PROJECT / 'examples/add_zero.lean')
    s = c.render(c.root.signature + ' := by simp')
    assert len(c.validate(s)) == 1
    with pytest.raises(ValueError):
        c.validate(s.replace('n + 0 = n', 'True'))
    with pytest.raises(ValueError):
        c.validate(s.replace('by simp', 'by\n run_tac pure ()'))


async def test_budget():
    budget = Budget(100)
    await budget.reserve(80)
    with pytest.raises(BudgetExceeded):
        await budget.reserve(21)
    await budget.settle(80, 20)
    assert budget.used == 20 and budget.reserved == 0


@pytest.mark.lean
async def test_inspector(tmp_path):
    c = Contract.load(PROJECT / 'examples/add_zero.lean')
    lean = Lean(PROJECT)
    good = await lean.check(c, c.render(c.root.signature + ' := by simp'), tmp_path)
    assert good.ok and good.closed == ['add_zero_demo']
    pending = await lean.check(c, c.render(c.root.signature + ' := by sorry'), tmp_path)
    assert pending.ok and pending.open == ['add_zero_demo']
    wrong = await lean.check(c, c.render(c.root.signature + ' := by rfl'), tmp_path)
    assert wrong.ok  # Nat.add_zero is definitional too.


@pytest.mark.lean
async def test_offline_runtime(tmp_path):
    result = await demo(Config(), tmp_path / 'demo')
    assert result.status == 'proved', result.detail
