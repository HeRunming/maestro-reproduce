"""Offline robustness: model-output parsing, provider retries, cohorts, region boundary."""
import asyncio
from pathlib import Path
from types import SimpleNamespace
import pytest
from maestro import agent
from maestro.agent import Budget, Reply, ScriptedSession, Session, TransportError, interact
from maestro.config import Config, ProviderConfig
from maestro.contracts import Contract
from maestro.engine import Engine
from maestro.models import Decision, Diagnosis, Event

PROJECT = Path('/data/hrm/lean_workspace')
C = Contract.load(PROJECT / 'examples/add_zero.lean')


@pytest.mark.parametrize('raw,expected', [(0, 1), (None, 1), ('3', 3), (99, 15), ('x', 1)])
def test_explorer_count_is_clamped(raw, expected):
    d = Decision.model_validate({'decision': 'act', 'extra': 1, 'actions': [
        {'op': ' reprove ', 'explorer_count': raw, 'target': None, 'unknown': True}]})
    assert d.decision == 'ACT' and d.actions[0].op == 'REPROVE'
    assert d.actions[0].explorer_count == expected and d.actions[0].target == 'root'


def test_diagnosis_tolerates_model_variation():
    d = Diagnosis.model_validate({'outcome': 'stuck_hard', 'approaches_tried': 'simp', 'note': 'x'})
    assert d.detail == '' and d.approaches_tried == ['simp']


async def test_interact_repairs_one_malformed_reply():
    s = ScriptedSession([Reply('Here is my answer: done', [], 0, 'end_turn'),
                         Reply('```json\n{"decision":"CONTINUE"}\n```', [], 0, 'end_turn')])
    assert await interact(s, 'state', None, 3) == {'decision': 'CONTINUE'}
    assert 'not a single JSON object' in s.history[1]['user']
    s = ScriptedSession([Reply('no', [], 0, 'end_turn'), Reply('still no', [], 0, 'end_turn')])
    with pytest.raises(ValueError):
        await interact(s, 'state', None, 3)


def test_malformed_tool_arguments_do_not_crash():
    assert agent.arguments('{"text": "a"}') == {'text': 'a'}
    assert agent.arguments('{bad') == {'__invalid__': '{bad'}
    assert agent.arguments('[1]') == {'__invalid__': '[1]'}


class RemoteProtocolError(Exception):
    pass


class Status(Exception):
    def __init__(self, code):
        super().__init__(f'status {code}')
        self.status_code = code


async def test_provider_retry_timeout_and_budget(monkeypatch):
    monkeypatch.setenv('MAESTRO_TEST_KEY', 'x')
    real_sleep = asyncio.sleep
    monkeypatch.setattr(agent.asyncio, 'sleep', lambda s: real_sleep(0))  # skip backoff
    cfg = ProviderConfig(key_env='MAESTRO_TEST_KEY', max_tokens=200, timeout=0.2, retries=3)
    budget = Budget(10_000)
    session = Session(cfg, 'system', budget)
    calls = []
    async def attempt(tools):
        calls.append(1)
        if len(calls) == 1:
            raise RemoteProtocolError('incomplete chunked read')
        if len(calls) == 2:
            await asyncio.Event().wait()  # stalled stream: only the hard deadline ends it
        if len(calls) == 3:
            raise Status(529)
        return 7, Reply('{}', [], 7, 'end_turn')
    monkeypatch.setattr(session, '_attempt', attempt)
    reply = await session.request('hi', [])
    assert reply.tokens == 7 and len(calls) == 4
    assert budget.reserved == 0 and budget.used == 3 * 200 + 7
    # Non-retryable errors surface immediately; exhausted retries raise TransportError.
    async def bad_request(tools):
        raise Status(400)
    monkeypatch.setattr(session, '_attempt', bad_request)
    with pytest.raises(Status):
        await session.request('hi', [])
    async def down(tools):
        raise ConnectionResetError('reset')
    monkeypatch.setattr(session, '_attempt', down)
    with pytest.raises(TransportError):
        await session.request('hi', [])
    assert budget.reserved == 0
    await session.close()


async def test_explorer_cohort_completes_with_errors():
    engine = Engine(Config(), lambda role: ScriptedSession([]))
    engine.ws = SimpleNamespace(journal=SimpleNamespace(record=lambda *a, **k: None))
    engine.cohorts['c'] = {'size': 2, 'results': []}
    first = Event(kind='explorer', worker_id='a', goal='g', revision=1,
                  payload={'output': {'outcome': 'candidate'}, 'cohort_id': 'c'})
    second = Event(kind='worker_error', worker_id='b', goal='g', revision=1,
                   payload={'error': 'TransportError', 'cohort_id': 'c'})
    await engine.apply(first)
    assert 'cohort_complete' not in first.payload
    await engine.apply(second)
    assert [r['kind'] for r in second.payload['cohort_complete']] == ['explorer', 'worker_error']


@pytest.mark.parametrize('code', ['variable (x : ℕ)', 'universe u', 'private theorem t : True := trivial',
                                  'noncomputable theorem t : True := trivial'])
def test_region_rejects_context_changing_commands(code):
    with pytest.raises(ValueError):
        C.validate(C.render(code + '\n' + C.root.signature + ' := by simp'))


def test_region_accepts_lemma_keyword():
    goals = C.validate(C.render('lemma helper (n : ℕ) : n + 0 = n := by simp\n\n'
                                + C.root.signature + ' := helper n'))
    assert [g.name for g in goals] == ['helper', 'add_zero_demo']
