"""Provider-independent tool loop; native provider history stays append-only."""
import asyncio
import json
import os
from dataclasses import dataclass
from .config import ProviderConfig


class BudgetExceeded(Exception):
    pass


class TransportError(Exception):
    """Provider unreachable or failing after all retries."""


RETRY_STATUS = {408, 409, 429, 500, 502, 503, 504, 529}
TRANSPORT = ('RemoteProtocolError', 'ReadError', 'WriteError', 'ConnectError', 'ReadTimeout',
             'WriteTimeout', 'ConnectTimeout', 'PoolTimeout', 'APIConnectionError', 'APITimeoutError')


def retryable(exc):
    if isinstance(exc, (TimeoutError, ConnectionError)):
        return True
    if getattr(exc, 'status_code', None) in RETRY_STATUS:
        return True
    return type(exc).__name__ in TRANSPORT


def arguments(raw):
    # Malformed tool arguments become a tool error the model can see, not a crash.
    try:
        value = json.loads(raw or '{}')
        return value if isinstance(value, dict) else {'__invalid__': raw}
    except json.JSONDecodeError:
        return {'__invalid__': raw}


class Budget:
    def __init__(self, total):
        self.total, self.used, self.reserved = total, 0, 0
        self.lock = asyncio.Lock()

    async def reserve(self, amount):
        async with self.lock:
            if self.used + self.reserved + amount > self.total:
                raise BudgetExceeded('output token budget exhausted')
            self.reserved += amount

    async def settle(self, reserved, used):
        async with self.lock:
            self.reserved -= reserved
            self.used += used


@dataclass
class Reply:
    text: str
    calls: list
    tokens: int
    stop: str


class Session:
    def __init__(self, config: ProviderConfig, system: str, budget: Budget):
        key = os.environ.get(config.key_env)
        if not key:
            raise ValueError(f'missing key environment variable: {config.key_env}')
        self.config, self.system, self.budget = config, system, budget
        self.history = []
        # Retries are ours, so that every attempt is bounded by one wall-clock deadline.
        # SDK timeouts are per read; keep-alive pings can hold a stalled stream open forever.
        if config.protocol == 'anthropic':
            from anthropic import AsyncAnthropic
            self.client = AsyncAnthropic(api_key=key, base_url=config.base_url,
                                         timeout=config.timeout, max_retries=0)
        else:
            from openai import AsyncOpenAI
            self.client = AsyncOpenAI(api_key=key, base_url=config.base_url,
                                     timeout=config.timeout, max_retries=0)
            self.history.append({'role': 'system', 'content': system})

    async def request(self, user, tools):
        if user is not None:
            self.history.append({'role': 'user', 'content': user})
        cfg = self.config
        last = None
        for attempt in range(cfg.retries + 1):
            if attempt:
                await asyncio.sleep(min(2 ** attempt, 30))
            await self.budget.reserve(cfg.max_tokens)
            # A failed attempt may still have been billed; charge the reservation.
            used = cfg.max_tokens
            try:
                used, reply = await asyncio.wait_for(self._attempt(tools), cfg.timeout)
                return reply
            except Exception as exc:
                if not retryable(exc):
                    raise
                last = exc
            finally:
                await self.budget.settle(cfg.max_tokens, used)
        raise TransportError(f'provider failed after {cfg.retries + 1} attempts: '
                             f'{type(last).__name__}: {last}') from last

    async def _attempt(self, tools):
        """Single API call; returns (tokens_used, Reply). History changes only on success."""
        cfg = self.config
        if cfg.protocol == 'anthropic':
            async with self.client.messages.stream(model=cfg.model, max_tokens=cfg.max_tokens,
                system=self.system, messages=self.history, tools=tools,
                thinking={'type': 'adaptive'}, output_config={'effort': cfg.effort}) as stream:
                msg = await stream.get_final_message()
            used = msg.usage.output_tokens
            self.history.append({'role': 'assistant', 'content': msg.model_dump()['content']})
            return used, Reply(
                ''.join(b.text for b in msg.content if b.type == 'text'),
                [(b.id, b.name, b.input) for b in msg.content if b.type == 'tool_use'],
                used, msg.stop_reason)
        mapped = [{'type': 'function', 'function': {'name': t['name'],
            'description': t['description'], 'parameters': t['input_schema']}} for t in tools]
        msg = await self.client.chat.completions.create(model=cfg.model,
            messages=self.history, tools=mapped or None, max_completion_tokens=cfg.max_tokens)
        used = msg.usage.completion_tokens if msg.usage else cfg.max_tokens
        choice = msg.choices[0]
        self.history.append(choice.message.model_dump(exclude_none=True))
        calls = [(c.id, c.function.name, arguments(c.function.arguments))
                 for c in choice.message.tool_calls or []]
        return used, Reply(choice.message.content or '', calls, used, choice.finish_reason)

    def results(self, results):
        if self.config.protocol == 'anthropic':
            self.history.append({'role': 'user', 'content': [
                {'type': 'tool_result', 'tool_use_id': i, 'content': text, 'is_error': error}
                for i, text, error in results]})
        else:
            self.history.extend({'role': 'tool', 'tool_call_id': i, 'content': text} for i, text, _ in results)

    async def close(self):
        await self.client.close()


class ScriptedSession:
    """Offline test adapter exercising the same tools, scheduler, and Lean verifier."""
    def __init__(self, replies):
        self.replies = iter(replies)
        self.history = []

    async def request(self, user, tools):
        self.history.append({'user': user})
        return next(self.replies)

    def results(self, results):
        self.history.append({'results': results})

    async def close(self):
        pass


def object_response(text):
    text = text.strip()
    if not text:
        raise ValueError('empty response from provider')
    if text.startswith('```'):
        text = text.split('\n', 1)[1].rsplit('```', 1)[0]
    try:
        data = json.loads(text)
    except json.JSONDecodeError:
        # Model sometimes wraps JSON in prose; extract the first balanced {…} block.
        import re
        m = re.search(r'\{.*\}', text, re.DOTALL)
        if m:
            try:
                data = json.loads(m.group())
            except json.JSONDecodeError:
                raise ValueError(f'no valid JSON object found in provider response: {text[:300]}')
        else:
            raise ValueError(f'no JSON object found in provider response: {text[:300]}')
    if not isinstance(data, dict):
        raise TypeError('expected JSON object')
    return data


REPAIR = ('Your last reply was not a single JSON object ({error}). Reply again with only the '
          'JSON object required by your instructions, with no prose or code fences.')


async def interact(session, prompt, toolbox, max_turns):
    repaired = False
    for _ in range(max_turns):
        reply = await session.request(prompt, toolbox.schemas if toolbox else [])
        prompt = None
        if reply.stop in ('max_tokens', 'length', 'refusal', 'content_filter'):
            raise ValueError(f'provider stopped without valid output: {reply.stop}')
        if reply.stop == 'pause_turn' and not reply.calls:
            continue  # server paused a long turn; resending the history resumes it
        if not reply.calls:
            try:
                return object_response(reply.text)
            except (ValueError, TypeError) as exc:
                if repaired:
                    raise ValueError(f'{exc} (stop_reason={reply.stop})') from exc
                repaired = True
                prompt = REPAIR.format(error=str(exc)[:200])
                continue
        if toolbox is None:
            # Coordinator has no tools; a tool call from the model is a protocol error.
            raise ValueError(f'unexpected tool call from provider when no tools provided: {reply.calls[0][1]}')
        results = []
        for call_id, name, args in reply.calls:
            try:
                result = await toolbox.call(name, args)
                results.append((call_id, json.dumps(result, default=str), False))
            except (ValueError, OSError, TimeoutError) as exc:
                results.append((call_id, str(exc)[:6000], True))
        session.results(results)
    raise BudgetExceeded('agent tool-turn limit reached')
