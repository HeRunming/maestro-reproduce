"""Loogle search via HTTP API (https://loogle.lean-lang.org)."""
import asyncio
import urllib.request
import urllib.parse
import json


class LoogleClient:
    """Stateless HTTP client for Loogle type-search queries."""

    def __init__(self, base_url: str = 'https://loogle.lean-lang.org', timeout: float = 15):
        self.base_url = base_url.rstrip('/')
        self.timeout = timeout

    async def search(self, query: str) -> dict:
        url = self.base_url + '/json?' + urllib.parse.urlencode({'q': query})
        loop = asyncio.get_event_loop()
        try:
            raw = await loop.run_in_executor(None, lambda: _fetch(url, self.timeout))
            return json.loads(raw)
        except Exception as exc:
            return {'error': str(exc), 'hits': []}

    async def call_tool(self, name: str, arguments: dict) -> str:
        if name != 'loogle':
            raise ValueError(f'unknown tool {name}')
        result = await self.search(arguments.get('query', ''))
        if 'error' in result:
            return f"Loogle error: {result['error']}"
        hits = result.get('hits', []) or []
        lines = []
        for h in hits[:10]:
            name_str = h.get('name', '')
            typ = h.get('type', '') or h.get('statement', '')
            lines.append(f'{name_str} : {typ}' if typ else name_str)
        return '\n'.join(lines) if lines else 'No results found.'

    async def close(self):
        pass


def _fetch(url: str, timeout: float) -> bytes:
    req = urllib.request.Request(url, headers={'User-Agent': 'maestro-lean/0.1'})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


async def test_loogle(query: str = 'Nat.add_comm'):
    client = LoogleClient()
    return await client.call_tool('loogle', {'query': query})
