"""Scoped worker tools: no arbitrary shell, network, or filesystem mutation."""
import asyncio
from pydantic import BaseModel, ConfigDict


class Args(BaseModel):
    model_config = ConfigDict(extra='forbid')
    text: str = ''


def clip(text, limit=6000):
    # Lean errors usually come first and summaries last; keep both ends.
    return text if len(text) <= limit else text[:limit // 2] + '\n…[truncated]…\n' + text[-limit // 2:]


class Tools:
    def __init__(self, workspace, source, directory, progress=None, readonly=False, mcp=None, negation=False):
        self.workspace, self.source, self.directory = workspace, source, directory
        self.progress, self.readonly, self.mcp = progress, readonly, mcp
        names = ['read_proof', 'check_proof', 'search_mathlib', 'report_progress']
        if mcp:
            names.append('loogle_search')
        if not readonly:
            names.append('write_proof')
        if negation:
            names.append('check_negation')
        self.schemas = [{'name': n, 'description': {
            'read_proof': 'Read private Proof.lean and immutable task boundaries.',
            'write_proof': 'Replace the entire private Proof.lean. Frozen regions must remain identical.',
            'check_proof': 'Compile private proof and inspect transitive axioms. No text argument needed.',
            'check_negation': 'Compile a proof term or tactic block (e.g. "by ...") of the negation of the '
                              'complete root proposition. Returns whether it is a checked certificate.',
            'search_mathlib': 'Search local Mathlib source for a literal string (minimum 3 characters).',
            'loogle_search': 'Search Mathlib by type signature or name pattern using Loogle.',
            'report_progress': 'Send concrete progress/blocker information while continuing work.'}[n],
            'input_schema': Args.model_json_schema()} for n in names]

    async def call(self, name, args):
        arg = Args.model_validate(args)
        if name not in {s['name'] for s in self.schemas}:
            raise ValueError('unknown tool')
        if name == 'read_proof':
            return {'source': self.source}
        if name == 'write_proof':
            self.workspace.contract.validate(arg.text)
            self.source = arg.text
            self.directory.mkdir(parents=True, exist_ok=True)
            (self.directory / 'Proof.lean').write_text(self.source)
            return {'saved': True}
        if name == 'check_proof':
            result = await self.workspace.lean.check(self.workspace.contract, self.source, self.directory)
            return {**result.model_dump(exclude={'output'}), 'output': clip(result.output)}
        if name == 'check_negation':
            certified, _, result = await self.workspace.check_negation(arg.text)
            return {'certified': certified, 'ok': result.ok, 'output': clip(result.output)}
        if name == 'loogle_search':
            if not self.mcp:
                return {'error': 'Loogle MCP server not configured'}
            try:
                result = await self.mcp.call_tool('loogle', {'query': arg.text})
                return {'results': result[:2000]}
            except Exception as exc:
                return {'error': str(exc)}
        if name == 'report_progress':
            if self.progress:
                await self.progress(arg.text)
            return {'reported': True}
        if len(arg.text) < 3:
            raise ValueError('search needs at least three characters')
        # Scanning Mathlib takes seconds; keep it off the event loop.
        return await asyncio.to_thread(self._search, arg.text)

    def _search(self, text):
        # Explicitly return a bounded search page, not a truncated file.
        hits = []
        root = self.workspace.lean.project / 'vendor/mathlib-source/Mathlib'
        for path in root.rglob('*.lean'):
            for line, value in enumerate(path.read_text().splitlines(), 1):
                if text in value:
                    hits.append({'file': str(path.relative_to(root)), 'line': line, 'text': value})
                    if len(hits) == 20:
                        return {'hits': hits, 'more_possible': True}
        return {'hits': hits, 'more_possible': False}
