"""Scoped worker tools: no arbitrary shell, network, or filesystem mutation."""
from pydantic import BaseModel, ConfigDict


class Args(BaseModel):
    model_config = ConfigDict(extra='forbid')
    text: str = ''


class Tools:
    def __init__(self, workspace, source, directory, progress=None, readonly=False, mcp=None):
        self.workspace, self.source, self.directory = workspace, source, directory
        self.progress, self.readonly, self.mcp = progress, readonly, mcp
        names = ['read_proof', 'check_proof', 'search_mathlib', 'report_progress']
        if mcp:
            names.append('loogle_search')
        if not readonly:
            names.append('write_proof')
        self.schemas = [{'name': n, 'description': {
            'read_proof': 'Read private Proof.lean and immutable task boundaries.',
            'write_proof': 'Replace the entire private Proof.lean. Frozen regions must remain identical.',
            'check_proof': 'Compile private proof and inspect transitive axioms. No text argument needed.',
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
            return (await self.workspace.lean.check(self.workspace.contract, self.source, self.directory)).model_dump()
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
        # Explicitly return a bounded search page, not a truncated file.
        hits = []
        root = self.workspace.lean.project / 'vendor/mathlib-source/Mathlib'
        for path in root.rglob('*.lean'):
            for line, value in enumerate(path.read_text().splitlines(), 1):
                if arg.text in value:
                    hits.append({'file': str(path.relative_to(root)), 'line': line, 'text': value})
                    if len(hits) == 20:
                        return {'hits': hits, 'more_possible': True}
        return {'hits': hits, 'more_possible': False}
