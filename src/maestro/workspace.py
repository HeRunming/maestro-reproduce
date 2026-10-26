"""Atomic, single-writer proof workspace with immutable revisions."""
import asyncio
import hashlib
import json
import os
from pathlib import Path
from .contracts import Contract
from .lean import Lean


class Journal:
    def __init__(self, directory: Path):
        self.path = directory / 'events.jsonl'

    def record(self, kind: str, **data):
        with self.path.open('a') as f:
            f.write(json.dumps({'kind': kind, **data}, ensure_ascii=False, default=str) + '\n')
            f.flush()


class Workspace:
    def __init__(self, contract: Contract, lean: Lean, directory: Path):
        if directory.exists() and any(directory.iterdir()):
            raise ValueError('run directory must be new or empty')
        directory.mkdir(parents=True, exist_ok=True)
        self.directory, self.contract, self.lean = directory, contract, lean
        self.revision = 0
        self.source = contract.render(contract.root.signature + ' := by\n  sorry')
        self.check_result = None
        self.lock = asyncio.Lock()
        self.journal = Journal(directory)
        self._save()

    def _save(self):
        # Immutable snapshot is the commit record. CURRENT is the atomic pointer.
        snapshot = self.directory / f'revision-{self.revision:05d}.lean'
        snapshot.write_text(self.source)
        pointer = self.directory / 'CURRENT.tmp'
        pointer.write_text(str(self.revision))
        os.replace(pointer, self.directory / 'CURRENT')
        self.journal.record('revision', revision=self.revision, sha256=hashlib.sha256(self.source.encode()).hexdigest())

    async def commit(self, source: str, base: int):
        async with self.lock:
            if base != self.revision:
                raise ValueError('stale workspace revision')
            result = await self.lean.check(self.contract, source, self.directory / 'checks')
            if not result.ok:
                raise ValueError(result.output)
            self.source, self.check_result = source, result
            self.revision += 1
            self._save()
            return result

    async def initialize(self):
        return await self.commit(self.source, self.revision)

    @property
    def goals(self):
        return self.contract.validate(self.source)

    @property
    def open_goals(self):
        return self.check_result.open if self.check_result else [g.name for g in self.goals]

    def replace_proof(self, name: str, proof: str, source: str | None = None):
        goals = self.contract.validate(source or self.source)
        if not any(g.name == name for g in goals):
            raise ValueError('unknown target')
        return self.contract.render('\n\n'.join(g.signature + ' := ' + (proof if g.name == name else g.proof) for g in goals))

    async def merge_proof(self, name: str, candidate: str, base: int):
        incoming = self.contract.validate(candidate)
        current = {g.name: g for g in self.goals}
        goal = next(g for g in incoming if g.name == name)
        if name not in current or current[name].signature != goal.signature:
            raise ValueError('obsolete target signature')
        if base != self.revision:
            self.journal.record('stale_revalidation', goal=name, base=base, current=self.revision)
        # Never merge unrelated worker source edits; recompile against current state.
        return await self.commit(self.replace_proof(name, goal.proof), self.revision)
