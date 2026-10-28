"""Atomic, single-writer proof workspace with immutable revisions."""
import asyncio
import hashlib
import json
import os
from pathlib import Path
from .contracts import Contract
from .lean import Lean
from .models import Goal

NEGATION = 'maestro_root_negation'


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
        # Elaborated root type, pinned by the first commit. Matching signature text is not
        # enough: an `open ... in` before the root can change what its identifiers mean.
        self.root_hash = None
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

    async def _commit_locked(self, source: str):
        """Must be called with self.lock already held."""
        result = await self.lean.check(self.contract, source, self.directory / 'checks')
        if not result.ok:
            raise ValueError(result.output)
        if not result.root_type_hash:
            raise ValueError('root theorem was not inspected')
        if self.root_hash is not None and result.root_type_hash != self.root_hash:
            raise ValueError('root statement elaborates to a different type than the original')
        self.root_hash = self.root_hash or result.root_type_hash
        self.source, self.check_result = source, result
        self.revision += 1
        self._save()
        return result

    async def commit(self, source: str, base: int):
        async with self.lock:
            if base != self.revision:
                raise ValueError('stale workspace revision')
            return await self._commit_locked(source)

    async def initialize(self):
        return await self.commit(self.source, self.revision)

    @property
    def goals(self):
        return self.contract.validate(self.source)

    @property
    def open_goals(self):
        if self.check_result and self.check_result.ok:
            return self.check_result.open
        return [g.name for g in self.goals]

    @property
    def frontier(self):
        """Open goals whose own proof is unfinished; falls back to all open goals."""
        open_ = self.open_goals
        direct = [n for n in (self.check_result.frontier if self.check_result else []) if n in open_]
        return direct or open_

    @property
    def proved(self):
        r = self.check_result
        return bool(r and r.ok and not r.open and self.contract.root.name in r.closed)

    def replace_proof(self, name: str, proof: str, source: str | None = None):
        goals = self.contract.validate(source or self.source)
        if not any(g.name == name for g in goals):
            raise ValueError('unknown target')
        return self.contract.render('\n\n'.join(g.signature + ' := ' + (proof if g.name == name else g.proof) for g in goals))

    def rebase(self, name: str, candidate: str):
        """Goal-wise merge of a worker's private source onto the current source.

        Takes only the target's new proof and genuinely new declarations (theorems and
        defs) from the candidate. Every other existing declaration keeps its current text,
        so a sibling proved after the worker's snapshot is never reverted and existing defs
        are never redefined. New declarations are inserted, in candidate order, immediately
        before the target, which is the only consumer that can rely on them.
        """
        incoming = self.contract.validate(candidate)
        current = self.goals
        by_name = {g.name: g for g in current}
        mine = {g.name: g for g in incoming}
        if name not in by_name or by_name[name].kind != 'theorem':
            raise ValueError(f'unknown target {name}')
        if name not in mine:
            raise ValueError(f'candidate removed target {name}')
        if mine[name].signature != by_name[name].signature:
            raise ValueError(f'candidate changed the signature of {name}')
        added = [g for g in incoming if g.name not in by_name]
        ignored = [g.name for g in incoming if g.name in by_name and g.name != name
                   and (g.signature != by_name[g.name].signature or g.proof != by_name[g.name].proof)]
        merged = []
        for g in current:
            if g.name == name:
                merged.extend(added)
                merged.append(mine[name])
            else:
                merged.append(g)
        changed = bool(added) or mine[name].proof != by_name[name].proof
        source = self.contract.render('\n\n'.join(g.signature + ' := ' + g.proof for g in merged))
        return source, [g.name for g in added], ignored, changed

    async def merge(self, name: str, candidate: str, base: int, require_change: bool = False):
        """Rebase a worker result onto the current revision and commit it atomically."""
        async with self.lock:
            if name not in self.open_goals:
                raise ValueError(f'target {name} is already closed')
            source, added, ignored, changed = self.rebase(name, candidate)
            if require_change and not changed:
                raise ValueError(f'candidate does not change {name}')
            if base != self.revision:
                self.journal.record('stale_rebase', goal=name, base=base, current=self.revision)
            if ignored:
                self.journal.record('merge_ignored_edits', goal=name, goals=ignored)
            result = await self._commit_locked(source)
            self.journal.record('merged', goal=name, added=added, closed=name in result.closed,
                                revision=self.revision)
            return result, added

    async def merge_proof(self, name: str, candidate: str, base: int):
        return (await self.merge(name, candidate, base))[0]

    def negation_contract(self):
        root = self.contract.root
        neg = Goal(name=NEGATION, signature=f'theorem {NEGATION} : ¬ (type_of% @{root.name})')
        return Contract(self.contract.prefix, self.contract.suffix, root), neg

    async def check_negation(self, proof: str):
        """Check a proof of the negation of the exact elaborated root proposition.

        The root is declared with `sorry` only so that `type_of%` can read its elaborated
        type; a negation proof that uses the root itself inherits `sorryAx` and stays open.
        """
        contract, neg = self.negation_contract()
        region = contract.root.signature + ' := by\n  sorry\n\n' + neg.signature + ' := ' + proof.strip()
        source = contract.render(region)
        result = await self.lean.check(contract, source, self.directory / 'falsification')
        root_ok = result.root_type_hash == self.root_hash
        certified = result.ok and root_ok and NEGATION in result.closed
        return certified, source, result
