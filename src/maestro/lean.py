"""Lean subprocess bridge and transitive-axiom completion checks."""
import asyncio
import json
import os
from pathlib import Path
import signal
import uuid
from .contracts import Contract
from .models import Check, Inspection


class Lean:
    def __init__(self, project: Path, timeout: float = 120, parallel: int = 2):
        self.project = project.resolve()
        self.timeout = timeout
        self.slots = asyncio.Semaphore(parallel)
        self.inspector = (project / 'lean/Maestro/Inspect.lean').read_text()

    async def check(self, contract: Contract, source: str, directory: Path) -> Check:
        try:
            goals = contract.validate(source)
        except ValueError as e:
            return Check(ok=False, output=str(e))
        directory.mkdir(parents=True, exist_ok=True)
        path = directory / f'check_{uuid.uuid4().hex}.lean'
        # Inspector must precede namespaces. Its import is harness-owned.
        checks = '\n'.join(f'#maestro_inspect {g.name}' for g in goals)
        body = source.replace('\n-- MAESTRO GENERATED END\n', '\n' + checks + '\n-- MAESTRO GENERATED END\n')
        # Keep every frozen import ahead of the harness command definition.
        import re
        imports = re.findall(r'(?m)^import[^\n]*\n?', body)
        body = re.sub(r'(?m)^import[^\n]*\n?', '', body)
        path.write_text(''.join(imports) + self.inspector + '\n' + body)
        env = {**os.environ, 'ELAN_HOME': '/data/hrm/elan',
               'TMPDIR': str(self.project / '.setup-tmp'),
               'XDG_CACHE_HOME': str(self.project / '.cache')}
        async with self.slots:
            proc = await asyncio.create_subprocess_exec('lake', 'env', 'lean', str(path), cwd=self.project, env=env,
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT, start_new_session=True)
            try:
                raw, _ = await asyncio.wait_for(proc.communicate(), self.timeout)
            except (TimeoutError, asyncio.CancelledError):
                if proc.returncode is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                await proc.communicate()
                raise
        output = raw.decode(errors='replace')
        inspections = []
        for line in output.splitlines():
            if 'MAESTRO_JSON:' in line:
                inspections.append(Inspection.model_validate(json.loads(line.split('MAESTRO_JSON:', 1)[1])))
        allowed = {'propext', 'Classical.choice', 'Quot.sound', 'sorryAx'}
        ok = proc.returncode == 0 and len(inspections) == len(goals)
        ok = ok and all(i.is_theorem and set(i.axioms) <= allowed for i in inspections)
        closed = [g.name for g, i in zip(goals, inspections) if 'sorryAx' not in i.axioms]
        return Check(ok=ok, inspections=inspections, closed=closed,
                     open=[g.name for g in goals if g.name not in closed], output=output)
