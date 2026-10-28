"""Command line entrypoints. Offline demo never requests credentials."""
import argparse
import asyncio
import signal
import json
from pathlib import Path
import tempfile
from .agent import Reply, ScriptedSession
from .config import Config
from .contracts import Contract
from .engine import Engine
from .lean import Lean


async def demo(config, directory):
    task = config.project / 'examples/add_zero.lean'
    contract = Contract.load(task)
    source = contract.render(contract.root.signature + ' := by\n  simp')
    replies = [Reply('', [('1', 'write_proof', {'text': source})], 0, 'tool_use'),
               Reply('{"outcome":"proved"}', [], 0, 'end_turn')]
    def factory(role):
        if role == 'coordinator':
            return ScriptedSession([])
        return ScriptedSession(replies)
    return await Engine(config, factory).run(task, directory)


def graceful_stop():
    # SIGTERM cancels the main task so Engine.run records 'cancelled' and closes sessions,
    # instead of the process dying without result.json.
    loop, task = asyncio.get_running_loop(), asyncio.current_task()
    loop.add_signal_handler(signal.SIGTERM, task.cancel)


async def execute(args):
    graceful_stop()
    config = Config.load(args.config) if args.config else Config()
    if args.command == 'demo':
        result = await demo(config, args.run_dir)
        print(result.model_dump_json(indent=2))
        return 0 if result.status == 'proved' else 1
    if args.command == 'prove':
        result = await Engine(config).run(args.task, args.run_dir)
        print(result.model_dump_json(indent=2))
        return 0 if result.status in ('proved', 'falsified') else 1
    if args.command == 'report':
        print((args.run_dir / 'result.json').read_text())
        return 0
    if args.command == 'doctor':
        contract = Contract.load(config.project / 'examples/add_zero.lean')
        source = contract.render(contract.root.signature + ' := by simp')
        with tempfile.TemporaryDirectory(dir=config.project / '.setup-tmp') as tmp:
            check = await Lean(config.project).check(contract, source, Path(tmp))
        print(check.model_dump_json(indent=2))
        return 0 if check.ok and not check.open else 1
    benchmark = config.project / 'vendor/fatex-source'
    data = json.loads((benchmark / 'FATE-X.json').read_text())
    if args.operation == 'list':
        for row in data:
            print(row['id'], ', '.join(row['tag']))
        return 0
    ids = args.ids or list(range(1, 101))
    if args.operation == 'run':
        failures = 0
        for problem in ids:
            for repetition in range(args.repeats):
                directory = args.run_dir / f'{problem}-{repetition}'
                result = await Engine(config).run(benchmark / f'FATEX/{problem}.lean', directory)
                print(result.model_dump_json())
                failures += result.status not in ('proved', 'falsified')
        return int(bool(failures))
    semaphore = asyncio.Semaphore(3)
    async def validate(problem):
        async with semaphore:
            try:
                contract = Contract.load(benchmark / f'FATEX/{problem}.lean')
                source = contract.render(contract.root.signature + ' := by\n  sorry')
                with tempfile.TemporaryDirectory(dir=config.project / '.setup-tmp') as tmp:
                    result = await Lean(config.project).check(contract, source, Path(tmp))
                return {'id': problem, 'ok': result.ok, 'detail': '' if result.ok else result.output}
            except (ValueError, TimeoutError) as exc:
                return {'id': problem, 'ok': False, 'detail': str(exc)}
    results = await asyncio.gather(*(validate(i) for i in ids))
    args.run_dir.mkdir(parents=True, exist_ok=True)
    (args.run_dir / 'validation.json').write_text(json.dumps(results, indent=2))
    print(json.dumps({'compatible': sum(r['ok'] for r in results), 'total': len(results)}))
    return int(not all(r['ok'] for r in results))


def main():
    parser = argparse.ArgumentParser(description='MAESTRO Lean proof coordination')
    parser.add_argument('--config', type=Path)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ['doctor', 'demo', 'prove', 'report', 'fatex']:
        p = sub.add_parser(name)
        p.add_argument('--run-dir', type=Path, default=Path('runs') / name)
        if name == 'prove':
            p.add_argument('task', type=Path)
        if name == 'fatex':
            p.add_argument('operation', choices=['list', 'validate', 'run'])
            p.add_argument('--ids', nargs='+', type=int, choices=range(1, 101))
            p.add_argument('--repeats', type=int, default=1)
    try:
        raise SystemExit(asyncio.run(execute(parser.parse_args())))
    except (ValueError, OSError) as exc:
        parser.exit(2, f'maestro: {exc}\n')
