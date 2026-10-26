"""Fetch the exact dependency archives recorded by FATE-X (no downloaded scripts run)."""
import concurrent.futures
import json
from pathlib import Path
import subprocess

ROOT = Path('/data/hrm/lean_workspace')
manifest = json.loads((ROOT / 'vendor/fatex-source/lake-manifest.json').read_text())
def fetch(p):
    if p['name'] == 'mathlib':
        return
    dest = ROOT / 'vendor' / ('dep-' + p['name'])
    dest.mkdir(exist_ok=True)
    archive = dest / 'source.tar.gz'
    repo = p['url'].removeprefix('https://github.com/').removesuffix('.git')
    subprocess.run(['curl', '-fsSL', '--retry', '4', '--connect-timeout', '15', '--max-time', '240', f'https://codeload.github.com/{repo}/tar.gz/{p["rev"]}', '-o', str(archive)], check=True)
    source = dest / 'source'
    source.mkdir(exist_ok=True)
    subprocess.run(['tar', '-xzf', str(archive), '-C', str(source), '--strip-components=1'], check=True)
    print(p['name'], p['rev'], flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    list(pool.map(fetch, manifest['packages']))
