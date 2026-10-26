# MAESTRO for Lean / FATE-X

An engineering reproduction of the coordination architecture in
*MAESTRO: Agentic Formal Proof Development by Coordination* (arXiv:2610.25920):
a persistent coordinator that reads structured worker diagnoses and revises the
global proof plan, instead of repairing failures locally.

Status: integration-tested with Lean and scripted model replies (13 tests), and smoke-tested
with real Claude and GPT backends on a few FATE-X problems. No paper benchmark numbers are
claimed; see [docs/paper-mapping.md](docs/paper-mapping.md) for what is and is not implemented.

## Architecture

- **Coordinator** (`engine.py`): persistent session, event-driven (no fixed rounds); decides
  CONTINUE / REPROVE / DECOMPOSE / EXPLORE / RETRACT / FALSIFY from accumulated evidence.
- **Workers**: Prover (structured local/global/uncertain diagnosis), Planner
  (proposer → judge → translator, up to 6 revisions), Explorer (private snapshot, never
  auto-published), Falsifier (harness-built negation of the full root statement).
- **Workspace** (`workspace.py`): single writer, atomic commits, immutable revision snapshots;
  stale worker results are re-elaborated against the current source.
- **Verifier** (`lean.py`, `lean/Maestro/Inspect.lean`): Lean kernel check plus transitive
  axiom inspection.
- **Backends** (`agent.py`): Anthropic Messages API or OpenAI Chat Completions, each with its own
  base URL and key environment variable.
- **Search tools**: local Mathlib source search and Loogle (HTTP API).

## Requirements

- Lean 4.28.0 and Mathlib v4.28.0 (the versions pinned by FATE-X). Local setup notes,
  including offline dependency handling, are in [SETUP.md](SETUP.md).
- Python 3.12+.
- The FATE-X benchmark extracted at `vendor/fatex-source`
  (<https://github.com/frenzymath/FATE-X>, commit `a6fb49ee`). `vendor/` is not committed.

## Install and test

```bash
source env.sh                  # Lean toolchain/cache locations (edit paths for your machine)
python3 -m venv .venv
.venv/bin/pip install -e '.[dev]'
.venv/bin/pytest tests -q
.venv/bin/maestro doctor       # Lean + axiom inspection smoke test
.venv/bin/maestro demo         # offline end-to-end run with scripted replies
.venv/bin/maestro fatex validate
```

## Real API runs (billable)

Configs store only the **name** of the key environment variable; never put a key in a file.

```toml
[provider]
protocol = "anthropic"          # or "openai"
model = "claude-opus-5-5"
base_url = "https://..."        # Anthropic: no /v1 suffix. OpenAI-compatible: include /v1.
key_env = "ANTHROPIC_API_KEY"   # or OPENAI_API_KEY

[mcp]
enabled = true                  # expose the Loogle search tool to workers
```

```bash
export ANTHROPIC_API_KEY=...
cp configs/claude.example.toml configs/claude.toml   # then set base_url
maestro --config configs/claude.toml prove vendor/fatex-source/FATEX/1.lean --run-dir runs/p1
maestro --config configs/claude.toml fatex run --ids 1 2 3 --run-dir runs/batch
```

`mode = "maestro" | "plain" | "naive"` selects the coordinated system or the two baselines.
Budgets (output tokens reserved before each request, events, wall time, turns, compile time)
are hard harness limits.

## Observed runs (smoke tests, single run each)

| Problem | Backend | Result | Output tokens |
|---|---|---|---|
| FATE-X #1 | Claude Opus 5.5 | proved on first prover attempt | 3,418 |
| FATE-X #2 | GPT-6.1-sol | proved on first prover attempt | 19,602 |
| FATE-X #13 | Claude Opus 5.5 | event limit reached | 81,598 |

On #13 the coordinator classified two worker crashes as infrastructure failures and retried,
then acted on a worker's quaternion counterexample by dispatching the falsifier. The crashes
exposed two parsing bugs that are fixed in this version; #13 has not been rerun to completion.

## Trust boundary

A proof counts as closed only if the full file compiles and the theorem's transitive axioms are
within `propext`, `Classical.choice`, `Quot.sound`. `sorryAx` marks an open obligation.
Generated regions may contain only named theorems; imports, definitions, namespaces, settings,
attributes, instances and root statements are frozen.

Lean checks proof validity; it is not an OS sandbox. Model tools cannot run shell commands or
write outside their worker directory. The only network access exposed to models is the Loogle
query tool, and only when `[mcp] enabled = true`.
