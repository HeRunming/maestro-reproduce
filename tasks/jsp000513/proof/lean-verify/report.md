# Lean verification report: JSP-000513 (pre-submission self-check)

Produced by an independent agent following the awards repository's `lean-verify` skill
(TheJustinSunPrize/awards `fbaf42fcf8cfc036e00e9ae58a367155e8283e5a`), 2026-10-28
18:07–18:22 +08:00. The maintainer reproduced the bridge compile, its `#print axioms` and both
`leanchecker` runs afterwards.

**Overall verdict: Verification passed** for proof commit
`cb8b4285830f6ba69a686945ee7786a4ba7158c0` (standard Lean trust only).

The proof solves JSP-000513, the Erdős–Rubin–Taylor question "is every (a:b)-choosable graph
also (am:bm)-choosable?", by proving `JSP000513.exists_four_choosable_not_eight_two_choosable`:
a finite simple graph that is 4-choosable but not (8:2)-choosable. That is a counterexample with
a=4, b=1, m=2, the "doubling" the catalog asks about.

| Required question | Judgment | Decisive evidence |
| --- | --- | --- |
| Does the proof address the original problem? | Yes | `IsListSetColoring`/`IsChoosable` (proof lines 22-30, identical to the audited statement) match the paper's "Set coloring" paragraph (`dhs-aic.tex` 135-152); the statement matches Theorem 2 (197-199). ℕ colors are proved equivalent to arbitrary colors for finite graphs (`AuditJSP513.paper_of_submission`, `submission_of_paper_nat`). |
| Did the specified commit pass verification? | Yes | `lake env lean`: exit 0, linter warnings only. `#print axioms`: `[propext, Classical.choice, Quot.sound]`. `leanchecker --verbose JSP513Proof`: exit 0. |
| Does it fully solve the original problem? | Yes (complete disproof by counterexample) | `AuditJSP513.not_ERTQuestion : ¬ ERTQuestion`, proved from the submitted theorem. No other subproblems. |
| Lean completeness requirements | Meets | No `sorry`, custom axioms or `native_decide`; the theorem has no hypotheses. |

## Verification levels

1. Static review: done.
2. Lean checks with the pinned toolchain (Lean 4.28.0, Mathlib v4.28.0 `8f9d9cff`): done.
3. Kernel replay with `leanchecker` (non-fresh) of the proof module and of the bridge: done.
4. `leanchecker --fresh` replay of the whole import closure: run separately by the maintainer
   from an identical copy (sha256 `404aa3a0…4110821`): exit 0 in 3128 s. Done.
5. Independent external checker or comparator: not done (none available offline).

## Coverage

| # | Paper requirement | Lean | Correspondence |
| --- | --- | --- | --- |
| R1 | L-set coloring: φ(v) ⊆ L(v), adjacent sets disjoint | `IsListSetColoring` | Equivalent (simple, loopless, undirected) |
| R2 | \|φ(v)\| = b | `(φ v).card = b` | Equivalent |
| R3 | (a:b)-choosable over any colors | `IsChoosable`, ℕ colors | Equivalent for finite graphs, proved both ways |
| R4 | a-choosable = (a:1)-choosable | `IsChoosable G 4 1` | Proved to give ordinary list coloring (`classical_of_paper_one`) |
| R5 | finite simple graph | `Fintype V`, `SimpleGraph` | Equivalent or stronger |
| R6 | Theorem 2 | target theorem | Equivalent (`AuditJSP513.intended_theorem2`, any color type, `Set`/`encard`) |
| R7 | ERT question / catalog "doubled" | `AuditJSP513.not_ERTQuestion` | Complete negative answer |
| R8 | Definitions non-trivial | `K2_not_one_choosable`, `empty_choosable` | Supporting |

## Environment

- Toolchain binaries byte-identical to the official v4.28.0 release archive (sha256 matches the
  GitHub release digest). Mathlib and all 8 transitive dependencies match their pinned upstream
  commits by git tree hash.
- Mathlib `.olean` files come from the official cache (not rebuilt); `lake build --no-build
  --rehash Mathlib` reports all 8025 targets up to date.
- `audit.py preflight`/`prepare`: exit 0. `audit.py run` needs the proof to be a Lake module;
  the equivalent steps were run by hand and classified with the script's own functions
  (`standard_axioms_only`).

## Limitations

- L1: at audit time the commit was not on the public remote; cite it only after pushing.
- L2: resolved; the `--fresh` replay re-checked the whole import closure (level 4).
- L3: no container/VM isolation; checks ran as root. The proof file contains no metaprograms,
  environment-modifying commands or I/O.
- L4: no independent kernel or comparator.
- L5: an expert may confirm "graph" in the paper means a finite simple graph; the Lean statement
  requires finiteness, so it is at least as strong.

Files here: `AuditBridge.lean` (the auditor's independent statement and bridge proofs; compile it
with the proof compiled as module `JSP513Proof`), `targets.json` (audit manifest).
