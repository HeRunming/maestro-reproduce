# JSP-000513 proof: verification record (2026-10-28)

`JSP000513_proof.lean` (sha256 `404aa3a0bc3127211736cfdca927324b490f98dda2df77513446b717c4110821`)
proves `JSP000513.exists_four_choosable_not_eight_two_choosable`:

```lean
∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), IsChoosable G 4 1 ∧ ¬ IsChoosable G 8 2
```

i.e. Theorem 2 of Dvořák, Hu, Sereni (arXiv:1806.03880), a negative answer to the
Erdős–Rubin–Taylor question. The statement was audited independently before any proof
attempt (`../audit/`, verdict ACCEPT).

## Checks performed

| Check | Result |
|---|---|
| Frozen prefix/suffix (imports, `IsListSetColoring`, `IsChoosable`, namespace) identical to `../JSP000513.lean` | yes |
| Root theorem signature identical to the audited statement | yes |
| Standalone `lake env lean` + `#print axioms` (outside the harness) | `[propext, Classical.choice, Quot.sound]` |
| `sorry`, `admit`, `native_decide`, `axiom`, `debug.*`, attributes, `#` commands in file | none |
| Toolchain | Lean 4.28.0, Mathlib v4.28.0 (`8f9d9cff`) as pinned by FATE-X |

Not yet done: an independent kernel replay (e.g. lean4checker) and a review following the
prize's `lean-verify` skill. The catalog lists JSP-000513 as not eligible to claim.

## Proof structure (1226 lines, 7 defs, 58 theorems)

- `g5Edges`/`g5Graph`/`g5List`: the paper's 37-vertex gadget (G5, L5), built from G1–G4.
- Not (8:2)-choosable: 5-cycle has no (4:2)-coloring; forcing lemmas for G2–G4
  (`tri_78`, `g5_y4`, `g5_z7`, `g5_w`, `g5_pent`, `g5_two_core`) give `g5_not_two`.
- Half-list colorability of G5 (`g5_half`): case split as in the paper, `g5_half_eq`
  (all lists on C2 equal) and `g5_half_noneq` (via `hn_*` lemmas: rim, gadget, glue).
- `uniGraph`/`uniList`: the paper's list-uniformization (4-clique plus one gadget copy per
  (L':2)-coloring of the clique), `uni_choosable` and `uni_not_choosable`.

## How it was produced

MAESTRO reproduction (this repository), Claude Opus 5.5 workers and coordinator, with the
paper's LaTeX body as reference text:

| Run | Start | Result | Output tokens |
|---|---|---|---|
| `jsp000513-run1` | from scratch, no reference | stopped after ~7 min (workers lacked the construction) | not recorded |
| `jsp000513-run2` | from scratch, with reference | budget exhausted at revision 30: 44/54 theorems | 1,973,691 |
| `jsp000513-run3` | `--resume` revision 30 | **proved**, revision 9 | 287,863 |
