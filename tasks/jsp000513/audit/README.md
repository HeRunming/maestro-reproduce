# JSP-000513 statement audit (2026-10-28)

Statement: `../JSP000513.lean`, root `JSP000513.exists_four_choosable_not_eight_two_choosable`.
Source: Dvořák, Hu, Sereni, arXiv:1806.03880 (LaTeX source `dhs-aic.tex`), definitions in the
"Set coloring" paragraph, Theorem 2 (`thm-main`). Catalog: JSP-000513, `problems/catalog-0501-0600.md`.

An independent reviewer (separate agent; given only the paper, the catalog entry, the prize's
statement-audit guide and the Lean file) returned **ACCEPT** with no blocking issues.

| Requirement | Lean | Correspondence |
|---|---|---|
| L-set coloring: φ(v) ⊆ L(v), adjacent sets disjoint | `IsListSetColoring` | equivalent (simple graphs, no loops) |
| (L:b)-coloring: \|φ(v)\| = b | `(φ v).card = b` | equivalent |
| (a:b)-choosable: all L with \|L(v)\| = a | `IsChoosable` | equivalent |
| colors from an arbitrary set | colors in ℕ | equivalent for finite graphs (proved: `gen_iff`) |
| Theorem 2: ∃ G, 4-choosable ∧ ¬(8:2)-choosable | root theorem | equivalent; finiteness required (stronger) |
| ERT question (universal yes/no) | root ⇒ `IntendedStatement` (proved) | complete negative answer |

`StatementChecks.lean` (definitions copied verbatim; compiles with no `sorry`, re-run by the
maintainer): empty/edgeless graphs are (8:2)-choosable; K₂ not (3:2)-, K₃ not 2-, K₅ not
4-choosable; the paper's Lemma 3 5-cycle has no (L₀:2)-coloring; the root statement implies the
literal ERT negation; ℕ colors are equivalent to an arbitrary color type.
