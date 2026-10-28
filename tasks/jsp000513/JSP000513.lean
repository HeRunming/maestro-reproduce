import Mathlib

/-!
# JSP-000513

Catalog question: does list multicolorability persist when both the available-list size and
the required number of colors per vertex are doubled?

Erdős, Rubin and Taylor (1980) asked whether every `(a:b)`-choosable graph is
`(am:bm)`-choosable. Dvořák, Hu and Sereni, *A 4-choosable graph that is not
(8:2)-choosable*, Adv. Comb. 2019:5 (arXiv:1806.03880), Theorem 2, answer this negatively:
there is a graph that is 4-choosable but not (8:2)-choosable.

Definitions follow the paper's "Set coloring" paragraph. Colors are natural numbers; a list
assignment gives every vertex a finite set of colors.
-/

namespace JSP000513

/-- `φ` is an `(L:b)`-coloring of `G`: every vertex receives a `b`-element subset of its
list, and adjacent vertices receive disjoint sets. -/
def IsListSetColoring {V : Type} (G : SimpleGraph V) (L : V → Finset ℕ) (b : ℕ)
    (φ : V → Finset ℕ) : Prop :=
  (∀ v, φ v ⊆ L v ∧ (φ v).card = b) ∧ ∀ u v, G.Adj u v → Disjoint (φ u) (φ v)

/-- `G` is `(a:b)`-choosable: it has an `(L:b)`-coloring for every list assignment `L`
with `|L v| = a` for all vertices `v`. `(a:1)`-choosable is ordinary `a`-choosability. -/
def IsChoosable {V : Type} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = a) → ∃ φ : V → Finset ℕ, IsListSetColoring G L b φ

theorem exists_four_choosable_not_eight_two_choosable :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      IsChoosable G 4 1 ∧ ¬ IsChoosable G 8 2 := by
  sorry

end JSP000513
