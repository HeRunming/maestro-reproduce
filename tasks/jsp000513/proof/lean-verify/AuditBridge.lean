import Mathlib
import JSP513Proof

/-!
# Independent bridge for JSP-000513 (auditor-written; not part of the submission)

The definitions below are written by the auditor directly from Dvořák, Hu, Sereni,
"A 4-choosable graph that is not (8:2)-choosable", Adv. Comb. 2019:5 (arXiv:1806.03880v2),
paragraph "Set coloring" (dhs-aic.tex lines 135-152), Theorem 2 (`thm-main`, line 198) and the
Erdős–Rubin–Taylor question (abstract, lines 107-110; lines 157-162). They do NOT reuse the
submission's `IsChoosable` / `IsListSetColoring`:

* colors range over an arbitrary type `α` (the paper puts no restriction on colors);
* lists and color sets are `Set α`, sizes are measured with `Set.encard` (so `|L(v)| = a`
  literally, including the requirement that `L(v)` is finite);
* graphs are finite simple graphs.

The only link to the submission is the final theorem
`JSP000513.exists_four_choosable_not_eight_two_choosable`, used as a black box.
-/

namespace AuditJSP513

universe u

/-- Paper: `φ` is an `(L:b)`-coloring of `G` — an `L`-set coloring (`φ v ⊆ L v`, sets of
adjacent vertices disjoint) with `|φ(v)| = b` for every vertex. -/
def IsLbColoring {V : Type} {α : Type u} (G : SimpleGraph V) (L : V → Set α) (b : ℕ)
    (φ : V → Set α) : Prop :=
  (∀ v, φ v ⊆ L v) ∧ (∀ v, (φ v).encard = b) ∧ (∀ u v, G.Adj u v → Disjoint (φ u) (φ v))

/-- Paper: `G` is `(a:b)`-choosable (with colors drawn from `α`) if it is `(L:b)`-colorable
for every list assignment `L` with `|L(v)| = a` for each vertex. -/
def PaperChoosable {V : Type} (α : Type u) (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Set α, (∀ v, (L v).encard = a) → ∃ φ, IsLbColoring G L b φ

/-- Classical (ordinary) `a`-choosability with colors from `α`: every list assignment with
`|L(v)| = a` admits a proper coloring `c` with `c v ∈ L v`. -/
def ClassicalChoosable {V : Type} (α : Type u) (G : SimpleGraph V) (a : ℕ) : Prop :=
  ∀ L : V → Set α, (∀ v, (L v).encard = a) →
    ∃ c : V → α, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- Theorem 2 of the paper, read with colors from an arbitrary type: some finite graph is
4-choosable for every color type, and not (8:2)-choosable for some color type. -/
def IntendedTheorem2 : Prop :=
  ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V),
    (∀ α : Type u, PaperChoosable α G 4 1) ∧ ∃ α : Type, ¬ PaperChoosable α G 8 2

/-- Same, with ordinary 4-choosability (proper colorings by single colors) for the first half
and an explicit bad list assignment over ℕ for the second half. -/
def IntendedTheorem2Explicit : Prop :=
  ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V),
    (∀ α : Type u, ClassicalChoosable α G 4) ∧
    ∃ L : V → Set ℕ, (∀ v, (L v).encard = 8) ∧ ¬ ∃ φ, IsLbColoring G L 2 φ

/-- The Erdős–Rubin–Taylor question: is every `(a:b)`-choosable (finite) graph also
`(am:bm)`-choosable, for all positive integers `a ≥ b` and `m`? -/
def ERTQuestion : Prop :=
  ∀ (V : Type) (_ : Finite V) (G : SimpleGraph V) (a b m : ℕ), 1 ≤ b → b ≤ a → 1 ≤ m →
    (∀ α : Type, PaperChoosable α G a b) → ∀ α : Type, PaperChoosable α G (a * m) (b * m)

/-! ## Transfer lemmas between the submission's ℕ/Finset definitions and the paper's -/

/-- ℕ-colored `Finset` choosability of a finite graph implies choosability with colors from
any type `α`. -/
theorem paper_of_submission {V : Type} [Finite V] (G : SimpleGraph V) (a b : ℕ)
    (h : JSP000513.IsChoosable G a b) (α : Type u) : PaperChoosable α G a b := by
  classical
  intro L hL
  have hfin : ∀ v, (L v).Finite := fun v => Set.finite_of_encard_eq_coe (hL v)
  have hS : (⋃ v, L v).Finite := Set.finite_iUnion hfin
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injOn.mp hS.countable
  have hfv : ∀ v, Set.InjOn f (L v) := fun v => hf.mono (Set.subset_iUnion L v)
  let L' : V → Finset ℕ := fun v => (hfin v).toFinset.image f
  have hL'coe : ∀ v, (L' v : Set ℕ) = f '' L v := by
    intro v; simp [L']
  have hcard : ∀ v, (L' v).card = a := by
    intro v
    have h1 : ((L' v).card : ℕ∞) = (f '' L v).encard := by
      rw [← hL'coe v, Set.encard_coe_eq_coe_finsetCard]
    rw [(hfv v).encard_image, hL v] at h1
    exact_mod_cast h1
  obtain ⟨φ', hφ'⟩ := h L' hcard
  refine ⟨fun v => L v ∩ f ⁻¹' (φ' v : Set ℕ), ?_, ?_, ?_⟩
  · intro v; exact Set.inter_subset_left
  · intro v
    have himg : f '' (L v ∩ f ⁻¹' (φ' v : Set ℕ)) = (φ' v : Set ℕ) := by
      rw [Set.image_inter_preimage, ← hL'coe v]
      exact Set.inter_eq_right.mpr (by exact_mod_cast (hφ'.1 v).1)
    have := ((hfv v).mono (Set.inter_subset_left (t := f ⁻¹' (φ' v : Set ℕ)))).encard_image
    rw [himg, Set.encard_coe_eq_coe_finsetCard, (hφ'.1 v).2] at this
    exact this.symm
  · intro u v huv
    rw [Set.disjoint_left]
    rintro x ⟨_, hxu⟩ ⟨_, hxv⟩
    exact Finset.disjoint_left.mp (hφ'.2 u v huv) hxu hxv

/-- Choosability over ℕ in the paper's sense implies the submission's ℕ/Finset choosability;
hence the submission's non-choosability implies the paper's non-choosability over ℕ. -/
theorem submission_of_paper_nat {V : Type} (G : SimpleGraph V) (a b : ℕ)
    (h : PaperChoosable ℕ G a b) : JSP000513.IsChoosable G a b := by
  classical
  intro L hL
  obtain ⟨φ, hsub, hcard, hdisj⟩ := h (fun v => (L v : Set ℕ))
    (fun v => by rw [Set.encard_coe_eq_coe_finsetCard, hL v])
  have hfin : ∀ v, (φ v).Finite := fun v => (L v).finite_toSet.subset (hsub v)
  refine ⟨fun v => (hfin v).toFinset, fun v => ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    have : x ∈ φ v := (hfin v).mem_toFinset.mp hx
    exact_mod_cast hsub v this
  · have h1 := hcard v
    rw [(hfin v).encard_eq_coe_toFinset_card] at h1
    exact_mod_cast h1
  · intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    exact Set.disjoint_left.mp (hdisj u v huv) ((hfin u).mem_toFinset.mp hxu)
      ((hfin v).mem_toFinset.mp hxv)

theorem classical_of_paper_one {V : Type} {α : Type u} (G : SimpleGraph V) (a : ℕ)
    (h : PaperChoosable α G a 1) : ClassicalChoosable α G a := by
  intro L hL
  obtain ⟨φ, hsub, hcard, hdisj⟩ := h L hL
  have hs : ∀ v, ∃ x, φ v = {x} := fun v => Set.encard_eq_one.mp (by exact_mod_cast hcard v)
  choose c hc using hs
  refine ⟨c, fun v => hsub v (by rw [hc v]; exact rfl), ?_⟩
  intro u v huv heq
  have := hdisj u v huv
  rw [hc u, hc v, heq, Set.disjoint_singleton] at this
  exact this rfl

/-! ## Bridges from the submitted theorem -/

theorem intended_theorem2 : IntendedTheorem2.{u} := by
  obtain ⟨V, _, G, h4, h8⟩ := JSP000513.exists_four_choosable_not_eight_two_choosable
  exact ⟨V, inferInstance, G, fun α => paper_of_submission G 4 1 h4 α,
    ℕ, fun hp => h8 (submission_of_paper_nat G 8 2 hp)⟩

theorem intended_theorem2_explicit : IntendedTheorem2Explicit.{u} := by
  obtain ⟨V, _, G, h4, h8⟩ := JSP000513.exists_four_choosable_not_eight_two_choosable
  refine ⟨V, inferInstance, G, fun α => classical_of_paper_one G 4 (paper_of_submission G 4 1 h4 α), ?_⟩
  by_contra hcon
  push_neg at hcon
  exact h8 (submission_of_paper_nat G 8 2 hcon)

/-- The submitted theorem gives a complete negative answer to the Erdős–Rubin–Taylor question
(instance `a = 4`, `b = 1`, `m = 2`). -/
theorem not_ERTQuestion : ¬ ERTQuestion := by
  intro hq
  obtain ⟨V, hV, G, h4, α, h8⟩ := intended_theorem2.{0}
  exact h8 (hq V hV G 4 1 2 le_rfl (by norm_num) (by norm_num) h4 α)

/-! ## Sanity checks of the auditor's own definitions (non-vacuity) -/

/-- The complete graph on two vertices is not (1:1)-choosable over ℕ (both lists `{0}`). -/
theorem K2_not_one_choosable : ¬ PaperChoosable ℕ (⊤ : SimpleGraph (Fin 2)) 1 1 := by
  intro h
  obtain ⟨φ, hsub, hcard, hdisj⟩ := h (fun _ => {0}) (fun _ => by simp)
  have h0 : ∀ v, φ v = {0} := by
    intro v
    rcases Set.encard_eq_one.mp (hcard v) with ⟨x, hx⟩
    have : x ∈ ({0} : Set ℕ) := hsub v (by rw [hx]; exact rfl)
    rw [hx, Set.mem_singleton_iff.mp this]
  have := hdisj 0 1 (by decide)
  rw [h0, h0] at this
  exact (Set.disjoint_singleton.mp this) rfl

/-- Every graph is vacuously `(a:b)`-choosable only if lists of size `a` exist; on an empty vertex
type everything is choosable (the existential in Theorem 2 therefore needs `¬(8:2)`). -/
theorem empty_choosable (α : Type) (a b : ℕ) : PaperChoosable α (⊥ : SimpleGraph Empty) a b :=
  fun _ _ => ⟨fun _ => ∅, fun v => v.elim, fun v => v.elim, fun u => u.elim⟩

end AuditJSP513

set_option pp.universes false in
#print axioms AuditJSP513.intended_theorem2
#print axioms AuditJSP513.intended_theorem2_explicit
#print axioms AuditJSP513.not_ERTQuestion
#print axioms AuditJSP513.paper_of_submission
#print axioms AuditJSP513.submission_of_paper_nat
#print axioms AuditJSP513.K2_not_one_choosable
#check @AuditJSP513.intended_theorem2
#print AuditJSP513.IntendedTheorem2
#print AuditJSP513.ERTQuestion
