import Mathlib

namespace JSP000513

def IsListSetColoring {V : Type} (G : SimpleGraph V) (L : V → Finset ℕ) (b : ℕ)
    (φ : V → Finset ℕ) : Prop :=
  (∀ v, φ v ⊆ L v ∧ (φ v).card = b) ∧ ∀ u v, G.Adj u v → Disjoint (φ u) (φ v)

def IsChoosable {V : Type} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = a) → ∃ φ : V → Finset ℕ, IsListSetColoring G L b φ

/-- Check 1: single vertex is (8:2)-choosable (non-vacuity of positive side). -/
example : IsChoosable (⊥ : SimpleGraph Unit) 8 2 := by
  intro L hL
  choose φ hsub hcard using fun v => Finset.exists_subset_card_eq (s := L v) (n := 2) (by rw [hL]; norm_num)
  exact ⟨φ, fun v => ⟨hsub v, hcard v⟩, fun u v h => by simp at h⟩

/-- Check 1b: edgeless graphs of any size are (a:b)-choosable for b ≤ a. -/
example {V : Type} (a b : ℕ) (hab : b ≤ a) : IsChoosable (⊥ : SimpleGraph V) a b := by
  intro L hL
  choose φ hsub hcard using fun v => Finset.exists_subset_card_eq (s := L v) (n := b) (by rw [hL]; exact hab)
  exact ⟨φ, fun v => ⟨hsub v, hcard v⟩, fun u v h => by simp at h⟩

/-- Check 2: K₂ is not (3:2)-choosable. -/
example : ¬ IsChoosable (⊤ : SimpleGraph (Fin 2)) 3 2 := by
  intro h
  obtain ⟨φ, hφ, hdis⟩ := h (fun _ => {0,1,2}) (fun _ => rfl)
  have hd := hdis 0 1 (by simp)
  have hu : φ 0 ∪ φ 1 ⊆ {0,1,2} := Finset.union_subset (hφ 0).1 (hφ 1).1
  have := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hd, (hφ 0).2, (hφ 1).2] at this
  simp at this

/-- Check 3: K₃ is not 2-choosable (b = 1 case behaves as ordinary list coloring). -/
example : ¬ IsChoosable (⊤ : SimpleGraph (Fin 3)) 2 1 := by
  intro h
  obtain ⟨φ, hφ, hdis⟩ := h (fun _ => {0,1}) (fun _ => rfl)
  have h01 := hdis 0 1 (by simp); have h02 := hdis 0 2 (by simp); have h12 := hdis 1 2 (by simp)
  have hu : φ 0 ∪ φ 1 ∪ φ 2 ⊆ {0,1} :=
    Finset.union_subset (Finset.union_subset (hφ 0).1 (hφ 1).1) (hφ 2).1
  have := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨h02, h12⟩),
    Finset.card_union_of_disjoint h01, (hφ 0).2, (hφ 1).2, (hφ 2).2] at this
  simp at this

/-- Check 4: K₄ ⊆ ... the trivial graph K₁ is 4-choosable and a 5-clique is not 4-choosable. -/
example : ¬ IsChoosable (⊤ : SimpleGraph (Fin 5)) 4 1 := by
  intro h
  obtain ⟨φ, hφ, hdis⟩ := h (fun _ => {0,1,2,3}) (fun _ => rfl)
  have hinj : ∀ i j : Fin 5, i ≠ j → Disjoint (φ i) (φ j) := fun i j hij => hdis i j hij
  have hcard : (Finset.univ.biUnion φ).card = 5 := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hinj i j hij)]; simp [fun v => (hφ v).2]
  have hsub : Finset.univ.biUnion φ ⊆ {0,1,2,3} := Finset.biUnion_subset.2 (fun v _ => (hφ v).1)
  have := Finset.card_le_card hsub
  rw [hcard] at this; simp at this

/-- Check 5: paper's Lemma 3 (lemma-pent) second half: C₅ with L₀ has no (L₀:2)-coloring. -/
def C5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun i j => j = i + 1)
instance : DecidableRel C5.Adj := by unfold C5; infer_instance

def L0 : Fin 5 → Finset ℕ := ![{1,2,5,6}, {1,4,5,6}, {3,4,5,6}, {3,4,5,6}, {2,4,5,6}]

-- explicit nested enumeration over 2-subsets of each list; edges v0v1, v1v2, v2v3, v3v4, v4v0
set_option maxRecDepth 100000 in
theorem pent_finite :
    ∀ s0 ∈ (L0 0).powersetCard 2, ∀ s1 ∈ (L0 1).powersetCard 2, ∀ s2 ∈ (L0 2).powersetCard 2,
    ∀ s3 ∈ (L0 3).powersetCard 2, ∀ s4 ∈ (L0 4).powersetCard 2,
      ¬ (Disjoint s0 s1 ∧ Disjoint s1 s2 ∧ Disjoint s2 s3 ∧ Disjoint s3 s4 ∧ Disjoint s4 s0) := by
  decide +kernel

example : ¬ ∃ φ, IsListSetColoring C5 L0 2 φ := by
  rintro ⟨φ, hφ, hdis⟩
  have m := fun v => Finset.mem_powersetCard.2 (hφ v)
  exact pent_finite _ (m 0) _ (m 1) _ (m 2) _ (m 3) _ (m 4)
    ⟨hdis 0 1 (by decide), hdis 1 2 (by decide), hdis 2 3 (by decide), hdis 3 4 (by decide),
     hdis 4 0 (by decide)⟩

/-- Check 6: target theorem implies the general negative answer to the ERT question
(with m = 2), stated independently. -/
def IntendedStatement : Prop :=
  ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (a b m : ℕ), 0 < b → b ≤ a → 0 < m →
      IsChoosable G a b → IsChoosable G (a * m) (b * m)

example (h : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      IsChoosable G 4 1 ∧ ¬ IsChoosable G 8 2) : IntendedStatement := by
  obtain ⟨V, _, G, h4, h8⟩ := h
  intro hall
  exact h8 (hall V G 4 1 2 (by norm_num) (by norm_num) (by norm_num) h4)

/-- Check 7: color-type independence. Choosability with an arbitrary color type `α`
(with `DecidableEq`) is equivalent to choosability with ℕ colors for finite graphs. -/
def IsChoosableGen {V : Type} (G : SimpleGraph V) (a b : ℕ) (α : Type) [DecidableEq α] : Prop :=
  ∀ L : V → Finset α, (∀ v, (L v).card = a) → ∃ φ : V → Finset α,
    (∀ v, φ v ⊆ L v ∧ (φ v).card = b) ∧ ∀ u v, G.Adj u v → Disjoint (φ u) (φ v)

theorem gen_iff {V : Type} [Fintype V] (G : SimpleGraph V) (a b : ℕ) :
    IsChoosable G a b ↔ ∀ (α : Type) [DecidableEq α], IsChoosableGen G a b α := by
  constructor
  · intro h α _ L hL
    classical
    -- relabel the finitely many used colors into ℕ
    let S : Finset α := Finset.univ.biUnion L
    let e : S ≃ Fin S.card := S.equivFin
    let f : α ↪ ℕ ⊕ α := ⟨Sum.inr, Sum.inr_injective⟩
    -- injective map S → ℕ
    let g : S ↪ ℕ := ⟨fun x => (e x : ℕ), fun x y hxy => e.injective (Fin.ext hxy)⟩
    have hmem : ∀ v, ∀ c ∈ L v, c ∈ S := fun v c hc => Finset.mem_biUnion.2 ⟨v, by simp, hc⟩
    let L' : V → Finset ℕ := fun v => (L v).attach.map
      ⟨fun c => g ⟨c.1, hmem v c.1 c.2⟩, fun x y hxy => by
        have := g.injective hxy; exact Subtype.ext (by simpa using congrArg Subtype.val this)⟩
    obtain ⟨φ', hφ', hdis'⟩ := h L' (fun v => by simp [L', hL])
    let φ : V → Finset α := fun v => (L v).filter (fun c => ∃ hc : c ∈ S, g ⟨c, hc⟩ ∈ φ' v)
    refine ⟨φ, fun v => ⟨Finset.filter_subset _ _, ?_⟩, fun u v huv => ?_⟩
    · rw [← (hφ' v).2]
      symm
      apply Finset.card_bij (fun n hn => (e.symm ⟨n, ?_⟩ : S).1)
      · intro n hn
        have := (hφ' v).1 hn
        simp only [L', Finset.mem_map, Finset.mem_attach, true_and] at this
        obtain ⟨c, rfl⟩ := this
        simp only [φ, Finset.mem_filter]
        refine ⟨by simp [g], ?_⟩
        exact ⟨by simpa [g] using hmem v c.1 c.2, by simpa [g] using hn⟩
      · intro n₁ h₁ n₂ h₂ heq
        have := e.symm.injective (Subtype.ext heq)
        simpa using congrArg Fin.val this
      · intro c hc
        simp only [φ, Finset.mem_filter] at hc
        obtain ⟨hcL, hcS, hg⟩ := hc
        exact ⟨g ⟨c, hcS⟩, hg, by simp [g]⟩
      · have := (hφ' v).1 hn
        simp only [L', Finset.mem_map, Finset.mem_attach, true_and] at this
        obtain ⟨c, rfl⟩ := this
        simp [g]
    · rw [Finset.disjoint_left]
      intro c hu hv
      simp only [φ, Finset.mem_filter] at hu hv
      obtain ⟨_, hS, h1⟩ := hu
      obtain ⟨_, hS', h2⟩ := hv
      exact Finset.disjoint_left.1 (hdis' u v huv) h1 h2
  · intro h
    exact h ℕ
