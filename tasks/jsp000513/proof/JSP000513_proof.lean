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

-- MAESTRO GENERATED BEGIN
def g5Edges : List (Fin 37 × Fin 37) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (5, 6), (6, 2), (0, 7), (7, 2), (2, 8), (8, 9), (9, 0), (10, 0), (10, 7), (10, 2), (10, 8), (10, 9), (11, 12), (12, 13), (11, 13), (10, 11), (13, 14), (13, 15), (14, 16), (14, 17), (15, 16), (15, 17), (16, 17), (18, 19), (19, 20), (18, 20), (17, 18), (13, 21), (13, 22), (21, 23), (21, 24), (22, 23), (22, 24), (23, 24), (25, 26), (26, 27), (25, 27), (24, 25), (28, 29), (29, 30), (28, 30), (31, 32), (32, 33), (31, 33), (34, 35), (35, 36), (34, 36), (20, 28), (27, 28), (30, 31), (30, 34), (33, 1), (33, 3), (36, 5), (36, 6)]

def g5Graph : SimpleGraph (Fin 37) := SimpleGraph.fromRel (fun a b => (a, b) ∈ g5Edges)

def g5List (v : Fin 37) : Finset ℕ := match v.val with
  | 0 => {1, 2, 3, 4, 5, 6}
  | 1 => {1, 4, 5, 6, 7, 8}
  | 2 => {1, 2, 3, 4, 5, 6}
  | 3 => {3, 4, 5, 6, 7, 8}
  | 4 => {2, 4, 5, 6}
  | 5 => {1, 2, 3, 4, 7, 8}
  | 6 => {1, 2, 7, 8}
  | 7 => {1, 2, 3, 4, 5, 6}
  | 8 => {1, 2, 3, 4, 5, 6}
  | 9 => {1, 2, 3, 4, 5, 6}
  | 10 => {1, 2, 3, 4, 5, 6, 7, 8}
  | 11 => {1, 2, 3, 4, 7, 8}
  | 12 => {1, 2, 3, 4}
  | 13 => {1, 2, 3, 4, 7, 8}
  | 14 => {1, 2, 3, 7}
  | 15 => {4, 5, 6, 7}
  | 16 => {1, 2, 3, 4, 5, 6}
  | 17 => {1, 2, 3, 4, 5, 6, 7, 8}
  | 18 => {1, 2, 3, 4, 7, 8}
  | 19 => {1, 2, 3, 4}
  | 20 => {1, 2, 3, 4, 7, 8}
  | 21 => {1, 2, 3, 8}
  | 22 => {4, 5, 6, 8}
  | 23 => {1, 2, 3, 4, 5, 6}
  | 24 => {1, 2, 3, 4, 5, 6, 7, 8}
  | 25 => {1, 2, 3, 4, 7, 8}
  | 26 => {1, 2, 3, 4}
  | 27 => {1, 2, 3, 4, 7, 8}
  | 28 => {1, 2, 3, 4, 7, 8}
  | 29 => {1, 2, 3, 4}
  | 30 => {1, 2, 3, 4, 7, 8}
  | 31 => {1, 2, 3, 4, 7, 8}
  | 32 => {1, 2, 3, 4}
  | 33 => {1, 2, 3, 4, 7, 8}
  | 34 => {1, 2, 3, 4, 7, 8}
  | 35 => {1, 2, 3, 4}
  | _ => {1, 2, 3, 4, 7, 8}

def uniRel {W : Type} (H : SimpleGraph W) (L5 : W → Finset ℕ) (a b : Fin 4 ⊕ ((Fin 4 → Finset (Fin 8)) × W)) : Prop := match a, b with
  | Sum.inl i, Sum.inl j => i ≠ j
  | Sum.inl i, Sum.inr p => i.val < 4 - (L5 p.2).card / 2
  | Sum.inr p, Sum.inr q => p.1 = q.1 ∧ H.Adj p.2 q.2
  | Sum.inr _, Sum.inl _ => False

def uniGraph {W : Type} (H : SimpleGraph W) (L5 : W → Finset ℕ) : SimpleGraph (Fin 4 ⊕ ((Fin 4 → Finset (Fin 8)) × W)) := SimpleGraph.fromRel (uniRel H L5)

def uniIntended {W : Type} (L5 : W → Finset ℕ) (p : (Fin 4 → Finset (Fin 8)) × W) : Finset ℕ := L5 p.2 ∪ (Finset.univ.filter (fun i : Fin 4 => i.val < 4 - (L5 p.2).card / 2)).biUnion (fun i => (p.1 i).image (fun k : Fin 8 => k.val + 9))

def uniList {W : Type} (L5 : W → Finset ℕ) (a : Fin 4 ⊕ ((Fin 4 → Finset (Fin 8)) × W)) : Finset ℕ := match a with
  | Sum.inl _ => Finset.Icc 9 16
  | Sum.inr p => if (uniIntended L5 p).card = 8 then uniIntended L5 p else Finset.range 8

theorem g5_sub : ∀ v : Fin 37, g5List v ⊆ Finset.range 9 := by
  intro v
  fin_cases v <;> first | decide | simp [g5List, Finset.subset_iff]

theorem g5_card : ∀ v : Fin 37, (g5List v).card % 2 = 0 ∧ (g5List v).card ≤ 8 := by
  intro v
  fin_cases v <;> decide

theorem c5_no_four_two (S a b c d e : Finset ℕ) (hS : S.card = 4) (ha : a ⊆ S) (hb : b ⊆ S) (hc : c ⊆ S) (hd : d ⊆ S) (he : e ⊆ S) (ha2 : a.card = 2) (hb2 : b.card = 2) (hc2 : c.card = 2) (hd2 : d.card = 2) (he2 : e.card = 2) (hab : Disjoint a b) (hbc : Disjoint b c) (hcd : Disjoint c d) (hde : Disjoint d e) (hea : Disjoint e a) : False := by
  have key : ∀ x y : Finset ℕ, x ⊆ S → y ⊆ S → x.card = 2 → y.card = 2 → Disjoint x y → x = S \ y := by
    intro x y hx hy hx2 hy2 hxy
    have hu : x ∪ y = S := Finset.eq_of_subset_of_card_le (Finset.union_subset hx hy)
      (by rw [Finset.card_union_of_disjoint hxy]; omega)
    rw [← hu, Finset.union_sdiff_cancel_right hxy]
  have h1 : a = S \ b := key a b ha hb ha2 hb2 hab
  have h2 : c = S \ b := key c b hc hb hc2 hb2 hbc.symm
  have h3 : d = S \ c := key d c hd hc hd2 hc2 hcd.symm
  have h4 : b = S \ c := key b c hb hc hb2 hc2 hbc
  have h5 : e = S \ d := key e d he hd he2 hd2 hde.symm
  have hac : a = c := h1.trans h2.symm
  have hdb : d = b := h3.trans h4.symm
  have hea' : e = a := by rw [h5, hdb, h1]
  rw [hea'] at hea
  have : a = ∅ := disjoint_self.mp hea
  rw [this] at ha2
  simp at ha2

theorem tri_78 (a b c : Finset ℕ) (ha : a ⊆ {1, 2, 3, 4}) (hb : b ⊆ {1, 2, 3, 4}) (hc : c ⊆ {1, 2, 3, 4, 7, 8}) (ha2 : a.card = 2) (hb2 : b.card = 2) (hc2 : c.card = 2) (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) : c = {7, 8} := by
  have hu : a ∪ b = {1, 2, 3, 4} := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset ha hb)
    rw [Finset.card_union_of_disjoint hab, ha2, hb2]
    rfl
  have hcd : Disjoint (a ∪ b) c := Finset.disjoint_union_left.mpr ⟨hac, hbc⟩
  rw [hu] at hcd
  have hc' : c ⊆ {7, 8} := by
    intro x hx
    have h1 := hc hx
    have h2 : x ∉ ({1, 2, 3, 4} : Finset ℕ) := Finset.disjoint_right.mp hcd hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
    omega
  exact Finset.eq_of_subset_of_card_le hc' (by rw [hc2]; rfl)

theorem g5_y4 (φ : Fin 37 → Finset ℕ) (hφ : IsListSetColoring g5Graph g5List 2 φ) : (φ 13 ∩ {7, 8}).Nonempty := by
  by_contra hne
  have adj : ∀ u v : Fin 37, (u, v) ∈ g5Edges → Disjoint (φ u) (φ v) ∧ Disjoint (φ v) (φ u) := by
    intro u v huv
    by_cases h : u = v
    · subst h; exact absurd huv (by revert huv; revert u; decide)
    · have h1 : g5Graph.Adj u v := by
        rw [g5Graph, SimpleGraph.fromRel_adj]; exact ⟨h, Or.inl huv⟩
      exact ⟨hφ.2 u v h1, hφ.2 v u h1.symm⟩
  have h13 : φ 13 ⊆ {1, 2, 3, 4, 7, 8} := (hφ.1 13).1
  have h13' : φ 13 ⊆ {1, 2, 3, 4} := by
    intro x hx
    have h1 := h13 hx
    have hx78 : x ∉ ({7, 8} : Finset ℕ) := fun h' => hne ⟨x, Finset.mem_inter.2 ⟨hx, h'⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 hx78 ⊢
    omega
  have h12 : φ 12 ⊆ {1, 2, 3, 4} := (hφ.1 12).1
  have h11 : φ 11 ⊆ {1, 2, 3, 4, 7, 8} := (hφ.1 11).1
  have e11 : φ 11 = {7, 8} :=
    tri_78 (φ 12) (φ 13) (φ 11) h12 h13' h11 (hφ.1 12).2 (hφ.1 13).2 (hφ.1 11).2
      (adj 12 13 (by decide)).1 (adj 11 12 (by decide)).2 (adj 11 13 (by decide)).2
  have h10 : φ 10 ⊆ {1, 2, 3, 4, 5, 6, 7, 8} := (hφ.1 10).1
  have d1011 := (adj 10 11 (by decide)).1
  rw [e11] at d1011
  have h10' : φ 10 ⊆ {1, 2, 3, 4, 5, 6} := by
    intro x hx
    have h1 := h10 hx
    have hx78 : x ∉ ({7, 8} : Finset ℕ) := Finset.disjoint_left.1 d1011 hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 hx78 ⊢
    omega
  have hS : (({1, 2, 3, 4, 5, 6} : Finset ℕ) \ φ 10).card = 4 := by
    rw [Finset.card_sdiff_of_subset h10', (hφ.1 10).2]; rfl
  have sub : ∀ v : Fin 37, φ v ⊆ {1, 2, 3, 4, 5, 6} → (10, v) ∈ g5Edges →
      φ v ⊆ ({1, 2, 3, 4, 5, 6} : Finset ℕ) \ φ 10 := by
    intro v hv he
    exact Finset.subset_sdiff.2 ⟨hv, (adj 10 v he).2⟩
  exact c5_no_four_two _ (φ 0) (φ 7) (φ 2) (φ 8) (φ 9) hS
    (sub 0 (hφ.1 0).1 (by decide)) (sub 7 (hφ.1 7).1 (by decide))
    (sub 2 (hφ.1 2).1 (by decide)) (sub 8 (hφ.1 8).1 (by decide))
    (sub 9 (hφ.1 9).1 (by decide))
    (hφ.1 0).2 (hφ.1 7).2 (hφ.1 2).2 (hφ.1 8).2 (hφ.1 9).2
    (adj 0 7 (by decide)).1 (adj 7 2 (by decide)).1 (adj 2 8 (by decide)).1
    (adj 8 9 (by decide)).1 (adj 9 0 (by decide)).1

theorem z_chain (c : ℕ) (hc : c = 7 ∨ c = 8) (Y B C D E F G H : Finset ℕ) (hcY : c ∈ Y) (hB : B ⊆ {1, 2, 3, c}) (hC : C ⊆ {4, 5, 6, c}) (hD : D ⊆ {1, 2, 3, 4, 5, 6}) (hE : E ⊆ {1, 2, 3, 4, 5, 6, 7, 8}) (hF : F ⊆ {1, 2, 3, 4, 7, 8}) (hG : G ⊆ {1, 2, 3, 4}) (hH : H ⊆ {1, 2, 3, 4, 7, 8}) (hB2 : B.card = 2) (hC2 : C.card = 2) (hD2 : D.card = 2) (hE2 : E.card = 2) (hF2 : F.card = 2) (hG2 : G.card = 2) (hH2 : H.card = 2) (hYB : Disjoint Y B) (hYC : Disjoint Y C) (hBD : Disjoint B D) (hBE : Disjoint B E) (hCD : Disjoint C D) (hCE : Disjoint C E) (hDE : Disjoint D E) (hEF : Disjoint E F) (hFG : Disjoint F G) (hGH : Disjoint G H) (hFH : Disjoint F H) : H = {7, 8} := by
  have hcB : c ∉ B := Finset.disjoint_left.mp hYB hcY
  have hcC : c ∉ C := Finset.disjoint_left.mp hYC hcY
  have hB' : ∀ x ∈ B, x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x hx
    have h1 := hB hx
    have h2 : x ≠ c := fun h => hcB (h ▸ hx)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hC' : ∀ x ∈ C, x = 4 ∨ x = 5 ∨ x = 6 := by
    intro x hx
    have h1 := hC hx
    have h2 : x ≠ c := fun h => hcC (h ▸ hx)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hBC : Disjoint B C := Finset.disjoint_left.mpr fun {x} hx hx' => by
    have := hB' x hx
    have := hC' x hx'
    omega
  have hU : (B ∪ C ∪ D).card = 6 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hBD, hCD⟩),
      Finset.card_union_of_disjoint hBC, hB2, hC2, hD2]
  have hU' : B ∪ C ∪ D = {1, 2, 3, 4, 5, 6} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_union] at hx
      rcases hx with (hx | hx) | hx
      · have := hB' x hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · have := hC' x hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · exact hD hx
    · rw [hU]; decide
  have hE' : E = {7, 8} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have h1 := hE hx
      have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hBE h hx
      have hxC : x ∉ C := fun h => Finset.disjoint_left.mp hCE h hx
      have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hDE h hx
      have hxU : x ∉ B ∪ C ∪ D := by
        simp only [Finset.mem_union]
        tauto
      rw [hU'] at hxU
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 hxU ⊢
      omega
    · rw [hE2]; decide
  have hF' : F ⊆ {1, 2, 3, 4} := by
    intro x hx
    have h1 := hF hx
    have h2 : x ∉ E := fun h => Finset.disjoint_left.mp hEF h hx
    rw [hE'] at h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
    omega
  exact tri_78 F G H hF' hG hH hF2 hG2 hH2 hFG hFH hGH

theorem g5_z7 (φ : Fin 37 → Finset ℕ) (hφ : IsListSetColoring g5Graph g5List 2 φ) : φ 20 = {7, 8} ∨ φ 27 = {7, 8} := by
  obtain ⟨x, hx⟩ := g5_y4 φ hφ
  obtain ⟨hL, hA⟩ := hφ
  have e : ∀ u v : Fin 37, (u ≠ v ∧ (u, v) ∈ g5Edges) → Disjoint (φ u) (φ v) := by
    intro u v h
    apply hA u v
    rw [g5Graph, SimpleGraph.fromRel_adj]
    exact ⟨h.1, Or.inl h.2⟩
  rw [Finset.mem_inter] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hx3 : x = 7 ∨ x = 8 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    exact hx2
  rcases hx3 with rfl | rfl
  · left
    exact z_chain 7 (Or.inl rfl) (φ 13) (φ 14) (φ 15) (φ 16) (φ 17) (φ 18) (φ 19) (φ 20) hx1
      (hL 14).1 (hL 15).1 (hL 16).1 (hL 17).1 (hL 18).1 (hL 19).1 (hL 20).1
      (hL 14).2 (hL 15).2 (hL 16).2 (hL 17).2 (hL 18).2 (hL 19).2 (hL 20).2
      (e 13 14 (by decide)) (e 13 15 (by decide)) (e 14 16 (by decide)) (e 14 17 (by decide))
      (e 15 16 (by decide)) (e 15 17 (by decide)) (e 16 17 (by decide)) (e 17 18 (by decide))
      (e 18 19 (by decide)) (e 19 20 (by decide)) (e 18 20 (by decide))
  · right
    exact z_chain 8 (Or.inr rfl) (φ 13) (φ 21) (φ 22) (φ 23) (φ 24) (φ 25) (φ 26) (φ 27) hx1
      (hL 21).1 (hL 22).1 (hL 23).1 (hL 24).1 (hL 25).1 (hL 26).1 (hL 27).1
      (hL 21).2 (hL 22).2 (hL 23).2 (hL 24).2 (hL 25).2 (hL 26).2 (hL 27).2
      (e 13 21 (by decide)) (e 13 22 (by decide)) (e 21 23 (by decide)) (e 21 24 (by decide))
      (e 22 23 (by decide)) (e 22 24 (by decide)) (e 23 24 (by decide)) (e 24 25 (by decide))
      (e 25 26 (by decide)) (e 26 27 (by decide)) (e 25 27 (by decide))

theorem g5w_sub78 (c : Finset ℕ) (hc : c ⊆ {1, 2, 3, 4, 7, 8}) (hd : Disjoint c {7, 8}) : c ⊆ {1, 2, 3, 4} := by
  intro x hx
  have h1 := hc hx
  have h2 := Finset.disjoint_left.mp hd hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
  omega

theorem g5w_tri (φ : Fin 37 → Finset ℕ) (hφ : IsListSetColoring g5Graph g5List 2 φ)
    (p a b c : Fin 37) (hp : φ p = {7, 8})
    (hpa : g5Graph.Adj p a) (hab : g5Graph.Adj a b)
    (hac : g5Graph.Adj a c) (hbc : g5Graph.Adj b c)
    (hLa : g5List a = {1, 2, 3, 4, 7, 8}) (hLb : g5List b = {1, 2, 3, 4})
    (hLc : g5List c = {1, 2, 3, 4, 7, 8}) : φ c = {7, 8} := by
  have ha : φ a ⊆ {1, 2, 3, 4} := by
    apply g5w_sub78
    · rw [← hLa]; exact (hφ.1 a).1
    · rw [← hp]; exact (hφ.2 p a hpa).symm
  have hb : φ b ⊆ {1, 2, 3, 4} := by
    rw [← hLb]; exact (hφ.1 b).1
  have hc : φ c ⊆ {1, 2, 3, 4, 7, 8} := by
    rw [← hLc]; exact (hφ.1 c).1
  exact tri_78 (φ a) (φ b) (φ c) ha hb hc (hφ.1 a).2 (hφ.1 b).2 (hφ.1 c).2
    (hφ.2 a b hab) (hφ.2 a c hac) (hφ.2 b c hbc)

theorem g5_w (φ : Fin 37 → Finset ℕ) (hφ : IsListSetColoring g5Graph g5List 2 φ) : φ 33 = {7, 8} ∧ φ 36 = {7, 8} := by
  have adj : ∀ a b : Fin 37, a ≠ b ∧ ((a, b) ∈ g5Edges ∨ (b, a) ∈ g5Edges) → g5Graph.Adj a b := by
    intro a b h
    rw [g5Graph, SimpleGraph.fromRel_adj]
    exact h
  have h30 : φ 30 = {7, 8} := by
    rcases g5_z7 φ hφ with h | h
    · exact g5w_tri φ hφ 20 28 29 30 h (adj _ _ (by decide))
        (adj _ _ (by decide)) (adj _ _ (by decide)) (adj _ _ (by decide)) rfl rfl rfl
    · exact g5w_tri φ hφ 27 28 29 30 h (adj _ _ (by decide))
        (adj _ _ (by decide)) (adj _ _ (by decide)) (adj _ _ (by decide)) rfl rfl rfl
  refine ⟨?_, ?_⟩
  · exact g5w_tri φ hφ 30 31 32 33 h30 (adj _ _ (by decide))
        (adj _ _ (by decide)) (adj _ _ (by decide)) (adj _ _ (by decide)) rfl rfl rfl
  · exact g5w_tri φ hφ 30 34 35 36 h30 (adj _ _ (by decide))
        (adj _ _ (by decide)) (adj _ _ (by decide)) (adj _ _ (by decide)) rfl rfl rfl

theorem g5_pent (a b c d e : Finset ℕ) (ha : a ⊆ {1, 2, 5, 6}) (hb : b ⊆ {1, 4, 5, 6}) (hc : c ⊆ {3, 4, 5, 6}) (hd : d ⊆ {3, 4, 5, 6}) (he : e ⊆ {2, 4, 5, 6}) (ha2 : a.card = 2) (hb2 : b.card = 2) (hc2 : c.card = 2) (hd2 : d.card = 2) (he2 : e.card = 2) (hab : Disjoint a b) (hbc : Disjoint b c) (hcd : Disjoint c d) (hde : Disjoint d e) (hea : Disjoint e a) : False := by
  have key : ∀ x ∈ ({1, 2, 5, 6} : Finset ℕ).powersetCard 2,
      ∀ y ∈ ({1, 4, 5, 6} : Finset ℕ).powersetCard 2, Disjoint x y →
      ∀ z ∈ ({3, 4, 5, 6} : Finset ℕ).powersetCard 2, Disjoint y z →
      ∀ w ∈ ({3, 4, 5, 6} : Finset ℕ).powersetCard 2, Disjoint z w →
      ∀ u ∈ ({2, 4, 5, 6} : Finset ℕ).powersetCard 2, Disjoint w u → Disjoint u x → False := by
    decide
  exact key a (Finset.mem_powersetCard.2 ⟨ha, ha2⟩) b (Finset.mem_powersetCard.2 ⟨hb, hb2⟩) hab
    c (Finset.mem_powersetCard.2 ⟨hc, hc2⟩) hbc d (Finset.mem_powersetCard.2 ⟨hd, hd2⟩) hcd
    e (Finset.mem_powersetCard.2 ⟨he, he2⟩) hde hea

theorem g5tc_sub_sdiff (s A B : Finset ℕ) (h1 : s ⊆ A) (h2 : Disjoint s B) : s ⊆ A \ B := by
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨h1 hx, Finset.disjoint_left.mp h2 hx⟩

theorem g5_two_core (φ : Fin 37 → Finset ℕ) (hφ : IsListSetColoring g5Graph g5List 2 φ) (h33 : φ 33 = {7, 8}) (h36 : φ 36 = {7, 8}) : False := by
  obtain ⟨hL, hD⟩ := hφ
  have adj : ∀ u v : Fin 37, u ≠ v → (u, v) ∈ g5Edges → Disjoint (φ u) (φ v) := by
    intro u v huv hm
    apply hD
    rw [g5Graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl hm⟩
  have d331 := adj 33 1 (by decide) (by decide)
  have d333 := adj 33 3 (by decide) (by decide)
  have d365 := adj 36 5 (by decide) (by decide)
  have d366 := adj 36 6 (by decide) (by decide)
  have d01 := adj 0 1 (by decide) (by decide)
  have d12 := adj 1 2 (by decide) (by decide)
  have d23 := adj 2 3 (by decide) (by decide)
  have d34 := adj 3 4 (by decide) (by decide)
  have d40 := adj 4 0 (by decide) (by decide)
  have d05 := adj 0 5 (by decide) (by decide)
  have d56 := adj 5 6 (by decide) (by decide)
  have d62 := adj 6 2 (by decide) (by decide)
  rw [h33] at d331 d333
  rw [h36] at d365 d366
  have l0 : φ 0 ⊆ ({1, 2, 3, 4, 5, 6} : Finset ℕ) := (hL 0).1
  have l1 : φ 1 ⊆ ({1, 4, 5, 6, 7, 8} : Finset ℕ) := (hL 1).1
  have l2 : φ 2 ⊆ ({1, 2, 3, 4, 5, 6} : Finset ℕ) := (hL 2).1
  have l3 : φ 3 ⊆ ({3, 4, 5, 6, 7, 8} : Finset ℕ) := (hL 3).1
  have s4 : φ 4 ⊆ ({2, 4, 5, 6} : Finset ℕ) := (hL 4).1
  have l5 : φ 5 ⊆ ({1, 2, 3, 4, 7, 8} : Finset ℕ) := (hL 5).1
  have l6 : φ 6 ⊆ ({1, 2, 7, 8} : Finset ℕ) := (hL 6).1
  have s1 : φ 1 ⊆ ({1, 4, 5, 6} : Finset ℕ) :=
    (g5tc_sub_sdiff _ _ _ l1 d331.symm).trans (by decide)
  have s3 : φ 3 ⊆ ({3, 4, 5, 6} : Finset ℕ) :=
    (g5tc_sub_sdiff _ _ _ l3 d333.symm).trans (by decide)
  have s6 : φ 6 ⊆ ({1, 2} : Finset ℕ) :=
    (g5tc_sub_sdiff _ _ _ l6 d366.symm).trans (by decide)
  have h6 : φ 6 = {1, 2} := Finset.eq_of_subset_of_card_le s6 (by rw [(hL 6).2]; decide)
  rw [h6] at d56 d62
  have s5 : φ 5 ⊆ ({3, 4} : Finset ℕ) :=
    (g5tc_sub_sdiff _ _ _ (g5tc_sub_sdiff _ _ _ l5 d365.symm) d56).trans (by decide)
  have h5 : φ 5 = {3, 4} := Finset.eq_of_subset_of_card_le s5 (by rw [(hL 5).2]; decide)
  rw [h5] at d05
  have s0 : φ 0 ⊆ ({1, 2, 5, 6} : Finset ℕ) :=
    (g5tc_sub_sdiff _ _ _ l0 d05).trans (by decide)
  have s2 : φ 2 ⊆ ({3, 4, 5, 6} : Finset ℕ) :=
    (g5tc_sub_sdiff _ _ _ l2 d62.symm).trans (by decide)
  exact g5_pent (φ 0) (φ 1) (φ 2) (φ 3) (φ 4) s0 s1 s2 s3 s4 (hL 0).2 (hL 1).2 (hL 2).2
    (hL 3).2 (hL 4).2 d01 d12 d23 d34 d40

theorem g5_not_two : ¬ ∃ φ : Fin 37 → Finset ℕ, IsListSetColoring g5Graph g5List 2 φ := by
  rintro ⟨φ, hφ⟩
  obtain ⟨h1, h2⟩ := g5_w φ hφ
  exact g5_two_core φ hφ h1 h2

theorem coloring_of_fn {V : Type} (G : SimpleGraph V) (L : V → Finset ℕ) (c : V → ℕ) (hc : ∀ v, c v ∈ L v) (hadj : ∀ u v, G.Adj u v → c u ≠ c v) : ∃ φ : V → Finset ℕ, IsListSetColoring G L 1 φ := by
  refine ⟨fun v => {c v}, fun v => ⟨Finset.singleton_subset_iff.mpr (hc v), Finset.card_singleton _⟩, ?_⟩
  intro u v huv
  exact Finset.disjoint_singleton.mpr (hadj u v huv)

theorem hn_ext2 (A B : Finset ℕ) (hA : 2 ≤ A.card) (hB : B.card = 2) (hne : A ≠ B) (z : ℕ) : ∃ a ∈ A, ∃ b ∈ B, a ≠ z ∧ b ≠ z ∧ a ≠ b := by
  by_cases hz : z ∈ B
  · obtain ⟨b, hb, hbz⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) z
    have hnsub : ¬ A ⊆ B := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
    obtain ⟨a, ha, haB⟩ := Finset.not_subset.1 hnsub
    refine ⟨a, ha, b, hb, ?_, hbz, ?_⟩
    · intro h
      apply haB
      rw [h]
      exact hz
    · intro h
      apply haB
      rw [h]
      exact hb
  · obtain ⟨a, ha, haz⟩ := Finset.exists_mem_ne (by omega : 1 < A.card) z
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) a
    refine ⟨a, ha, b, hb, haz, ?_, Ne.symm hba⟩
    intro h
    apply hz
    rw [← h]
    exact hb

theorem hn_bad (A B : Finset ℕ) (hA : A.card = 3) (hB : B.card = 2) : ∃ k : ℕ, ∀ t : ℕ, A.erase t = B → t = k := by
  by_cases h : ∃ k, A.erase k = B
  · obtain ⟨k, hk⟩ := h
    refine ⟨k, fun t ht => ?_⟩
    by_contra hne
    have htA : t ∈ A := by
      by_contra hn
      rw [Finset.erase_eq_self.2 hn] at ht
      rw [ht] at hA
      omega
    have hmem : t ∈ A.erase k := Finset.mem_erase.2 ⟨hne, htA⟩
    rw [hk, ← ht] at hmem
    simp at hmem
  · push_neg at h
    exact ⟨0, fun t ht => absurd ht (h t)⟩

theorem hn_zc (B C D : Finset ℕ) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 3) : ∃ k : ℕ, (k ∈ B ∧ k ∈ C) ∨ ((k ∈ B ∨ k ∈ C) ∧ k ∉ D) := by
  by_cases h : (B ∩ C).Nonempty
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl (Finset.mem_inter.1 hk)⟩
  · have hd : Disjoint B C :=
      Finset.disjoint_iff_inter_eq_empty.2 (Finset.not_nonempty_iff_eq_empty.1 h)
    have hc : (B ∪ C).card = 4 := by
      rw [Finset.card_union_of_disjoint hd]; omega
    obtain ⟨k, hk, hk'⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (show D.card < (B ∪ C).card by omega)
    exact ⟨k, Or.inr ⟨Finset.mem_union.1 hk, hk'⟩⟩

theorem hn_zback (s k h : ℕ) (B C D E F G : Finset ℕ) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 3) (hE : E.card = 4) (hF : F.card = 3) (hG : G.card = 2) (hk : (k ∈ B ∧ k ∈ C) ∨ ((k ∈ B ∨ k ∈ C) ∧ k ∉ D)) (hks : k ≠ s) : ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D, ∃ e ∈ E, ∃ f ∈ F, ∃ g ∈ G, b ≠ s ∧ c ≠ s ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ e ≠ f ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h := by
  obtain ⟨g, hg, hgh⟩ := Finset.exists_mem_ne (by omega : 1 < G.card) h
  obtain ⟨f, hf, hf'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := F) (s := {g, h})
    (by have := Finset.card_le_two (a := g) (b := h); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hf'
  rcases hk with ⟨hkB, hkC⟩ | ⟨hkBC, hkD⟩
  · obtain ⟨e, he, he'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := E) (s := {k, f})
      (by have := Finset.card_le_two (a := k) (b := f); omega)
    obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := D) (s := {k, e})
      (by have := Finset.card_le_two (a := k) (b := e); omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he' hd'
    exact ⟨k, hkB, k, hkC, d, hd, e, he, f, hf, g, hg, hks, hks, Ne.symm hd'.1, Ne.symm he'.1,
      Ne.symm hd'.1, Ne.symm he'.1, hd'.2, he'.2, hf'.1, hf'.2, hgh⟩
  · rcases hkBC with hkB | hkC
    · obtain ⟨c, hc, hcs⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) s
      obtain ⟨e, he, he'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := E) (s := {k, c, f})
        (by have := Finset.card_le_three (a := k) (b := c) (c := f); omega)
      obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := D) (s := {c, e})
        (by have := Finset.card_le_two (a := c) (b := e); omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he' hd'
      have hkd : k ≠ d := fun hh => hkD (by rw [hh]; exact hd)
      exact ⟨k, hkB, c, hc, d, hd, e, he, f, hf, g, hg, hks, hcs, hkd, Ne.symm he'.1,
        Ne.symm hd'.1, Ne.symm he'.2.1, hd'.2, he'.2.2, hf'.1, hf'.2, hgh⟩
    · obtain ⟨b, hb, hbs⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) s
      obtain ⟨e, he, he'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := E) (s := {k, b, f})
        (by have := Finset.card_le_three (a := k) (b := b) (c := f); omega)
      obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := D) (s := {b, e})
        (by have := Finset.card_le_two (a := b) (b := e); omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he' hd'
      have hkd : k ≠ d := fun hh => hkD (by rw [hh]; exact hd)
      exact ⟨b, hb, k, hkC, d, hd, e, he, f, hf, g, hg, hbs, hks, Ne.symm hd'.1, Ne.symm he'.2.1,
        hkd, Ne.symm he'.1, hd'.2, he'.2.2, hf'.1, hf'.2, hgh⟩

theorem hn_tail (w p q : ℕ) (A1 A2 A3 : Finset ℕ) (h1 : A1.card = 3) (h2 : A2.card = 2) (h3 : A3.card = 3) (hne : A1.erase w ≠ A2) : ∃ a1 ∈ A1, ∃ a2 ∈ A2, ∃ a3 ∈ A3, w ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a1 ≠ a3 ∧ a3 ≠ p ∧ a3 ≠ q := by
  obtain ⟨a3, ha3, ha3'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({p, q} : Finset ℕ)) (t := A3)
    (by have := Finset.card_le_two (a := p) (b := q); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha3'
  have hc : 2 ≤ (A1.erase w).card := by
    have := Finset.pred_card_le_card_erase (s := A1) (a := w)
    omega
  obtain ⟨a1, ha1, a2, ha2, n1, n2, n3⟩ := hn_ext2 (A1.erase w) A2 hc h2 hne a3
  rw [Finset.mem_erase] at ha1
  exact ⟨a1, ha1.2, a2, ha2, a3, ha3, Ne.symm ha1.1, n3, n2, n1, ha3'.1, ha3'.2⟩

theorem hn_head (w3 : ℕ) (Z1 Z2 W1 W2 : Finset ℕ) (h1 : Z1.card = 3) (h2 : Z2.card = 3) (h3 : W1.card = 3) (h4 : W2.card = 2) : ∃ z1 ∈ Z1, ∃ z2 ∈ Z2, ∃ w1 ∈ W1, ∃ w2 ∈ W2, z1 ≠ w1 ∧ z2 ≠ w1 ∧ w1 ≠ w2 ∧ w2 ≠ w3 ∧ w1 ≠ w3 := by
  obtain ⟨w2, hw2, hw2n⟩ := Finset.exists_mem_ne (by omega : 1 < W2.card) w3
  obtain ⟨w1, hw1, hw1n⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({w2, w3} : Finset ℕ)) (t := W1)
    (by have := Finset.card_le_two (a := w2) (b := w3); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw1n
  obtain ⟨z1, hz1, hz1n⟩ := Finset.exists_mem_ne (by omega : 1 < Z1.card) w1
  obtain ⟨z2, hz2, hz2n⟩ := Finset.exists_mem_ne (by omega : 1 < Z2.card) w1
  exact ⟨z1, hz1, z2, hz2, w1, hw1, w2, hw2, hz1n, hz2n, hw1n.1, hw2n, hw1n.2⟩

theorem hn_wback (p q r s : ℕ) (Z1 Z2 W1 W2 W3 A1 A2 A3 B1 B2 B3 : Finset ℕ) (hZ1 : Z1.card = 3) (hZ2 : Z2.card = 3) (hW1 : W1.card = 3) (hW2 : W2.card = 2) (hW3 : W3.card = 3) (hA1 : A1.card = 3) (hA2 : A2.card = 2) (hA3 : A3.card = 3) (hB1 : B1.card = 3) (hB2 : B2.card = 2) (hB3 : B3.card = 3) : ∃ z1 ∈ Z1, ∃ z2 ∈ Z2, ∃ w1 ∈ W1, ∃ w2 ∈ W2, ∃ w3 ∈ W3, ∃ a1 ∈ A1, ∃ a2 ∈ A2, ∃ a3 ∈ A3, ∃ b1 ∈ B1, ∃ b2 ∈ B2, ∃ b3 ∈ B3, z1 ≠ w1 ∧ z2 ≠ w1 ∧ w1 ≠ w2 ∧ w2 ≠ w3 ∧ w1 ≠ w3 ∧ w3 ≠ a1 ∧ w3 ≠ b1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a1 ≠ a3 ∧ b1 ≠ b2 ∧ b2 ≠ b3 ∧ b1 ≠ b3 ∧ a3 ≠ p ∧ a3 ≠ q ∧ b3 ≠ r ∧ b3 ≠ s := by
  have pick : ∀ S T : Finset ℕ, T.card < S.card → ∃ x ∈ S, x ∉ T := fun S T h => by
    obtain ⟨e, he, he'⟩ := Finset.exists_mem_notMem_of_card_lt_card h
    exact ⟨e, he, he'⟩
  have two : ∀ x y : ℕ, ({x, y} : Finset ℕ).card ≤ 2 := fun x y => Finset.card_le_two
  obtain ⟨a3, ha3, ha3'⟩ := pick A3 {p, q} (by have := two p q; omega)
  obtain ⟨a2, ha2, ha2'⟩ := Finset.exists_mem_ne (by omega : 1 < A2.card) a3
  obtain ⟨a1, ha1, ha1'⟩ := pick A1 {a2, a3} (by have := two a2 a3; omega)
  obtain ⟨b3, hb3, hb3'⟩ := pick B3 {r, s} (by have := two r s; omega)
  obtain ⟨b2, hb2, hb2'⟩ := Finset.exists_mem_ne (by omega : 1 < B2.card) b3
  obtain ⟨b1, hb1, hb1'⟩ := pick B1 {b2, b3} (by have := two b2 b3; omega)
  obtain ⟨w3, hw3, hw3'⟩ := pick W3 {a1, b1} (by have := two a1 b1; omega)
  obtain ⟨w2, hw2, hw2'⟩ := Finset.exists_mem_ne (by omega : 1 < W2.card) w3
  obtain ⟨w1, hw1, hw1'⟩ := pick W1 {w2, w3} (by have := two w2 w3; omega)
  obtain ⟨z1, hz1, hz1'⟩ := Finset.exists_mem_ne (by omega : 1 < Z1.card) w1
  obtain ⟨z2, hz2, hz2'⟩ := Finset.exists_mem_ne (by omega : 1 < Z2.card) w1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha3' ha1' hb3' hb1' hw3' hw1'
  exact ⟨z1, hz1, z2, hz2, w1, hw1, w2, hw2, w3, hw3, a1, ha1, a2, ha2, a3, ha3, b1, hb1, b2,
    hb2, b3, hb3, hz1', hz2', hw1'.1, hw2', hw1'.2, hw3'.1, hw3'.2, ha1'.1, ha2', ha1'.2,
    hb1'.1, hb2', hb1'.2, ha3'.1, ha3'.2, hb3'.1, hb3'.2⟩

theorem hn_c5 (A B C D E : Finset ℕ) (hA : 1 < A.card) (hB : 1 < B.card) (hC : 1 < C.card) (hD : 1 < D.card) (hE : 1 < E.card) (h : ∃ t ∈ A, t ∉ B) : ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ∃ w ∈ D, ∃ u ∈ E, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ u ∧ u ≠ x := by
  obtain ⟨t, htA, htB⟩ := h
  obtain ⟨u, hu, hut⟩ := Finset.exists_mem_ne hE t
  obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hD u
  obtain ⟨z, hz, hzw⟩ := Finset.exists_mem_ne hC w
  obtain ⟨y, hy, hyz⟩ := Finset.exists_mem_ne hB z
  have hty : t ≠ y := fun h => htB (by rw [h]; exact hy)
  exact ⟨t, htA, y, hy, z, hz, w, hw, u, hu, hty, hyz, hzw, hwu, hut⟩

theorem hn_cyc_aux (A B C D E : Finset ℕ) (hB : 1 < B.card) (hC : 1 < C.card) (hD : 1 < D.card) (hE : 1 < E.card) (t : ℕ) (ht : t ∈ A) (htB : t ∉ B) : ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ∃ w ∈ D, ∃ u ∈ E, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ u ∧ u ≠ x := by
  obtain ⟨u, hu, hut⟩ := Finset.exists_mem_ne hE t
  obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hD u
  obtain ⟨z, hz, hzw⟩ := Finset.exists_mem_ne hC w
  obtain ⟨y, hy, hyz⟩ := Finset.exists_mem_ne hB z
  have hty : t ≠ y := fun h => htB (by rw [h]; exact hy)
  exact ⟨t, ht, y, hy, z, hz, w, hw, u, hu, hty, hyz, hzw, hwu, hut⟩

theorem hn_cyc (A B C D E : Finset ℕ) (hA : 1 < A.card) (hB : 1 < B.card) (hC : 1 < C.card) (hD : 1 < D.card) (hE : 1 < E.card) (h : ¬(A ⊆ B ∧ B ⊆ C ∧ C ⊆ D ∧ D ⊆ E ∧ E ⊆ A)) : ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ∃ w ∈ D, ∃ u ∈ E, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ u ∧ u ≠ x := by
  by_cases s1 : A ⊆ B
  · by_cases s2 : B ⊆ C
    · by_cases s3 : C ⊆ D
      · by_cases s4 : D ⊆ E
        · by_cases s5 : E ⊆ A
          · exact absurd ⟨s1, s2, s3, s4, s5⟩ h
          · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s5
            obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
              hn_cyc_aux E A B C D hA hB hC hD t ht htn
            exact ⟨y, hy, z, hz, w, hw, u, hu, x, hx, h2, h3, h4, h5, h1⟩
        · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s4
          obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
            hn_cyc_aux D E A B C hE hA hB hC t ht htn
          exact ⟨z, hz, w, hw, u, hu, x, hx, y, hy, h3, h4, h5, h1, h2⟩
      · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s3
        obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
          hn_cyc_aux C D E A B hD hE hA hB t ht htn
        exact ⟨w, hw, u, hu, x, hx, y, hy, z, hz, h4, h5, h1, h2, h3⟩
    · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s2
      obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
        hn_cyc_aux B C D E A hC hD hE hA t ht htn
      exact ⟨u, hu, x, hx, y, hy, z, hz, w, hw, h5, h1, h2, h3, h4⟩
  · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s1
    exact hn_cyc_aux A B C D E hB hC hD hE t ht htn

theorem hn_erase_inj (P Q : Finset ℕ) (hP : P.card = 3) (hQ : Q.card = 3) (y : ℕ) (h : P.erase y = Q.erase y) : P = Q := by
  by_cases hp : y ∈ P <;> by_cases hq : y ∈ Q
  · rw [← Finset.insert_erase hp, ← Finset.insert_erase hq, h]
  · have h1 := Finset.card_erase_of_mem hp
    rw [h, Finset.erase_eq_self.2 hq] at h1
    omega
  · have h1 := Finset.card_erase_of_mem hq
    rw [← h, Finset.erase_eq_self.2 hp] at h1
    omega
  · rw [Finset.erase_eq_self.2 hp, Finset.erase_eq_self.2 hq] at h
    exact h

theorem hn_rim_einj (P Q : Finset ℕ) (hP : P.card = 3) (hQ : Q.card = 3) (y : ℕ) (h : P.erase y = Q.erase y) : P = Q := by
  by_cases hp : y ∈ P <;> by_cases hq : y ∈ Q
  · rw [← Finset.insert_erase hp, ← Finset.insert_erase hq, h]
  · have h1 := Finset.card_erase_of_mem hp
    rw [h, Finset.erase_eq_self.2 hq] at h1
    omega
  · have h1 := Finset.card_erase_of_mem hq
    rw [← h, Finset.erase_eq_self.2 hp] at h1
    omega
  · rwa [Finset.erase_eq_self.2 hp, Finset.erase_eq_self.2 hq] at h

theorem hn_rim (P0 P7 P2 P8 P9 Y Y11 : Finset ℕ) (h0 : P0.card = 3) (h7 : P7.card = 3) (h2 : P2.card = 3) (h8 : P8.card = 3) (h9 : P9.card = 3) (hY : Y.card = 4) (hY11 : Y11.card = 3) (hne : ¬(P0 = P7 ∧ P7 = P2 ∧ P2 = P8 ∧ P8 = P9)) : ∃ y ∈ Y, y ∉ Y11 ∧ ∃ x0 ∈ P0, ∃ x7 ∈ P7, ∃ x2 ∈ P2, ∃ x8 ∈ P8, ∃ x9 ∈ P9, x0 ≠ x7 ∧ x7 ≠ x2 ∧ x2 ≠ x8 ∧ x8 ≠ x9 ∧ x9 ≠ x0 ∧ y ≠ x0 ∧ y ≠ x7 ∧ y ≠ x2 ∧ y ≠ x8 ∧ y ≠ x9 := by
  obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_notMem_of_card_lt_card (show Y11.card < Y.card by omega)
  have c : ∀ P : Finset ℕ, P.card = 3 → 1 < (P.erase y).card := fun P hP => by
    have := Finset.pred_card_le_card_erase (s := P) (a := y)
    omega
  have hch : ¬(P0.erase y ⊆ P7.erase y ∧ P7.erase y ⊆ P2.erase y ∧ P2.erase y ⊆ P8.erase y ∧
      P8.erase y ⊆ P9.erase y ∧ P9.erase y ⊆ P0.erase y) := by
    rintro ⟨s1, s2, s3, s4, s5⟩
    apply hne
    exact ⟨hn_rim_einj _ _ h0 h7 y (Finset.Subset.antisymm s1 (s2.trans (s3.trans (s4.trans s5)))),
      hn_rim_einj _ _ h7 h2 y (Finset.Subset.antisymm s2 (s3.trans (s4.trans (s5.trans s1)))),
      hn_rim_einj _ _ h2 h8 y (Finset.Subset.antisymm s3 (s4.trans (s5.trans (s1.trans s2)))),
      hn_rim_einj _ _ h8 h9 y (Finset.Subset.antisymm s4 (s5.trans (s1.trans (s2.trans s3))))⟩
  obtain ⟨x0, hx0, x7, hx7, x2, hx2, x8, hx8, x9, hx9, n1, n2, n3, n4, n5⟩ :=
    hn_cyc _ _ _ _ _ (c P0 h0) (c P7 h7) (c P2 h2) (c P8 h8) (c P9 h9) hch
  rw [Finset.mem_erase] at hx0 hx7 hx2 hx8 hx9
  exact ⟨y, hy, hy', x0, hx0.2, x7, hx7.2, x2, hx2.2, x8, hx8.2, x9, hx9.2, n1, n2, n3, n4, n5,
    Ne.symm hx0.1, Ne.symm hx7.1, Ne.symm hx2.1, Ne.symm hx8.1, Ne.symm hx9.1⟩

theorem hn_g1fwd (x0 x2 : ℕ) (L1 L3 L4 L5 L6 : Finset ℕ) (h1 : L1.card = 3) (h3 : L3.card = 3) (h4 : L4.card = 2) (h5 : L5.card = 3) (h6 : L6.card = 2) : ∃ x1 ∈ L1, ∃ x3 ∈ L3, ∃ x4 ∈ L4, ∃ x5 ∈ L5, ∃ x6 ∈ L6, x0 ≠ x1 ∧ x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x4 ∧ x4 ≠ x0 ∧ x0 ≠ x5 ∧ x5 ≠ x6 ∧ x6 ≠ x2 := by
  obtain ⟨x1, hx1, hx1'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x0, x2} : Finset ℕ)) (t := L1)
    (by have := Finset.card_le_two (a := x0) (b := x2); omega)
  obtain ⟨x4, hx4, hx4'⟩ := Finset.exists_mem_ne (by omega : 1 < L4.card) x0
  obtain ⟨x3, hx3, hx3'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x2, x4} : Finset ℕ)) (t := L3)
    (by have := Finset.card_le_two (a := x2) (b := x4); omega)
  obtain ⟨x6, hx6, hx6'⟩ := Finset.exists_mem_ne (by omega : 1 < L6.card) x2
  obtain ⟨x5, hx5, hx5'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x0, x6} : Finset ℕ)) (t := L5)
    (by have := Finset.card_le_two (a := x0) (b := x6); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1' hx3' hx5'
  exact ⟨x1, hx1, x3, hx3, x4, hx4, x5, hx5, x6, hx6, Ne.symm hx1'.1, hx1'.2, Ne.symm hx3'.1,
    hx3'.2, hx4', Ne.symm hx5'.1, hx5'.2, hx6'⟩

theorem hlow_cyc_aux (A B C D E : Finset ℕ) (hB : 1 < B.card) (hC : 1 < C.card) (hD : 1 < D.card) (hE : 1 < E.card) (t : ℕ) (ht : t ∈ A) (htB : t ∉ B) : ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ∃ w ∈ D, ∃ u ∈ E, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ u ∧ u ≠ x := by
  obtain ⟨u, hu, hut⟩ := Finset.exists_mem_ne hE t
  obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hD u
  obtain ⟨z, hz, hzw⟩ := Finset.exists_mem_ne hC w
  obtain ⟨y, hy, hyz⟩ := Finset.exists_mem_ne hB z
  have hty : t ≠ y := fun h => htB (by rw [h]; exact hy)
  exact ⟨t, ht, y, hy, z, hz, w, hw, u, hu, hty, hyz, hzw, hwu, hut⟩

theorem hlow_cyc (A B C D E : Finset ℕ) (hA : 1 < A.card) (hB : 1 < B.card) (hC : 1 < C.card) (hD : 1 < D.card) (hE : 1 < E.card) (h : ¬(A ⊆ B ∧ B ⊆ C ∧ C ⊆ D ∧ D ⊆ E ∧ E ⊆ A)) : ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ∃ w ∈ D, ∃ u ∈ E, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ u ∧ u ≠ x := by
  by_cases s1 : A ⊆ B
  · by_cases s2 : B ⊆ C
    · by_cases s3 : C ⊆ D
      · by_cases s4 : D ⊆ E
        · by_cases s5 : E ⊆ A
          · exact absurd ⟨s1, s2, s3, s4, s5⟩ h
          · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s5
            obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
              hlow_cyc_aux E A B C D hA hB hC hD t ht htn
            exact ⟨y, hy, z, hz, w, hw, u, hu, x, hx, h2, h3, h4, h5, h1⟩
        · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s4
          obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
            hlow_cyc_aux D E A B C hE hA hB hC t ht htn
          exact ⟨z, hz, w, hw, u, hu, x, hx, y, hy, h3, h4, h5, h1, h2⟩
      · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s3
        obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
          hlow_cyc_aux C D E A B hD hE hA hB t ht htn
        exact ⟨w, hw, u, hu, x, hx, y, hy, z, hz, h4, h5, h1, h2, h3⟩
    · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s2
      obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, h1, h2, h3, h4, h5⟩ :=
        hlow_cyc_aux B C D E A hC hD hE hA t ht htn
      exact ⟨u, hu, x, hx, y, hy, z, hz, w, hw, h5, h1, h2, h3, h4⟩
  · obtain ⟨t, ht, htn⟩ := Finset.not_subset.1 s1
    exact hlow_cyc_aux A B C D E hB hC hD hE t ht htn

theorem hlow_erase_inj (P Q : Finset ℕ) (hP : P.card = 3) (hQ : Q.card = 3) (y : ℕ) (h : P.erase y = Q.erase y) : P = Q := by
  by_cases hp : y ∈ P <;> by_cases hq : y ∈ Q
  · rw [← Finset.insert_erase hp, ← Finset.insert_erase hq, h]
  · have h1 := Finset.card_erase_of_mem hp
    rw [h, Finset.erase_eq_of_notMem hq] at h1
    omega
  · have h1 := Finset.card_erase_of_mem hq
    rw [← h, Finset.erase_eq_of_notMem hp] at h1
    omega
  · rwa [Finset.erase_eq_of_notMem hp, Finset.erase_eq_of_notMem hq] at h

theorem hn_low (L : Fin 37 → Finset ℕ) (hL : ∀ v, (L v).card = (g5List v).card / 2) (hne : ¬ (L 0 = L 7 ∧ L 7 = L 2 ∧ L 2 = L 8 ∧ L 8 = L 9)) : ∃ y, y ∈ L 10 ∧ y ∉ L 11 ∧ ∃ d : Fin 37 → ℕ, (∀ v : Fin 37, v.val ≤ 9 → d v ∈ L v) ∧ y ≠ d 0 ∧ y ≠ d 7 ∧ y ≠ d 2 ∧ y ≠ d 8 ∧ y ≠ d 9 ∧ ∀ u v : Fin 37, (u, v) ∈ g5Edges → u.val ≤ 9 → v.val ≤ 9 → d u ≠ d v := by
  have c0 : (L 0).card = 3 := by rw [hL]; decide
  have c1 : (L 1).card = 3 := by rw [hL]; decide
  have c2 : (L 2).card = 3 := by rw [hL]; decide
  have c3 : (L 3).card = 3 := by rw [hL]; decide
  have c4 : (L 4).card = 2 := by rw [hL]; decide
  have c5 : (L 5).card = 3 := by rw [hL]; decide
  have c6 : (L 6).card = 2 := by rw [hL]; decide
  have c7 : (L 7).card = 3 := by rw [hL]; decide
  have c8 : (L 8).card = 3 := by rw [hL]; decide
  have c9 : (L 9).card = 3 := by rw [hL]; decide
  have c10 : (L 10).card = 4 := by rw [hL]; decide
  have c11 : (L 11).card = 3 := by rw [hL]; decide
  obtain ⟨y, hy10, hy11⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (L 11).card < (L 10).card by omega)
  have e0 := Finset.pred_card_le_card_erase (s := L 0) (a := y)
  have e7 := Finset.pred_card_le_card_erase (s := L 7) (a := y)
  have e2 := Finset.pred_card_le_card_erase (s := L 2) (a := y)
  have e8 := Finset.pred_card_le_card_erase (s := L 8) (a := y)
  have e9 := Finset.pred_card_le_card_erase (s := L 9) (a := y)
  have hne' : ¬((L 0).erase y ⊆ (L 7).erase y ∧ (L 7).erase y ⊆ (L 2).erase y ∧
      (L 2).erase y ⊆ (L 8).erase y ∧ (L 8).erase y ⊆ (L 9).erase y ∧
      (L 9).erase y ⊆ (L 0).erase y) := by
    rintro ⟨s1, s2, s3, s4, s5⟩
    apply hne
    have q07 := Finset.Subset.antisymm s1 (s2.trans (s3.trans (s4.trans s5)))
    have q72 := Finset.Subset.antisymm s2 (s3.trans (s4.trans (s5.trans s1)))
    have q28 := Finset.Subset.antisymm s3 (s4.trans (s5.trans (s1.trans s2)))
    have q89 := Finset.Subset.antisymm s4 (s5.trans (s1.trans (s2.trans s3)))
    exact ⟨hlow_erase_inj _ _ c0 c7 y q07, hlow_erase_inj _ _ c7 c2 y q72,
      hlow_erase_inj _ _ c2 c8 y q28, hlow_erase_inj _ _ c8 c9 y q89⟩
  obtain ⟨x0, hx0, x7, hx7, x2, hx2, x8, hx8, x9, hx9, n07, n72, n28, n89, n90⟩ :=
    hlow_cyc _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) hne'
  rw [Finset.mem_erase] at hx0 hx7 hx2 hx8 hx9
  obtain ⟨x1, hx1, hx1'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := L 1) (s := {x0, x2})
    (by have := Finset.card_le_two (a := x0) (b := x2); omega)
  obtain ⟨x4, hx4, n40⟩ := Finset.exists_mem_ne (by omega : 1 < (L 4).card) x0
  obtain ⟨x3, hx3, hx3'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := L 3) (s := {x2, x4})
    (by have := Finset.card_le_two (a := x2) (b := x4); omega)
  obtain ⟨x6, hx6, n62⟩ := Finset.exists_mem_ne (by omega : 1 < (L 6).card) x2
  obtain ⟨x5, hx5, hx5'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := L 5) (s := {x0, x6})
    (by have := Finset.card_le_two (a := x0) (b := x6); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1' hx3' hx5'
  have n01 : x0 ≠ x1 := Ne.symm hx1'.1
  have n12 : x1 ≠ x2 := hx1'.2
  have n23 : x2 ≠ x3 := Ne.symm hx3'.1
  have n34 : x3 ≠ x4 := hx3'.2
  have n05 : x0 ≠ x5 := Ne.symm hx5'.1
  have n56 : x5 ≠ x6 := hx5'.2
  have m0 := hx0.2
  have m2 := hx2.2
  have m7 := hx7.2
  have m8 := hx8.2
  have m9 := hx9.2
  refine ⟨y, hy10, hy11, fun v => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD v.val 0, ?_,
    Ne.symm hx0.1, Ne.symm hx7.1, Ne.symm hx2.1, Ne.symm hx8.1, Ne.symm hx9.1, ?_⟩
  · intro v hv
    fin_cases v
    all_goals first
      | exact m0 | exact hx1 | exact m2 | exact hx3 | exact hx4 | exact hx5 | exact hx6
      | exact m7 | exact m8 | exact m9 | exact absurd hv (by decide)
  · intro u v huv hu hv
    fin_cases u
    all_goals first | exact absurd hu (by decide) | skip
    all_goals fin_cases v
    all_goals first
      | exact absurd hv (by decide)
      | exact n01 | exact n12 | exact n23 | exact n34 | exact n40 | exact n05 | exact n56
      | exact n62 | exact n07 | exact n72 | exact n28 | exact n89 | exact n90
      | exact absurd huv (by decide)

theorem hn_gadget (L : Fin 37 → Finset ℕ) (hL : ∀ v, (L v).card = (g5List v).card / 2) (y : ℕ) (hy10 : y ∈ L 10) (hy11 : y ∉ L 11) (p q r s : ℕ) : ∃ c : Fin 37 → ℕ, c 10 = y ∧ (∀ v : Fin 37, 10 ≤ v.val → c v ∈ L v) ∧ c 33 ≠ p ∧ c 33 ≠ q ∧ c 36 ≠ r ∧ c 36 ≠ s ∧ ∀ u v : Fin 37, (u, v) ∈ g5Edges → 10 ≤ u.val → 10 ≤ v.val → c u ≠ c v := by
  have k11 : (L 11).card = 3 := by rw [hL]; decide
  have k12 : (L 12).card = 2 := by rw [hL]; decide
  have k13 : (L 13).card = 3 := by rw [hL]; decide
  obtain ⟨x20, h20, x27, h27, x28, h28, x29, h29, x30, h30, x31, h31, x32, h32, x33, h33,
      x34, h34, x35, h35, x36, h36, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13,
      t14, t15, t16, t17⟩ :=
    hn_wback p q r s (L 20) (L 27) (L 28) (L 29) (L 30) (L 31) (L 32) (L 33) (L 34) (L 35)
      (L 36) (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide)
  obtain ⟨k1, hk1⟩ := hn_zc (L 14) (L 15) (L 16) (by rw [hL]; decide) (by rw [hL]; decide)
    (by rw [hL]; decide)
  obtain ⟨k2, hk2⟩ := hn_zc (L 21) (L 22) (L 23) (by rw [hL]; decide) (by rw [hL]; decide)
    (by rw [hL]; decide)
  obtain ⟨x13, h13, h13'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := L 13)
    (s := {k1, k2}) (by have := Finset.card_le_two (a := k1) (b := k2); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h13'
  obtain ⟨m131, m132⟩ := h13'
  obtain ⟨x14, h14, x15, h15, x16, h16, x17, h17, x18, h18, x19, h19,
      a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hn_zback x13 k1 x20 (L 14) (L 15) (L 16) (L 17) (L 18) (L 19) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) hk1 (Ne.symm m131)
  obtain ⟨x21, h21, x22, h22, x23, h23, x24, h24, x25, h25, x26, h26,
      b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ :=
    hn_zback x13 k2 x27 (L 21) (L 22) (L 23) (L 24) (L 25) (L 26) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) hk2 (Ne.symm m132)
  obtain ⟨x12, h12, n1213⟩ := Finset.exists_mem_ne (by omega : 1 < (L 12).card) x13
  obtain ⟨x11, h11, h11'⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := L 11)
    (s := {x12, x13}) (by have := Finset.card_le_two (a := x12) (b := x13); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h11'
  obtain ⟨n1112, n1113⟩ := h11'
  have n1011 : y ≠ x11 := fun h => hy11 (h ▸ h11)
  refine ⟨fun v => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, y, x11, x12, x13, x14, x15, x16, x17, x18,
    x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35,
    x36].getD v.val 0, rfl, ?_, t14, t15, t16, t17, ?_⟩
  · intro v hv
    obtain ⟨n, hn⟩ := v
    change 10 ≤ n at hv
    interval_cases n <;> assumption
  · intro u v huv hu hv
    simp only [g5Edges, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    all_goals first
      | exact absurd hu (by decide)
      | exact absurd hv (by decide)
      | assumption
      | exact Ne.symm (by assumption)

theorem hn_glue (L : Fin 37 → Finset ℕ) (c d : Fin 37 → ℕ) (hcm : ∀ v : Fin 37, 10 ≤ v.val → c v ∈ L v) (hdm : ∀ v : Fin 37, v.val ≤ 9 → d v ∈ L v) (hce : ∀ u v : Fin 37, (u, v) ∈ g5Edges → 10 ≤ u.val → 10 ≤ v.val → c u ≠ c v) (hde : ∀ u v : Fin 37, (u, v) ∈ g5Edges → u.val ≤ 9 → v.val ≤ 9 → d u ≠ d v) (x0 : c 10 ≠ d 0) (x7 : c 10 ≠ d 7) (x2 : c 10 ≠ d 2) (x8 : c 10 ≠ d 8) (x9 : c 10 ≠ d 9) (y1 : c 33 ≠ d 1) (y3 : c 33 ≠ d 3) (y5 : c 36 ≠ d 5) (y6 : c 36 ≠ d 6) : ∃ φ : Fin 37 → Finset ℕ, IsListSetColoring g5Graph L 1 φ := by
  have key : ∀ u v : Fin 37, (u, v) ∈ g5Edges →
      (if u.val ≤ 9 then d u else c u) ≠ (if v.val ≤ 9 then d v else c v) := by
    intro u v h
    by_cases h1 : u.val ≤ 9 <;> by_cases h2 : v.val ≤ 9
    · rw [if_pos h1, if_pos h2]
      exact hde u v h h1 h2
    · rw [if_pos h1, if_neg h2]
      exfalso
      simp only [g5Edges, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (revert h1 h2; decide)
    · rw [if_neg h1, if_pos h2]
      simp only [g5Edges, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | assumption
        | (exfalso; revert h1 h2; decide)
    · rw [if_neg h1, if_neg h2]
      exact hce u v h (by omega) (by omega)
  refine coloring_of_fn g5Graph L (fun v => if v.val ≤ 9 then d v else c v) ?_ ?_
  · intro v
    by_cases h : v.val ≤ 9
    · simp only [if_pos h]
      exact hdm v h
    · simp only [if_neg h]
      exact hcm v (by omega)
  · intro u v huv
    rw [g5Graph, SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with h | h
    · exact key u v h
    · exact (key v u h).symm

theorem g5_half_noneq (L : Fin 37 → Finset ℕ) (hL : ∀ v, (L v).card = (g5List v).card / 2) (hne : ¬ (L 0 = L 7 ∧ L 7 = L 2 ∧ L 2 = L 8 ∧ L 8 = L 9)) : ∃ φ : Fin 37 → Finset ℕ, IsListSetColoring g5Graph L 1 φ := by
  obtain ⟨y, hy10, hy11, d, hdm, n0, n7, n2, n8, n9, hde⟩ := hn_low L hL hne
  obtain ⟨c, hc10, hcm, a1, a3, b5, b6, hce⟩ :=
    hn_gadget L hL y hy10 hy11 (d 1) (d 3) (d 5) (d 6)
  exact hn_glue L c d hcm hdm hce hde (by rw [hc10]; exact n0) (by rw [hc10]; exact n7)
    (by rw [hc10]; exact n2) (by rw [hc10]; exact n8) (by rw [hc10]; exact n9) a1 a3 b5 b6

theorem heq_pick (S T : Finset ℕ) (h : T.card < S.card) : ∃ x ∈ S, x ∉ T := by
  obtain ⟨e, he, he'⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨e, he, he'⟩

theorem heq_pent (A B C D E : Finset ℕ) (hA : 1 < A.card) (hB : 1 < B.card) (hC : 1 < C.card) (hD : 1 < D.card) (hE : 1 < E.card) (hBAC : B.card < (A ∪ C).card) : ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ∃ w ∈ D, ∃ u ∈ E, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ u ∧ u ≠ x := by
  obtain ⟨t, ht, htB⟩ := heq_pick (A ∪ C) B hBAC
  rcases Finset.mem_union.1 ht with htA | htC
  · obtain ⟨u, hu, hux⟩ := Finset.exists_mem_ne hE t
    obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hD u
    obtain ⟨z, hz, hzw⟩ := Finset.exists_mem_ne hC w
    obtain ⟨y, hy, hyz⟩ := Finset.exists_mem_ne hB z
    have hty : t ≠ y := fun h => htB (by rw [h]; exact hy)
    exact ⟨t, htA, y, hy, z, hz, w, hw, u, hu, hty, hyz, hzw, hwu, hux⟩
  · obtain ⟨w, hw, hwz⟩ := Finset.exists_mem_ne hD t
    obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne hE w
    obtain ⟨x, hx, hxu⟩ := Finset.exists_mem_ne hA u
    obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne hB x
    have hyt : y ≠ t := fun h => htB (by rw [← h]; exact hy)
    exact ⟨x, hx, y, hy, t, htC, w, hw, u, hu, Ne.symm hyx, hyt, Ne.symm hwz, Ne.symm huw,
      Ne.symm hxu⟩

theorem heq_tri (A B C : Finset ℕ) (hA : A.card = 3) (hB : B.card = 2) (hC : C.card = 3) (p q : ℕ) : ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a ≠ p ∧ a ≠ q ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  obtain ⟨a, ha, ha'⟩ := heq_pick A {p, q} (by have := Finset.card_le_two (a := p) (b := q); omega)
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) a
  obtain ⟨c, hc, hc'⟩ := heq_pick C {a, b} (by have := Finset.card_le_two (a := a) (b := b); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha' hc'
  exact ⟨a, ha, b, hb, c, hc, ha'.1, ha'.2, Ne.symm hba, Ne.symm hc'.2, Ne.symm hc'.1⟩

theorem heq_zchain (s : ℕ) (B C D E F G H : Finset ℕ) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 3) (hE : E.card = 4) (hF : F.card = 3) (hG : G.card = 2) (hH : H.card = 3) : ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D, ∃ e ∈ E, ∃ f ∈ F, ∃ g ∈ G, ∃ h ∈ H, b ≠ s ∧ c ≠ s ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ e ≠ f ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h := by
  obtain ⟨b, hb, hbs⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) s
  obtain ⟨c, hc, hcs⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) s
  obtain ⟨d, hd, hd'⟩ := heq_pick D {b, c} (by have := Finset.card_le_two (a := b) (b := c); omega)
  obtain ⟨e, he, he'⟩ := heq_pick E {b, c, d} (by have := Finset.card_le_three (a := b) (b := c) (c := d); omega)
  obtain ⟨f, hf, hf'⟩ := heq_pick F {e} (by rw [Finset.card_singleton]; omega)
  obtain ⟨g, hg, hgf⟩ := Finset.exists_mem_ne (by omega : 1 < G.card) f
  obtain ⟨h, hh, hh'⟩ := heq_pick H {f, g} (by have := Finset.card_le_two (a := f) (b := g); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd' he' hf' hh'
  exact ⟨b, hb, c, hc, d, hd, e, he, f, hf, g, hg, h, hh, hbs, hcs, Ne.symm hd'.1,
    Ne.symm he'.1, Ne.symm hd'.2, Ne.symm he'.2.1, Ne.symm he'.2.2, Ne.symm hf',
    Ne.symm hgf, Ne.symm hh'.1, Ne.symm hh'.2⟩

theorem heq_g1_vals (L : Fin 37 → Finset ℕ) (hL : ∀ v, (L v).card = (g5List v).card / 2) (a b : ℕ) : ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℕ, x0 ∈ L 0 ∧ x1 ∈ L 1 ∧ x2 ∈ L 0 ∧ x3 ∈ L 3 ∧ x4 ∈ L 4 ∧ x5 ∈ L 5 ∧ x6 ∈ L 6 ∧ x7 ∈ L 0 ∧ x8 ∈ L 0 ∧ x9 ∈ L 0 ∧ x1 ≠ a ∧ x3 ≠ a ∧ x5 ≠ b ∧ x6 ≠ b ∧ x0 ≠ x1 ∧ x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x4 ∧ x4 ≠ x0 ∧ x0 ≠ x5 ∧ x5 ≠ x6 ∧ x6 ≠ x2 ∧ x0 ≠ x7 ∧ x7 ≠ x2 ∧ x2 ≠ x8 ∧ x8 ≠ x9 ∧ x9 ≠ x0 := by
  have c0 : (L 0).card = 3 := by rw [hL]; decide
  have c1 : (L 1).card = 3 := by rw [hL]; decide
  have c3 : (L 3).card = 3 := by rw [hL]; decide
  have c4 : (L 4).card = 2 := by rw [hL]; decide
  have c5 : (L 5).card = 3 := by rw [hL]; decide
  have c6 : (L 6).card = 2 := by rw [hL]; decide
  obtain ⟨x6, h6, h6b⟩ := Finset.exists_mem_ne (by omega : 1 < (L 6).card) b
  obtain ⟨x5, h5, h5'⟩ := heq_pick (L 5) {b, x6}
    (by have := Finset.card_le_two (a := b) (b := x6); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h5'
  have hA := Finset.pred_card_le_card_erase (s := L 0) (a := x5)
  have hC := Finset.pred_card_le_card_erase (s := L 0) (a := x6)
  have h1e := Finset.pred_card_le_card_erase (s := L 1) (a := a)
  have h3e := Finset.pred_card_le_card_erase (s := L 3) (a := a)
  obtain ⟨B, hBs, hB2⟩ := Finset.exists_subset_card_eq (s := (L 1).erase a) (n := 2) (by omega)
  obtain ⟨D, hDs, hD2⟩ := Finset.exists_subset_card_eq (s := (L 3).erase a) (n := 2) (by omega)
  have hsub : L 0 ⊆ (L 0).erase x5 ∪ (L 0).erase x6 := by
    intro y hy
    rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
    by_cases hy5 : y = x5
    · right
      exact ⟨fun h => h5'.2 (hy5.symm.trans h), hy⟩
    · left
      exact ⟨hy5, hy⟩
  have hU := Finset.card_le_card hsub
  obtain ⟨x0, hx0, x1, hx1, x2, hx2, x3, hx3, x4, hx4, n01, n12, n23, n34, n40⟩ :=
    heq_pent ((L 0).erase x5) B ((L 0).erase x6) D (L 4) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  rw [Finset.mem_erase] at hx0 hx2
  have hx1' := Finset.mem_erase.1 (hBs hx1)
  have hx3' := Finset.mem_erase.1 (hDs hx3)
  obtain ⟨x7, h7, h7'⟩ := heq_pick (L 0) {x0, x2}
    (by have := Finset.card_le_two (a := x0) (b := x2); omega)
  obtain ⟨x8, h8, h8'⟩ := Finset.exists_mem_ne (by omega : 1 < (L 0).card) x2
  obtain ⟨x9, h9, h9'⟩ := heq_pick (L 0) {x8, x0}
    (by have := Finset.card_le_two (a := x8) (b := x0); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h7' h9'
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, hx0.2, hx1'.2, hx2.2, hx3'.2, hx4, h5, h6,
    h7, h8, h9, hx1'.1, hx3'.1, h5'.1, h6b, n01, n12, n23, n34, n40, hx0.1, h5'.2,
    Ne.symm hx2.1, Ne.symm h7'.1, h7'.2, Ne.symm h8', Ne.symm h9'.1, h9'.2⟩

theorem heq_g1 (L : Fin 37 → Finset ℕ) (hL : ∀ v, (L v).card = (g5List v).card / 2) (h07 : L 0 = L 7) (h72 : L 7 = L 2) (h28 : L 2 = L 8) (h89 : L 8 = L 9) (a b : ℕ) : ∃ d : Fin 37 → ℕ, (∀ v : Fin 37, v.val ≤ 9 → d v ∈ L v) ∧ d 0 ∈ L 0 ∧ d 7 ∈ L 0 ∧ d 2 ∈ L 0 ∧ d 8 ∈ L 0 ∧ d 9 ∈ L 0 ∧ d 1 ≠ a ∧ d 3 ≠ a ∧ d 5 ≠ b ∧ d 6 ≠ b ∧ ∀ u v : Fin 37, (u, v) ∈ g5Edges → u.val ≤ 9 → v.val ≤ 9 → d u ≠ d v := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9,
    a1, a3, b5, b6, n01, n12, n23, n34, n40, n05, n56, n62, n07, n72, n28, n89, n90⟩ :=
    heq_g1_vals L hL a b
  have m2' : x2 ∈ L 2 := by rw [← h72, ← h07]; exact m2
  have m7' : x7 ∈ L 7 := by rw [← h07]; exact m7
  have m8' : x8 ∈ L 8 := by rw [← h28, ← h72, ← h07]; exact m8
  have m9' : x9 ∈ L 9 := by rw [← h89, ← h28, ← h72, ← h07]; exact m9
  refine ⟨fun v => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD v.val 0, ?_, m0, m7, m2, m8,
    m9, a1, a3, b5, b6, ?_⟩
  · intro v hv
    fin_cases v
    all_goals first
      | exact m0 | exact m1 | exact m2' | exact m3 | exact m4 | exact m5 | exact m6
      | exact m7' | exact m8' | exact m9' | exact absurd hv (by decide)
  · intro u v huv hu hv
    fin_cases u
    all_goals first | exact absurd hu (by decide) | skip
    all_goals fin_cases v
    all_goals first
      | exact absurd hv (by decide)
      | exact n01 | exact n12 | exact n23 | exact n34 | exact n40 | exact n05 | exact n56
      | exact n62 | exact n07 | exact n72 | exact n28 | exact n89 | exact n90
      | exact absurd huv (by decide)

theorem heq_gadget (L : Fin 37 → Finset ℕ) (hL : ∀ v, (L v).card = (g5List v).card / 2) : ∃ c : Fin 37 → ℕ, (∀ v : Fin 37, 10 ≤ v.val → c v ∈ L v) ∧ c 10 ∉ L 0 ∧ ∀ u v : Fin 37, (u, v) ∈ g5Edges → 10 ≤ u.val → 10 ≤ v.val → c u ≠ c v := by
  have k0 : (L 0).card = 3 := by rw [hL]; decide
  have k10 : (L 10).card = 4 := by rw [hL]; decide
  have k11 : (L 11).card = 3 := by rw [hL]; decide
  have k12 : (L 12).card = 2 := by rw [hL]; decide
  have k13 : (L 13).card = 3 := by rw [hL]; decide
  obtain ⟨x10, h10, h10n⟩ := heq_pick (L 10) (L 0) (by omega)
  obtain ⟨x12, h12⟩ := Finset.card_pos.1 (by omega : 0 < (L 12).card)
  obtain ⟨x11, h11, h11'⟩ := heq_pick (L 11) {x10, x12}
    (by have := Finset.card_le_two (a := x10) (b := x12); omega)
  obtain ⟨x13, h13, h13'⟩ := heq_pick (L 13) {x11, x12}
    (by have := Finset.card_le_two (a := x11) (b := x12); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h11' h13'
  obtain ⟨n1110, n1112⟩ := h11'
  obtain ⟨n1311, n1312⟩ := h13'
  obtain ⟨x14, h14, x15, h15, x16, h16, x17, h17, x18, h18, x19, h19, x20, h20,
      a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    heq_zchain x13 (L 14) (L 15) (L 16) (L 17) (L 18) (L 19) (L 20) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide)
  obtain ⟨x21, h21, x22, h22, x23, h23, x24, h24, x25, h25, x26, h26, x27, h27,
      b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ :=
    heq_zchain x13 (L 21) (L 22) (L 23) (L 24) (L 25) (L 26) (L 27) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) (by rw [hL]; decide)
  obtain ⟨x28, h28, x29, h29, x30, h30, t1, t2, t3, t4, t5⟩ :=
    heq_tri (L 28) (L 29) (L 30) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) x20 x27
  obtain ⟨x31, h31, x32, h32, x33, h33, u1, u2, u3, u4, u5⟩ :=
    heq_tri (L 31) (L 32) (L 33) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) x30 x30
  obtain ⟨x34, h34, x35, h35, x36, h36, w1, w2, w3, w4, w5⟩ :=
    heq_tri (L 34) (L 35) (L 36) (by rw [hL]; decide) (by rw [hL]; decide)
      (by rw [hL]; decide) x30 x30
  refine ⟨fun v => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x10, x11, x12, x13, x14, x15, x16, x17, x18,
    x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35,
    x36].getD v.val 0, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨n, hn⟩ := v
    change 10 ≤ n at hv
    interval_cases n <;> assumption
  · exact h10n
  · intro u v huv hu hv
    simp only [g5Edges, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    all_goals first
      | exact absurd hu (by decide)
      | exact absurd hv (by decide)
      | assumption
      | exact Ne.symm (by assumption)

theorem heq_glue (L : Fin 37 → Finset ℕ) (c d : Fin 37 → ℕ) (hcm : ∀ v : Fin 37, 10 ≤ v.val → c v ∈ L v) (hdm : ∀ v : Fin 37, v.val ≤ 9 → d v ∈ L v) (hce : ∀ u v : Fin 37, (u, v) ∈ g5Edges → 10 ≤ u.val → 10 ≤ v.val → c u ≠ c v) (hde : ∀ u v : Fin 37, (u, v) ∈ g5Edges → u.val ≤ 9 → v.val ≤ 9 → d u ≠ d v) (x0 : c 10 ≠ d 0) (x7 : c 10 ≠ d 7) (x2 : c 10 ≠ d 2) (x8 : c 10 ≠ d 8) (x9 : c 10 ≠ d 9) (y1 : c 33 ≠ d 1) (y3 : c 33 ≠ d 3) (y5 : c 36 ≠ d 5) (y6 : c 36 ≠ d 6) : ∃ φ : Fin 37 → Finset ℕ, IsListSetColoring g5Graph L 1 φ := by
  have key : ∀ u v : Fin 37, (u, v) ∈ g5Edges →
      (if u.val ≤ 9 then d u else c u) ≠ (if v.val ≤ 9 then d v else c v) := by
    intro u v h
    by_cases h1 : u.val ≤ 9 <;> by_cases h2 : v.val ≤ 9
    · rw [if_pos h1, if_pos h2]
      exact hde u v h h1 h2
    · rw [if_pos h1, if_neg h2]
      exfalso
      simp only [g5Edges, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (revert h1 h2; decide)
    · rw [if_neg h1, if_pos h2]
      simp only [g5Edges, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | assumption
        | (exfalso; revert h1 h2; decide)
    · rw [if_neg h1, if_neg h2]
      exact hce u v h (by omega) (by omega)
  refine coloring_of_fn g5Graph L (fun v => if v.val ≤ 9 then d v else c v) ?_ ?_
  · intro v
    by_cases h : v.val ≤ 9
    · simp only [if_pos h]
      exact hdm v h
    · simp only [if_neg h]
      exact hcm v (by omega)
  · intro u v huv
    rw [g5Graph, SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with h | h
    · exact key u v h
    · exact (key v u h).symm

theorem g5_half_eq (L : Fin 37 → Finset ℕ) (hL : ∀ v, (L v).card = (g5List v).card / 2) (h07 : L 0 = L 7) (h72 : L 7 = L 2) (h28 : L 2 = L 8) (h89 : L 8 = L 9) : ∃ φ : Fin 37 → Finset ℕ, IsListSetColoring g5Graph L 1 φ := by
  obtain ⟨c, hcm, hc10, hce⟩ := heq_gadget L hL
  obtain ⟨d, hdm, h0, h7, h2, h8, h9, ha1, ha3, hb5, hb6, hde⟩ :=
    heq_g1 L hL h07 h72 h28 h89 (c 33) (c 36)
  have ne : ∀ y, y ∈ L 0 → c 10 ≠ y := fun y hy h => hc10 (h ▸ hy)
  exact heq_glue L c d hcm hdm hce hde (ne _ h0) (ne _ h7) (ne _ h2) (ne _ h8) (ne _ h9)
    (Ne.symm ha1) (Ne.symm ha3) (Ne.symm hb5) (Ne.symm hb6)

theorem g5_half : ∀ L : Fin 37 → Finset ℕ, (∀ v, (L v).card = (g5List v).card / 2) → ∃ φ : Fin 37 → Finset ℕ, IsListSetColoring g5Graph L 1 φ := by
  intro L hL
  by_cases h : (L 0 = L 7 ∧ L 7 = L 2 ∧ L 2 = L 8 ∧ L 8 = L 9)
  · exact g5_half_eq L hL h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact g5_half_noneq L hL h

theorem uni_list_card {W : Type} (L5 : W → Finset ℕ) : ∀ a, (uniList L5 a).card = 8 := by
  intro a
  cases a with
  | inl i => simp [uniList]
  | inr p =>
    simp only [uniList]
    split_ifs with h
    · exact h
    · simp

theorem fin4_filter_lt_card (m : ℕ) (hm : m ≤ 4) : (Finset.univ.filter (fun i : Fin 4 => i.val < m)).card = m := by
  interval_cases m <;> decide

theorem uni_intended_card {W : Type} (L5 : W → Finset ℕ) (hsub : ∀ v, L5 v ⊆ Finset.range 9) (hcard : ∀ v, (L5 v).card % 2 = 0 ∧ (L5 v).card ≤ 8) (f : Fin 4 → Finset (Fin 8)) (hf2 : ∀ i, (f i).card = 2) (hfd : ∀ i j, i ≠ j → Disjoint (f i) (f j)) (v : W) : (uniIntended L5 (f, v)).card = 8 := by
  unfold uniIntended
  have hinj : Function.Injective (fun x : Fin 8 => x.val + 9) := by
    intro a b h
    exact Fin.ext (by simpa using h)
  have hdisj : Disjoint (L5 v) ((Finset.univ.filter (fun i : Fin 4 => i.val < 4 - (L5 v).card / 2)).biUnion (fun i => (f i).image (fun x : Fin 8 => x.val + 9))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have := hsub v ha
    rw [Finset.mem_range] at this
    rw [Finset.mem_biUnion] at hb
    obtain ⟨i, _, hi⟩ := hb
    rw [Finset.mem_image] at hi
    obtain ⟨x, _, rfl⟩ := hi
    omega
  show (L5 v ∪ (Finset.univ.filter (fun i : Fin 4 => i.val < 4 - (L5 v).card / 2)).biUnion (fun i => (f i).image (fun x : Fin 8 => x.val + 9))).card = 8
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_biUnion]
  · have hc : ∀ i, ((f i).image (fun x : Fin 8 => x.val + 9)).card = 2 := by
      intro i
      rw [Finset.card_image_of_injective _ hinj, hf2]
    simp only [hc, Finset.sum_const, smul_eq_mul]
    obtain ⟨h1, h2⟩ := hcard v
    rw [fin4_filter_lt_card _ (by omega)]
    omega
  · intro i _ j _ hij
    exact (Finset.disjoint_image hinj).mpr (hfd i j hij)

theorem uni_not_coloring {W : Type} (H : SimpleGraph W) (L5 : W → Finset ℕ) (hsub : ∀ v, L5 v ⊆ Finset.range 9) (hcard : ∀ v, (L5 v).card % 2 = 0 ∧ (L5 v).card ≤ 8) (hnot : ¬ ∃ φ : W → Finset ℕ, IsListSetColoring H L5 2 φ) : ¬ ∃ φ, IsListSetColoring (uniGraph H L5) (uniList L5) 2 φ := by
  rintro ⟨φ, hφ⟩
  have hinj : Function.Injective (fun k : Fin 8 => k.val + 9) := by
    intro a b h
    simp only at h
    exact Fin.ext (by omega)
  have hadj : ∀ a b, uniRel H L5 a b → a ≠ b → Disjoint (φ a) (φ b) := by
    intro a b hr hne
    exact hφ.2 a b ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl hr⟩)
  obtain ⟨f, hfdef⟩ : ∃ f : Fin 4 → Finset (Fin 8),
      f = fun i => Finset.univ.filter (fun k : Fin 8 => k.val + 9 ∈ φ (Sum.inl i)) := ⟨_, rfl⟩
  have himg : ∀ i, (f i).image (fun k : Fin 8 => k.val + 9) = φ (Sum.inl i) := by
    intro i
    ext x
    simp only [hfdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hx
      have h1 := (hφ.1 (Sum.inl i)).1 hx
      have h2 : x ∈ Finset.Icc 9 16 := h1
      rw [Finset.mem_Icc] at h2
      refine ⟨⟨x - 9, by omega⟩, ?_, ?_⟩
      · show x - 9 + 9 ∈ φ (Sum.inl i)
        rwa [Nat.sub_add_cancel h2.1]
      · show x - 9 + 9 = x
        omega
  have hf2 : ∀ i, (f i).card = 2 := by
    intro i
    rw [← Finset.card_image_of_injective (f i) hinj, himg i]
    exact (hφ.1 _).2
  have hfd : ∀ i j, i ≠ j → Disjoint (f i) (f j) := by
    intro i j hij
    rw [← Finset.disjoint_image hinj, himg i, himg j]
    exact hadj _ _ hij (fun h => hij (Sum.inl_injective h))
  apply hnot
  refine ⟨fun v => φ (Sum.inr (f, v)), ⟨fun v => ⟨?_, (hφ.1 _).2⟩, ?_⟩⟩
  · intro x hx
    have h1 := (hφ.1 (Sum.inr (f, v))).1 hx
    have h2 : uniList L5 (Sum.inr (f, v)) = uniIntended L5 (f, v) := by
      show (if (uniIntended L5 (f, v)).card = 8 then uniIntended L5 (f, v) else Finset.range 8) = _
      rw [if_pos (uni_intended_card L5 hsub hcard f hf2 hfd v)]
    rw [h2] at h1
    simp only [uniIntended, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at h1
    rcases h1 with h | ⟨i, hi, hx'⟩
    · exact h
    · rw [himg i] at hx'
      exact absurd hx (Finset.disjoint_left.1
        (hadj (Sum.inl i) (Sum.inr (f, v)) hi Sum.inl_ne_inr) hx')
  · intro u w huw
    exact hadj (Sum.inr (f, u)) (Sum.inr (f, w)) ⟨rfl, huw⟩
      (fun h => H.ne_of_adj huw (congrArg Prod.snd (Sum.inr_injective h)))

theorem uni_not_choosable {W : Type} (H : SimpleGraph W) (L5 : W → Finset ℕ) (hsub : ∀ v, L5 v ⊆ Finset.range 9) (hcard : ∀ v, (L5 v).card % 2 = 0 ∧ (L5 v).card ≤ 8) (hnot : ¬ ∃ φ : W → Finset ℕ, IsListSetColoring H L5 2 φ) : ¬ IsChoosable (uniGraph H L5) 8 2 := fun h => uni_not_coloring H L5 hsub hcard hnot (h (uniList L5) (uni_list_card L5))

theorem hub_avoid (S T : Finset ℕ) (hS : S.card = 4) (hT : T.card ≤ 3) : ∃ x ∈ S, x ∉ T := by
  by_contra h
  push_neg at h
  have := Finset.card_le_card (show S ⊆ T from h)
  omega

theorem hub_color (L : Fin 4 → Finset ℕ) (hL : ∀ i, (L i).card = 4) : ∃ c : Fin 4 → ℕ, (∀ i, c i ∈ L i) ∧ ∀ i j, i ≠ j → c i ≠ c j := by
  obtain ⟨a, ha, -⟩ := hub_avoid (L 0) ∅ (hL 0) (by simp)
  obtain ⟨b, hb, hb'⟩ := hub_avoid (L 1) {a} (hL 1) (by simp)
  obtain ⟨c, hc, hc'⟩ := hub_avoid (L 2) {a, b} (hL 2) (Finset.card_le_two.trans (by norm_num))
  obtain ⟨d, hd, hd'⟩ := hub_avoid (L 3) {a, b, c} (hL 3) Finset.card_le_three
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb' hc' hd'
  refine ⟨![a, b, c, d], ?_, ?_⟩
  · intro i
    fin_cases i <;> simpa
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega

theorem uni_avoid (A B : Finset ℕ) (hA : A.card = 4) (hB : B.card ≤ 3) : ∃ x, x ∈ A ∧ x ∉ B := by
  have h := Finset.le_card_sdiff B A
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (show 0 < (A \ B).card by omega)
  exact ⟨x, (Finset.mem_sdiff.1 hx).1, (Finset.mem_sdiff.1 hx).2⟩

theorem uni_hub (L : Fin 4 → Finset ℕ) (hL : ∀ i, (L i).card = 4) : ∃ c : Fin 4 → ℕ, (∀ i, c i ∈ L i) ∧ ∀ i j, i ≠ j → c i ≠ c j := by
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (show 0 < (L 0).card by rw [hL 0]; norm_num)
  obtain ⟨b, hb, hab⟩ := uni_avoid (L 1) {a} (hL 1) (by simp)
  obtain ⟨c, hc, hc'⟩ := uni_avoid (L 2) {a, b} (hL 2) (Finset.card_le_two.trans (by norm_num))
  obtain ⟨d, hd, hd'⟩ := uni_avoid (L 3) {a, b, c} (hL 3) Finset.card_le_three
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hab hc' hd'
  refine ⟨![a, b, c, d], ?_, ?_⟩
  · intro i
    fin_cases i <;> simpa
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega

theorem uni_pick_sub (Lv : Finset ℕ) (hLv : Lv.card = 4) (c : Fin 4 → ℕ) (k : ℕ) (hk : k ≤ 4) :
    ∃ t : Finset ℕ, t ⊆ Lv \ (Finset.univ.filter (fun i : Fin 4 => i.val < 4 - k)).image c ∧ t.card = k := by
  apply Finset.exists_subset_card_eq
  have h1 := Finset.le_card_sdiff ((Finset.univ.filter (fun i : Fin 4 => i.val < 4 - k)).image c) Lv
  have h2 := Finset.card_image_le (s := Finset.univ.filter (fun i : Fin 4 => i.val < 4 - k)) (f := c)
  have h3 : (Finset.univ.filter (fun i : Fin 4 => i.val < 4 - k)).card = 4 - k := by
    interval_cases k <;> decide
  omega

theorem uni_choosable {W : Type} (H : SimpleGraph W) (L5 : W → Finset ℕ) (hcard : ∀ v, (L5 v).card ≤ 8) (hhalf : ∀ L : W → Finset ℕ, (∀ v, (L v).card = (L5 v).card / 2) → ∃ φ : W → Finset ℕ, IsListSetColoring H L 1 φ) : IsChoosable (uniGraph H L5) 4 1 := by
  intro L hL
  obtain ⟨c, hcL, hcd⟩ := uni_hub (fun i => L (Sum.inl i)) (fun i => hL _)
  have hpick : ∀ (f : Fin 4 → Finset (Fin 8)) (w : W), ∃ t : Finset ℕ,
      t ⊆ L (Sum.inr (f, w)) \ (Finset.univ.filter (fun i : Fin 4 => i.val < 4 - (L5 w).card / 2)).image c
        ∧ t.card = (L5 w).card / 2 :=
    fun f w => uni_pick_sub _ (hL _) c _ (by have := hcard w; omega)
  choose s hs using hpick
  have hcol : ∀ f, ∃ φ : W → Finset ℕ, IsListSetColoring H (s f) 1 φ :=
    fun f => hhalf (s f) (fun w => (hs f w).2)
  choose φ hφ using hcol
  refine ⟨Sum.elim (fun i => {c i}) (fun p => φ p.1 p.2), ?_, ?_⟩
  · rintro (i | ⟨f, w⟩)
    · have := hcL i
      simp only [Sum.elim_inl, Finset.singleton_subset_iff, Finset.card_singleton, and_true]
      exact this
    · obtain ⟨h1, h2⟩ := (hφ f).1 w
      exact ⟨h1.trans ((hs f w).1.trans Finset.sdiff_subset), h2⟩
  · have key : ∀ a b, uniRel H L5 a b →
        Disjoint (Sum.elim (fun i => ({c i} : Finset ℕ)) (fun p => φ p.1 p.2) a)
          (Sum.elim (fun i => ({c i} : Finset ℕ)) (fun p => φ p.1 p.2) b) := by
      rintro (i | ⟨f, w⟩) (j | ⟨g, x⟩) h
      · simp only [uniRel] at h
        simp only [Sum.elim_inl, Finset.disjoint_singleton]
        exact hcd i j h
      · simp only [uniRel] at h
        simp only [Sum.elim_inl, Sum.elim_inr, Finset.disjoint_singleton_left]
        intro hm
        have hm' := (hs g x).1 (((hφ g).1 x).1 hm)
        rw [Finset.mem_sdiff] at hm'
        exact hm'.2 (Finset.mem_image.2 ⟨i, by simpa using h, rfl⟩)
      · simp [uniRel] at h
      · simp only [uniRel] at h
        obtain ⟨rfl, hadj⟩ := h
        exact (hφ f).2 w x hadj
    intro u v huv
    rw [uniGraph, SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with h | h
    · exact key u v h
    · exact (key v u h).symm

theorem exists_four_choosable_not_eight_two_choosable :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      IsChoosable G 4 1 ∧ ¬ IsChoosable G 8 2 := ⟨Fin 4 ⊕ ((Fin 4 → Finset (Fin 8)) × Fin 37), inferInstance, uniGraph g5Graph g5List,
    uni_choosable g5Graph g5List (fun v => (g5_card v).2) g5_half,
    uni_not_choosable g5Graph g5List g5_sub g5_card g5_not_two⟩
-- MAESTRO GENERATED END
end JSP000513
