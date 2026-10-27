module
public import RefinedAbsorption.Faithful2024.Defs
public import RefinedAbsorption.Placement.MultiEmbed
public import RefinedAbsorption.Placement.Absorbers
public import RefinedAbsorption.FlatDown.AntiEdge

/-!
# Absorber gadgets for divisible *multi*-hypergraphs

In the proof of Theorem 3.7 of arXiv:2402.17855v1 an absorber (Theorem 1.4) is attached to every
member `H` of the refinement family of the multi-refiner given by Theorem 3.8.  Such an `H` is a
`K_q^r`-divisible sub-multigraph (it may contain parallel copies).  Here we build, for every such
`H` with at most `c` copies, a *gadget*: a simple `r`-graph `T` on the roots `V(H)` plus `h`
auxiliary vertices (`Fin n ⊕ Fin h`), every edge of which meets an auxiliary vertex, together with
two families of labelled `K_q^r`-copies:

* `Qoff`, a decomposition of `T` into edge-disjoint copies of `K_q^r`;
* `Qon`, a decomposition of `T ∪ H` (the copies of `H` kept as labels) into edge-disjoint copies.

Construction: every copy `c` of `H` (with vertex set `e_c`) gets `q - r` private auxiliary vertices
`N_c`; the clique `K_c` on `e_c ∪ N_c` *moves* the copy `c` to the simple divisible `r`-graph
`L' = ⋃_c (K_c - e_c)` (every edge of which meets some `N_c`, so the union is simple).  A (simple)
absorber `A'` for `L'` from the uniform absorber library completes the gadget: `T = A' ∪ L'`,
`Qoff` = a decomposition of `A' ∪ L'`, `Qon` = a decomposition of `A'` together with the cliques
`K_c`.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.Absorber17

section Gadget

variable {n h : ℕ} {E : Type*} [DecidableEq E]

/-- The vertex sets of the labels of a local gadget: the copies of the piece (`inl c`) sit on the
roots, the template edges (`inr t`) are themselves. -/
def endsL (ends : E → Finset (Fin n)) : E ⊕ Finset (Fin n ⊕ Fin h) → Finset (Fin n ⊕ Fin h) :=
  Sum.elim (fun c => (ends c).map Function.Embedding.inl) id

/-- **Multi-absorber gadget** for the piece `W` (a set of copies). -/
structure IsMultiGadget (q r k : ℕ) (ends : E → Finset (Fin n)) (W : Finset E)
    (T : Finset (Finset (Fin n ⊕ Fin h)))
    (Qon Qoff : Finset (Finset (E ⊕ Finset (Fin n ⊕ Fin h)))) : Prop where
  wf : GadgetWF r k (W.biUnion ends) T
  off_clique : ∀ K ∈ Qoff, IsCliqueCopy q r (endsL ends) K
  off_disj : (Qoff : Set (Finset (E ⊕ Finset (Fin n ⊕ Fin h)))).PairwiseDisjoint id
  off_sup : Qoff.sup id = T.map Function.Embedding.inr
  on_clique : ∀ K ∈ Qon, IsCliqueCopy q r (endsL ends) K
  on_disj : (Qon : Set (Finset (E ⊕ Finset (Fin n ⊕ Fin h)))).PairwiseDisjoint id
  on_sup : Qon.sup id = W.map Function.Embedding.inl ∪ T.map Function.Embedding.inr

/-- A clique, as a set of labelled template edges. -/
def labelClique (r : ℕ) (Q : Finset (Fin n ⊕ Fin h)) : Finset (E ⊕ Finset (Fin n ⊕ Fin h)) :=
  (Q.powersetCard r).map Function.Embedding.inr

theorem isCliqueCopy_labelClique {q r : ℕ} (ends : E → Finset (Fin n))
    {Q : Finset (Fin n ⊕ Fin h)} (hQ : Q.card = q) :
    IsCliqueCopy q r (endsL ends) (labelClique (E := E) r Q) := by
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [labelClique, coe_map, Set.mem_image, mem_coe] at ha hb
    obtain ⟨s, -, rfl⟩ := ha
    obtain ⟨t, -, rfl⟩ := hb
    simpa [endsL] using hab
  · ext t
    simp [labelClique, endsL]

/-- A decomposition of a simple `r`-graph `G`, as labelled cliques. -/
theorem decomposition_labels {q r : ℕ} (ends : E → Finset (Fin n))
    {G 𝒬 : Finset (Finset (Fin n ⊕ Fin h))} (hd : IsDecomposition q r G 𝒬) :
    (∀ K ∈ 𝒬.image (labelClique (E := E) r), IsCliqueCopy q r (endsL ends) K) ∧
    ((𝒬.image (labelClique (E := E) r) : Set (Finset (E ⊕ Finset (Fin n ⊕ Fin h)))).PairwiseDisjoint
      id) ∧
    (𝒬.image (labelClique (E := E) r)).sup id = G.map Function.Embedding.inr := by
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hK
    exact isCliqueCopy_labelClique ends (hd.card_eq Q hQ)
  · intro K hK K' hK' hne
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 (mem_coe.1 hK)
    obtain ⟨Q', hQ', rfl⟩ := mem_image.1 (mem_coe.1 hK')
    have hQQ : Q ≠ Q' := fun h => hne (h ▸ rfl)
    rw [Function.onFun, id, id, disjoint_left]
    intro x hx hx'
    simp only [labelClique, mem_map, mem_powersetCard] at hx hx'
    obtain ⟨t, ⟨htQ, htr⟩, rfl⟩ := hx
    obtain ⟨t', ⟨htQ', -⟩, ht'⟩ := hx'
    have htt : t' = t := Function.Embedding.inr.injective ht'
    subst htt
    have h1 := hd.mult_eq t' htr
    have h2 : 2 ≤ cliqueMult 𝒬 t' := by
      rw [cliqueMult]
      have : ({Q, Q'} : Finset _) ⊆ 𝒬.filter fun P => t' ⊆ P := by
        intro P hP
        rcases mem_insert.1 hP with rfl | hP
        · exact mem_filter.2 ⟨hQ, htQ⟩
        · rw [mem_singleton] at hP; subst hP; exact mem_filter.2 ⟨hQ', htQ'⟩
      exact (card_pair hQQ).symm.le.trans (card_le_card this)
    split_ifs at h1 <;> omega
  · ext x
    rw [mem_sup, mem_map]
    constructor
    · rintro ⟨K, hK, hxK⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hK
      obtain ⟨t, ht, rfl⟩ := mem_map.1 hxK
      exact ⟨t, hd.cliqueEdges_subset hQ ht, rfl⟩
    · rintro ⟨t, htG, rfl⟩
      have h1 := hd.mult_eq t (hd.rgraph t htG)
      rw [if_pos htG, cliqueMult] at h1
      obtain ⟨Q, hQ⟩ := card_pos.1 (by omega : 0 < (𝒬.filter fun Q => t ⊆ Q).card)
      exact ⟨_, mem_image.2 ⟨Q, (mem_filter.1 hQ).1, rfl⟩,
        mem_map.2 ⟨t, mem_powersetCard.2 ⟨(mem_filter.1 hQ).2, hd.rgraph t htG⟩, rfl⟩⟩

end Gadget

section Movers

variable {n h : ℕ} {E : Type*} [DecidableEq E] (q r : ℕ) (ends : E → Finset (Fin n))
  (nv : E → Fin (q - r) → Fin h)

/-- The vertex set `e_c ∪ N_c` of the clique moving the copy `c`. -/
def moverSet (c : E) : Finset (Fin n ⊕ Fin h) :=
  (ends c).map Function.Embedding.inl ∪ univ.image fun j => Sum.inr (nv c j)

/-- The edges of the moving clique other than `e_c`. -/
def moverEdges (c : E) : Finset (Finset (Fin n ⊕ Fin h)) :=
  ((moverSet q r ends nv c).powersetCard r).erase ((ends c).map Function.Embedding.inl)

/-- The moved (simple) graph `L' = ⋃_c (K_c - e_c)`. -/
def moverGraph (W : Finset E) : Finset (Finset (Fin n ⊕ Fin h)) := W.biUnion (moverEdges q r ends nv)

/-- The moving clique of `c`, as labels. -/
def moverLabel (c : E) : Finset (E ⊕ Finset (Fin n ⊕ Fin h)) :=
  insert (Sum.inl c) ((moverEdges q r ends nv c).map Function.Embedding.inr)

variable {q r ends nv}

theorem card_moverSet {c : E} (hrq : r ≤ q) (hc : (ends c).card = r)
    (hinj : Function.Injective (nv c)) : (moverSet q r ends nv c).card = q := by
  rw [moverSet, card_union_of_disjoint, card_map, card_image_of_injective, card_univ,
    Fintype.card_fin, hc]
  · omega
  · intro a b hab; exact hinj (Sum.inr_injective hab)
  · rw [disjoint_left]
    intro x hx hx'
    obtain ⟨a, -, rfl⟩ := mem_map.1 hx
    obtain ⟨j, -, hj⟩ := mem_image.1 hx'
    exact Sum.inr_ne_inl hj

theorem map_inl_mem_powersetCard {c : E} (hc : (ends c).card = r) :
    (ends c).map Function.Embedding.inl ∈ (moverSet q r ends nv c).powersetCard r :=
  mem_powersetCard.2 ⟨subset_union_left, by rw [card_map, hc]⟩

theorem exists_inr_of_mem_moverEdges {c : E} (hc : (ends c).card = r) {t : Finset (Fin n ⊕ Fin h)}
    (ht : t ∈ moverEdges q r ends nv c) : ∃ j, Sum.inr (nv c j) ∈ t := by
  rw [moverEdges, mem_erase, mem_powersetCard] at ht
  obtain ⟨hne, hsub, hcard⟩ := ht
  by_contra hno
  push_neg at hno
  apply hne
  apply eq_of_subset_of_card_le
  · intro x hx
    rcases mem_union.1 (hsub hx) with h' | h'
    · exact h'
    · obtain ⟨j, -, rfl⟩ := mem_image.1 h'
      exact absurd hx (hno j)
  · rw [card_map, hc, hcard]

theorem inl_mem_moverEdges {c : E} {t : Finset (Fin n ⊕ Fin h)}
    (ht : t ∈ moverEdges q r ends nv c) {a : Fin n} (ha : Sum.inl a ∈ t) : a ∈ ends c := by
  rw [moverEdges, mem_erase, mem_powersetCard] at ht
  rcases mem_union.1 (ht.2.1 ha) with h' | h'
  · obtain ⟨b, hb, hba⟩ := mem_map.1 h'
    rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hba
    exact hba ▸ hb
  · obtain ⟨j, -, hj⟩ := mem_image.1 h'
    exact absurd hj Sum.inr_ne_inl

theorem inr_mem_moverEdges {c : E} {t : Finset (Fin n ⊕ Fin h)}
    (ht : t ∈ moverEdges q r ends nv c) {p : Fin h} (hp : Sum.inr p ∈ t) : ∃ j, nv c j = p := by
  rw [moverEdges, mem_erase, mem_powersetCard] at ht
  rcases mem_union.1 (ht.2.1 hp) with h' | h'
  · obtain ⟨b, -, hb⟩ := mem_map.1 h'
    exact absurd hb Sum.inl_ne_inr
  · obtain ⟨j, -, hj⟩ := mem_image.1 h'
    exact ⟨j, Sum.inr_injective hj⟩

theorem disjoint_moverEdges {c c' : E} (hc : (ends c).card = r)
    (hnv : ∀ j j', nv c j ≠ nv c' j') :
    Disjoint (moverEdges q r ends nv c) (moverEdges q r ends nv c') := by
  rw [disjoint_left]
  intro t ht ht'
  obtain ⟨j, hj⟩ := exists_inr_of_mem_moverEdges hc ht
  obtain ⟨j', hj'⟩ := inr_mem_moverEdges ht' hj
  exact hnv j j' hj'.symm

theorem card_mem_moverEdges {c : E} {t : Finset (Fin n ⊕ Fin h)}
    (ht : t ∈ moverEdges q r ends nv c) : t.card = r :=
  (mem_powersetCard.1 (mem_of_mem_erase ht)).2

/-- Degrees in a mover: `deg(K_c - e_c, S) + [S ⊆ e_c] = deg(K_c, S)`. -/
theorem deg_moverEdges_add {c : E} (hc : (ends c).card = r) (S : Finset (Fin n ⊕ Fin h)) :
    deg (moverEdges q r ends nv c) S +
        (if S ⊆ (ends c).map Function.Embedding.inl then 1 else 0) =
      deg (cliqueEdges r (moverSet q r ends nv c)) S := by
  rw [deg, deg, moverEdges, cliqueEdges, filter_erase]
  split_ifs with hS
  · rw [card_erase_of_mem (mem_filter.2 ⟨map_inl_mem_powersetCard hc, hS⟩)]
    exact Nat.sub_add_cancel (card_pos.2 ⟨_, mem_filter.2 ⟨map_inl_mem_powersetCard hc, hS⟩⟩)
  · rw [erase_eq_of_notMem (fun h' => hS (mem_filter.1 h').2), add_zero]

end Movers

section MoverGraph

variable {n h : ℕ} {E : Type*} [DecidableEq E] {q r : ℕ} {ends : E → Finset (Fin n)}
  {nv : E → Fin (q - r) → Fin h} {W : Finset E}

theorem isRGraph_moverGraph : IsRGraph r (moverGraph q r ends nv W) := by
  intro t ht
  obtain ⟨c, -, htc⟩ := mem_biUnion.1 ht
  exact card_mem_moverEdges htc

theorem deg_moverGraph (hW : ∀ c ∈ W, (ends c).card = r)
    (hsep : ∀ c ∈ W, ∀ c' ∈ W, c ≠ c' → ∀ j j', nv c j ≠ nv c' j')
    (S : Finset (Fin n ⊕ Fin h)) :
    deg (moverGraph q r ends nv W) S = ∑ c ∈ W, deg (moverEdges q r ends nv c) S := by
  rw [deg, moverGraph, filter_biUnion, card_biUnion]
  · rfl
  · intro c hc c' hc' hne
    exact disjoint_filter_filter (disjoint_moverEdges (hW c hc) (hsep c hc c' hc' hne))

theorem isDivisible_moverGraph (hrq : r < q) (hW : ∀ c ∈ W, (ends c).card = r)
    (hinj : ∀ c ∈ W, Function.Injective (nv c))
    (hsep : ∀ c ∈ W, ∀ c' ∈ W, c ≠ c' → ∀ j j', nv c j ≠ nv c' j')
    (hdiv : MIsDivisible q r ends W) : IsDivisible q r (moverGraph q r ends nv W) := by
  intro S hS
  rw [deg_moverGraph hW hsep]
  have hsum : ∑ c ∈ W, deg (moverEdges q r ends nv c) S +
      ∑ c ∈ W, (if S ⊆ (ends c).map Function.Embedding.inl then 1 else 0) =
      ∑ c ∈ W, deg (cliqueEdges r (moverSet q r ends nv c)) S := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun c hc => deg_moverEdges_add (hW c hc) S
  have hcl : (q - S.card).choose (r - S.card) ∣
      ∑ c ∈ W, deg (cliqueEdges r (moverSet q r ends nv c)) S :=
    dvd_sum fun c hc => FlatDown.dvd_deg_cliqueEdges
      (card_moverSet hrq.le (hW c hc) (hinj c hc)) hS.le
  have hind : (q - S.card).choose (r - S.card) ∣
      ∑ c ∈ W, (if S ⊆ (ends c).map Function.Embedding.inl then 1 else 0) := by
    rw [sum_boole]
    by_cases hinr : ∃ p, Sum.inr p ∈ S
    · obtain ⟨p, hp⟩ := hinr
      convert dvd_zero _
      rw [Nat.cast_id, card_eq_zero, filter_eq_empty_iff]
      intro c _ hsub
      obtain ⟨a, -, ha⟩ := mem_map.1 (hsub hp)
      exact Sum.inl_ne_inr ha
    · push_neg at hinr
      set S0 := S.preimage Sum.inl (Sum.inl_injective.injOn) with hS0
      have hSS0 : S = S0.map Function.Embedding.inl := by
        ext x
        rcases x with a | p
        · simp [hS0]
        · simp [hinr p]
      have hc0 : S0.card = S.card := by rw [hSS0, card_map]
      have := hdiv S0 (by omega)
      rw [hc0] at this
      convert this using 1
      rw [Nat.cast_id, mdeg]
      congr 1
      apply filter_congr
      intro c _
      rw [hSS0, map_subset_map]
  rw [← hsum] at hcl
  exact (Nat.dvd_add_left hind).1 hcl

theorem card_moverGraph_le (hrq : r ≤ q) (hW : ∀ c ∈ W, (ends c).card = r)
    (hinj : ∀ c ∈ W, Function.Injective (nv c)) :
    (moverGraph q r ends nv W).card ≤ W.card * q.choose r := by
  calc _ ≤ ∑ c ∈ W, (moverEdges q r ends nv c).card := card_biUnion_le
    _ ≤ ∑ _c ∈ W, q.choose r := sum_le_sum fun c hc => (card_erase_le).trans
        (by rw [card_powersetCard, card_moverSet hrq (hW c hc) (hinj c hc)])
    _ = W.card * q.choose r := by rw [sum_const, smul_eq_mul]

theorem mem_vertexSet_moverGraph {x : Fin n ⊕ Fin h} (hx : x ∈ vertexSet (moverGraph q r ends nv W)) :
    (∃ a ∈ W.biUnion ends, x = Sum.inl a) ∨ (∃ c ∈ W, ∃ j, x = Sum.inr (nv c j)) := by
  obtain ⟨t, ht, hxt⟩ := mem_sup.1 hx
  obtain ⟨c, hc, htc⟩ := mem_biUnion.1 ht
  rcases x with a | p
  · exact Or.inl ⟨a, mem_biUnion.2 ⟨c, hc, inl_mem_moverEdges htc hxt⟩, rfl⟩
  · obtain ⟨j, hj⟩ := inr_mem_moverEdges htc hxt
    exact Or.inr ⟨c, hc, j, hj ▸ rfl⟩

end MoverGraph

section Existence

variable {n h : ℕ} {E : Type*} [DecidableEq E] {q r : ℕ} {ends : E → Finset (Fin n)}
  {nv : E → Fin (q - r) → Fin h} {W : Finset E}

theorem isCliqueCopy_moverLabel (hrq : r ≤ q) {c : E} (hc : (ends c).card = r)
    (hinj : Function.Injective (nv c)) :
    IsCliqueCopy q r (endsL ends) (moverLabel q r ends nv c) := by
  refine ⟨moverSet q r ends nv c, card_moverSet hrq hc hinj, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [moverLabel, coe_insert, coe_map, Set.mem_insert_iff, Set.mem_image,
      mem_coe] at ha hb
    rcases ha with rfl | ⟨t, ht, rfl⟩ <;> rcases hb with rfl | ⟨t', ht', rfl⟩
    · rfl
    · exact absurd hab.symm (ne_of_mem_erase ht')
    · exact absurd hab (ne_of_mem_erase ht)
    · simpa [endsL] using hab
  · rw [moverLabel, image_insert, map_eq_image, image_image]
    have : (endsL ends ∘ ⇑Function.Embedding.inr : Finset (Fin n ⊕ Fin h) → _) = id := by
      funext t; rfl
    rw [this, image_id]
    exact insert_erase (map_inl_mem_powersetCard hc)

theorem disjoint_moverLabel {c c' : E} (hne : c ≠ c') (hc : (ends c).card = r)
    (hnv : ∀ j j', nv c j ≠ nv c' j') :
    Disjoint (moverLabel q r ends nv c) (moverLabel q r ends nv c') := by
  rw [moverLabel, moverLabel, disjoint_insert_left, disjoint_insert_right, disjoint_map]
  refine ⟨?_, ?_, disjoint_moverEdges hc hnv⟩
  · simp only [mem_insert, Sum.inl.injEq, mem_map, not_or]
    exact ⟨hne, fun ⟨_, _, h'⟩ => Sum.inr_ne_inl h'⟩
  · simp only [mem_map, not_exists, not_and]
    intro t _ h'
    exact Sum.inr_ne_inl h'

theorem nat_mul_add_inj {a b j j' m : ℕ} (hj : j < m) (hj' : j' < m)
    (h : a * m + j = b * m + j') : a = b ∧ j = j' := by
  have hab : a = b := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have : (a + 1) * m ≤ b * m := Nat.mul_le_mul_right _ hlt
      nlinarith
    · exact heq
    · have : (b + 1) * m ≤ a * m := Nat.mul_le_mul_right _ hgt
      nlinarith
  subst hab
  exact ⟨rfl, by omega⟩

end Existence

/-- **Absorber gadgets for divisible multi-hypergraphs.**  Fix `q > r ≥ 1` and `c`.  There is
`h` such that every nonempty `K_q^r`-divisible `r`-uniform multi-hypergraph `W` (labelled copies)
on `Fin n` with at most `c` copies has a multi-absorber gadget with `h` auxiliary vertices. -/
theorem exists_multiGadget {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (c : ℕ) :
    ∃ h : ℕ, ∀ (n : ℕ) {E : Type*} [DecidableEq E] (ends : E → Finset (Fin n)) (W : Finset E),
      W.Nonempty → MIsRGraph r ends W → MIsDivisible q r ends W → W.card ≤ c →
      ∃ (T : Finset (Finset (Fin n ⊕ Fin h)))
        (Qon Qoff : Finset (Finset (E ⊕ Finset (Fin n ⊕ Fin h)))),
        IsMultiGadget q r (r * c) ends W T Qon Qoff := by
  obtain ⟨B, hB⟩ := absorberLibrary hr hrq (c * q.choose r)
  refine ⟨c * (q - r) + B, ?_⟩
  intro n E _ ends W hne hWr hdiv hWc
  classical
  set h := c * (q - r) + B with hh
  obtain ⟨c₀, hc₀⟩ := hne
  have hc1 : 1 ≤ c := le_trans (card_pos.2 ⟨c₀, hc₀⟩) hWc
  let idx : E → ℕ := fun x => if hx : x ∈ W then (W.equivFin ⟨x, hx⟩ : ℕ) else 0
  have hidx : ∀ x, idx x < c := by
    intro x
    simp only [idx]
    split_ifs with hx
    · exact lt_of_lt_of_le (W.equivFin ⟨x, hx⟩).2 hWc
    · omega
  have hidxW : ∀ x ∈ W, ∀ y ∈ W, idx x = idx y → x = y := by
    intro x hx y hy hxy
    simp only [idx, dif_pos hx, dif_pos hy] at hxy
    have := W.equivFin.injective (Fin.ext hxy)
    exact congrArg Subtype.val this
  have hbound : ∀ x (j : Fin (q - r)), idx x * (q - r) + j < h := by
    intro x j
    have h1 : (idx x + 1) * (q - r) ≤ c * (q - r) := Nat.mul_le_mul_right _ (hidx x)
    have h2 := j.2
    rw [add_mul, one_mul] at h1
    omega
  let nv : E → Fin (q - r) → Fin h := fun x j => ⟨idx x * (q - r) + j, hbound x j⟩
  have hnv_lt : ∀ x j, (nv x j : ℕ) < c * (q - r) := by
    intro x j
    have h1 : (idx x + 1) * (q - r) ≤ c * (q - r) := Nat.mul_le_mul_right _ (hidx x)
    have h2 := j.2
    rw [add_mul, one_mul] at h1
    show idx x * (q - r) + j < c * (q - r)
    omega
  have hinj : ∀ x ∈ W, Function.Injective (nv x) := by
    intro x _ j j' hjj
    have := congrArg Fin.val hjj
    simp only [nv] at this
    exact Fin.ext (by omega)
  have hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∀ j j', nv x j ≠ nv y j' := by
    intro x hx y hy hxy j j' hjj
    have := congrArg Fin.val hjj
    simp only [nv] at this
    exact hxy (hidxW x hx y hy (nat_mul_add_inj j.2 j'.2 this).1)
  set L' := moverGraph q r ends nv W with hL'
  -- the prescribed vertices of the absorber
  let sv : Fin B ↪ Fin n ⊕ Fin h :=
    ⟨fun p => Sum.inr ⟨c * (q - r) + p, by omega⟩, fun p p' hpp => by
      have := congrArg Fin.val (Sum.inr_injective hpp)
      simp only at this
      exact Fin.ext (by omega)⟩
  set S := (univ : Finset (Fin B)).map sv with hS
  have hSdisj : Disjoint S (vertexSet L') := by
    rw [disjoint_left]
    intro x hxS hxL
    obtain ⟨p, -, rfl⟩ := mem_map.1 hxS
    rcases mem_vertexSet_moverGraph hxL with ⟨a, -, ha⟩ | ⟨y, -, j, hj⟩
    · exact Sum.inr_ne_inl ha
    · have := congrArg Fin.val (Sum.inr_injective hj)
      have h1 := hnv_lt y j
      simp only at this
      omega
  have hL'c : L'.card ≤ c * q.choose r :=
    (card_moverGraph_le hrq.le hWr hinj).trans (Nat.mul_le_mul_right _ hWc)
  obtain ⟨A, Qon', Qoff', hbd, hvert⟩ := hB (Fin n ⊕ Fin h) L' isRGraph_moverGraph
    (isDivisible_moverGraph hrq hWr hinj hsep hdiv) hL'c S hSdisj
    (by rw [hS, card_map, card_univ, Fintype.card_fin])
  have hAL : Disjoint A L' := by
    rw [disjoint_left]
    intro t htA htL
    exact hbd.absorber.independent t htA (subset_vertexSet htL)
  obtain ⟨hoffc, hoffd, hoffs⟩ := decomposition_labels (E := E) ends hbd.on
  obtain ⟨honc, hond, hons⟩ := decomposition_labels (E := E) ends hbd.off
  refine ⟨A ∪ L', Qoff'.image (labelClique r) ∪ W.image (moverLabel q r ends nv),
    Qon'.image (labelClique r), ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hoffc, hoffd, hoffs, ?_, ?_, ?_⟩⟩
  · -- roots_le
    calc (W.biUnion ends).card ≤ ∑ x ∈ W, (ends x).card := card_biUnion_le
      _ = ∑ _x ∈ W, r := sum_congr rfl fun x hx => hWr x hx
      _ = W.card * r := by rw [sum_const, smul_eq_mul]
      _ ≤ r * c := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hWc
  · -- roots_ge
    calc r - 1 ≤ (ends c₀).card := by rw [hWr c₀ hc₀]; omega
      _ ≤ _ := card_le_card (subset_biUnion_of_mem ends hc₀)
  · exact hbd.on.rgraph
  · intro t ht a ha
    rcases mem_union.1 ht with htA | htL
    · rcases mem_union.1 (hvert (subset_vertexSet htA ha)) with h' | h'
      · rcases mem_vertexSet_moverGraph h' with ⟨b, hb, hba⟩ | ⟨y, -, j, hj⟩
        · rw [Sum.inl.injEq] at hba; exact hba ▸ hb
        · exact absurd hj Sum.inl_ne_inr
      · obtain ⟨p, -, hp⟩ := mem_map.1 h'
        exact absurd hp Sum.inr_ne_inl
    · obtain ⟨x, hx, htx⟩ := mem_biUnion.1 htL
      exact mem_biUnion.2 ⟨x, hx, inl_mem_moverEdges htx ha⟩
  · intro t ht
    rcases mem_union.1 ht with htA | htL
    · obtain ⟨x, hxt, hxS⟩ := IsAbsorber.exists_mem_of_subset hbd.absorber hvert htA
      obtain ⟨p, -, rfl⟩ := mem_map.1 hxS
      exact ⟨_, hxt⟩
    · obtain ⟨x, hx, htx⟩ := mem_biUnion.1 htL
      obtain ⟨j, hj⟩ := exists_inr_of_mem_moverEdges (hWr x hx) htx
      exact ⟨_, hj⟩
  · -- on cliques
    intro K hK
    rcases mem_union.1 hK with hK | hK
    · exact honc K hK
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hK
      exact isCliqueCopy_moverLabel hrq.le (hWr x hx) (hinj x hx)
  · -- on disjointness
    rw [coe_union, Set.pairwiseDisjoint_union]
    refine ⟨hond, ?_, ?_⟩
    · intro K hK K' hK' hKK
      obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hK)
      obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_coe.1 hK')
      have hxy : x ≠ y := fun h' => hKK (h' ▸ rfl)
      exact disjoint_moverLabel hxy (hWr x hx) (hsep x hx y hy hxy)
    · intro K hK K' hK' _
      obtain ⟨Q, hQ, rfl⟩ := mem_image.1 (mem_coe.1 hK)
      obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_coe.1 hK')
      rw [id, id, disjoint_left]
      intro z hz hz'
      obtain ⟨t, ht, rfl⟩ := mem_map.1 hz
      have htA : t ∈ A := hbd.off.cliqueEdges_subset hQ ht
      rcases mem_insert.1 hz' with h' | h'
      · exact Sum.inr_ne_inl h'
      · obtain ⟨t', ht', htt⟩ := mem_map.1 h'
        have : t' = t := Function.Embedding.inr.injective htt
        subst this
        exact disjoint_left.1 hAL htA (mem_biUnion.2 ⟨y, hy, ht'⟩)
  · -- on union
    rw [sup_union, hons, map_union]
    have hmov : (W.image (moverLabel q r ends nv)).sup id =
        W.map Function.Embedding.inl ∪ L'.map Function.Embedding.inr := by
      ext z
      simp only [mem_sup, mem_image, id, mem_union, mem_map]
      constructor
      · rintro ⟨K, ⟨x, hx, rfl⟩, hz⟩
        rcases mem_insert.1 hz with rfl | hz
        · exact Or.inl ⟨x, hx, rfl⟩
        · obtain ⟨t, ht, rfl⟩ := mem_map.1 hz
          exact Or.inr ⟨t, mem_biUnion.2 ⟨x, hx, ht⟩, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨t, ht, rfl⟩)
        · exact ⟨_, ⟨x, hx, rfl⟩, mem_insert_self _ _⟩
        · obtain ⟨x, hx, htx⟩ := mem_biUnion.1 ht
          exact ⟨_, ⟨x, hx, rfl⟩, mem_insert_of_mem (mem_map_of_mem _ htx)⟩
    rw [hmov]
    ext z
    simp only [Finset.sup_eq_union, mem_union]
    tauto

end RefinedAbsorption.Faithful2024
