module
public import RequestProject.MultiRefiner.FakeEdge

/-!
# Multiplicity reduction

Given a `C`-refined multi-refiner `R` of `X` (copies labelled by `E`) and a set `K ⊇ X` of labels
on which `ends` is injective (the copies that are kept as genuine edges), we replace every copy
`i ∉ K` by its fake edge on new vertices tagged by `i`.  The result is a genuine (simple) refined
refiner in the sense of `IsRefinedRefiner`, on the extended vertex type `V ⊕ (E × _ × _)`,
with refinedness `C · fakeBound q r` (`multiplicityReduction`).

The invariant recorded for the final embedding step (`ReductionInvariant`):

* the reduced graph is a `C · fakeBound`-refined refiner of the lifted copy of `X`;
* the lifted `X` is exactly the image of `X` (`gimg_eq_image`);
* (root degrees) for every set `S₀` of old vertices and every sub-multigraph `G ⊆ X ∪ R`,
  `deg(G', S₀) ≤ fakeBound · mdeg(G, S₀)`, so the `(r-1)`-degree budget of the reduced refiner on
  old vertices is controlled by the budget of the multi-refiner;
* (fresh degrees) every set containing a new vertex has degree at most `fakeBound`.

The global statement `RefinerAbsorbersFor q r` (for `r ≥ 2`) stays open: it still needs refiners
whose degree budget is `O(max(D, n^{1-1/r} log n))`, and the embedding of the new vertices (of the
fake edges and of the attached absorbers) into `K_n^r`.
-/

@[expose] public section

namespace RefinedAbsorption.MultiRefiner

open Finset

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The image of a copy: the lifted edge if `i ∈ K`, otherwise the fake edge of `i`. -/
def img (q r : ℕ) (ends : E → Finset V) (K : Finset E) (i : E) : Finset (Finset (XV V E q r)) :=
  if i ∈ K then {lift q r ends i} else fakeEdge q r ends i

/-- The image of a labelled multigraph. -/
def gimg (q r : ℕ) (ends : E → Finset V) (K : Finset E) (G : Finset E) :
    Finset (Finset (XV V E q r)) :=
  G.biUnion (img q r ends K)

/-- The constant `m · binom(q, r) + 1` bounding the size of the image of one copy. -/
def fakeBound (q r : ℕ) : ℕ := fakeCount q r * q.choose r + 1

section

variable {q r : ℕ} {ends : E → Finset V} {K : Finset E}

theorem one_le_fakeBound : 1 ≤ fakeBound q r := Nat.le_add_left _ _

omit [DecidableEq V] [DecidableEq E] in
theorem inr_not_mem_lift {i : E} (x : E × Fin (fakeCount q r) × Fin (q - r)) :
    (Sum.inr x : XV V E q r) ∉ lift q r ends i := by
  intro h
  obtain ⟨v, -, hv⟩ := mem_map.1 h
  simp at hv

theorem img_card_edge {i : E} (hi : (ends i).card = r) {f : Finset (XV V E q r)}
    (hf : f ∈ img q r ends K i) : f.card = r := by
  unfold img at hf
  split_ifs at hf
  · rw [mem_singleton.1 hf, card_lift, hi]
  · exact fakeEdge_card_edge hf

theorem card_img_le (hrq : r ≤ q) {i : E} (hi : (ends i).card = r) :
    (img q r ends K i).card ≤ fakeBound q r := by
  unfold img fakeBound
  split_ifs
  · simp
  · exact (card_fakeEdge_le hrq hi).trans (Nat.le_succ _)

theorem img_inl {i : E} {f : Finset (XV V E q r)} (hf : f ∈ img q r ends K i) {v : V}
    (hv : (Sum.inl v : XV V E q r) ∈ f) : v ∈ ends i := by
  unfold img at hf
  split_ifs at hf
  · rw [mem_singleton.1 hf] at hv
    obtain ⟨w, hw, hwv⟩ := mem_map.1 hv
    simp only [Function.Embedding.inl_apply, Sum.inl.injEq] at hwv
    exact hwv ▸ hw
  · exact fakeEdge_inl hf hv

theorem img_fresh_tag {i : E} {f : Finset (XV V E q r)} (hf : f ∈ img q r ends K i) {i' : E}
    {j : Fin (fakeCount q r)} {t : Fin (q - r)} (hx : (Sum.inr (i', j, t) : XV V E q r) ∈ f) :
    i' = i := by
  unfold img at hf
  split_ifs at hf
  · rw [mem_singleton.1 hf] at hx
    exact absurd hx (inr_not_mem_lift _)
  · exact fakeEdge_fresh_tag hf hx

theorem img_exists_fresh {i : E} (hi : (ends i).card = r) (hiK : i ∉ K)
    {f : Finset (XV V E q r)} (hf : f ∈ img q r ends K i) :
    ∃ j t, (Sum.inr (i, j, t) : XV V E q r) ∈ f := by
  unfold img at hf
  rw [if_neg hiK] at hf
  exact fakeEdge_exists_fresh hi hf

/-- Images of distinct copies are edge-disjoint. -/
theorem img_disjoint (hinj : Set.InjOn ends K) {i i' : E} (hi : (ends i).card = r)
    (hi' : (ends i').card = r) (hne : i ≠ i') :
    Disjoint (img q r ends K i) (img q r ends K i') := by
  rw [disjoint_left]
  intro f hf hf'
  by_cases hiK : i ∈ K
  · by_cases hiK' : i' ∈ K
    · unfold img at hf hf'
      rw [if_pos hiK] at hf
      rw [if_pos hiK'] at hf'
      have h := (mem_singleton.1 hf).symm.trans (mem_singleton.1 hf')
      exact hne (hinj hiK hiK' (map_injective _ h))
    · obtain ⟨j, t, ht⟩ := img_exists_fresh hi' hiK' hf'
      exact hne (img_fresh_tag hf ht).symm
  · obtain ⟨j, t, ht⟩ := img_exists_fresh hi hiK hf
    exact hne (img_fresh_tag hf' ht)

theorem img_pairwiseDisjoint (hinj : Set.InjOn ends K) {G : Finset E} (hG : MIsRGraph r ends G) :
    (G : Set E).PairwiseDisjoint (img q r ends K) :=
  fun _ hi _ hi' hne => img_disjoint hinj (hG _ hi) (hG _ hi') hne

theorem mem_gimg {G : Finset E} {f : Finset (XV V E q r)} :
    f ∈ gimg q r ends K G ↔ ∃ i ∈ G, f ∈ img q r ends K i := mem_biUnion

theorem gimg_union (G H : Finset E) :
    gimg q r ends K (G ∪ H) = gimg q r ends K G ∪ gimg q r ends K H := union_biUnion

theorem gimg_mono {G H : Finset E} (h : G ⊆ H) : gimg q r ends K G ⊆ gimg q r ends K H :=
  biUnion_subset_biUnion_of_subset_left _ h

/-- The copy of `f` in a disjoint family is unique. -/
theorem img_unique (hinj : Set.InjOn ends K) {i i' : E} (hi : (ends i).card = r)
    (hi' : (ends i').card = r) {f : Finset (XV V E q r)} (hf : f ∈ img q r ends K i)
    (hf' : f ∈ img q r ends K i') : i = i' := by
  by_contra hne
  exact disjoint_left.1 (img_disjoint hinj hi hi' hne) hf hf'

theorem disjoint_gimg (hinj : Set.InjOn ends K) {G H : Finset E} (hG : MIsRGraph r ends G)
    (hH : MIsRGraph r ends H) (hGH : Disjoint G H) :
    Disjoint (gimg q r ends K G) (gimg q r ends K H) := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨i, hi, hfi⟩ := mem_gimg.1 hf
  obtain ⟨i', hi', hfi'⟩ := mem_gimg.1 hf'
  have := img_unique hinj (hG i hi) (hH i' hi') hfi hfi'
  subst this
  exact disjoint_left.1 hGH hi hi'

theorem deg_gimg (hinj : Set.InjOn ends K) {G : Finset E} (hG : MIsRGraph r ends G)
    (S : Finset (XV V E q r)) :
    deg (gimg q r ends K G) S = ∑ i ∈ G, deg (img q r ends K i) S := by
  rw [deg, gimg, filter_biUnion, card_biUnion]
  · rfl
  · intro i hi i' hi' hne
    exact disjoint_filter_filter (img_pairwiseDisjoint hinj hG hi hi' hne)

theorem card_gimg_le (hrq : r ≤ q) (hinj : Set.InjOn ends K) {G : Finset E}
    (hG : MIsRGraph r ends G) : (gimg q r ends K G).card ≤ G.card * fakeBound q r := by
  rw [gimg, card_biUnion (fun i hi i' hi' hne => img_pairwiseDisjoint hinj hG hi hi' hne)]
  calc ∑ i ∈ G, (img q r ends K i).card ≤ ∑ _i ∈ G, fakeBound q r :=
        sum_le_sum fun i hi => card_img_le hrq (hG i hi)
    _ = G.card * fakeBound q r := by rw [sum_const, smul_eq_mul]

theorem IsRGraph_gimg {G : Finset E} (hG : MIsRGraph r ends G) :
    IsRGraph r (gimg q r ends K G) := by
  intro f hf
  obtain ⟨i, hi, hfi⟩ := mem_gimg.1 hf
  exact img_card_edge (hG i hi) hfi

/-- On kept copies the image is the lifted multigraph. -/
theorem gimg_eq_image {G : Finset E} (hGK : G ⊆ K) :
    gimg q r ends K G = G.image (lift q r ends) := by
  ext f
  rw [mem_gimg, mem_image]
  constructor
  · rintro ⟨i, hi, hf⟩
    unfold img at hf
    rw [if_pos (hGK hi)] at hf
    exact ⟨i, hi, (mem_singleton.1 hf).symm⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    unfold img
    rw [if_pos (hGK hi)]
    exact mem_singleton_self _

/-- Modulo `binom(q-|S|, r-|S|)` the degree of the image of one copy is `[S ⊆ e]`. -/
theorem deg_img_cast (hrq : r ≤ q) {i : E} (hi : (ends i).card = r) {S : Finset (XV V E q r)}
    (hS : S.card < r) :
    ((deg (img q r ends K i) S : ℕ) : ZMod ((q - S.card).choose (r - S.card))) =
      if S ⊆ lift q r ends i then 1 else 0 := by
  unfold img
  split_ifs with hK h h
  · simp [deg, filter_singleton, h]
  · simp [deg, filter_singleton, h]
  · rw [fakeEdge_deg_cast hrq hi hS, if_pos h]
  · rw [fakeEdge_deg_cast hrq hi hS, if_neg h]

/-- Counting the copies whose lift contains `S`. -/
theorem card_filter_lift_dvd {G : Finset E} (hG : MIsDivisible q r ends G)
    {S : Finset (XV V E q r)} (hS : S.card < r) :
    (q - S.card).choose (r - S.card) ∣ (G.filter fun i => S ⊆ lift q r ends i).card := by
  by_cases hrange : ∀ x ∈ S, ∃ v, (Sum.inl v : XV V E q r) = x
  · classical
    set S₀ := S.preimage (fun v => (Sum.inl v : XV V E q r)) Sum.inl_injective.injOn with hS₀
    have hmap : S₀.map Function.Embedding.inl = S := by
      ext x
      simp only [mem_map, hS₀, mem_preimage, Function.Embedding.inl_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        obtain ⟨v, rfl⟩ := hrange x hx
        exact ⟨v, hx, rfl⟩
    have hcard : S₀.card = S.card := by rw [← hmap, card_map]
    have hfilt : (G.filter fun i => S ⊆ lift q r ends i) = G.filter fun i => S₀ ⊆ ends i := by
      refine filter_congr fun i _ => ?_
      rw [← hmap, lift, map_subset_map]
    rw [hfilt, ← hcard]
    exact hG S₀ (hcard ▸ hS)
  · push_neg at hrange
    obtain ⟨x, hx, hxv⟩ := hrange
    have : (G.filter fun i => S ⊆ lift q r ends i) = ∅ := by
      refine filter_eq_empty_iff.2 fun i _ hsub => ?_
      obtain ⟨v, -, hv⟩ := mem_map.1 (hsub hx)
      exact hxv v hv
    rw [this, card_empty]
    exact dvd_zero _

/-- The image of a divisible multigraph is divisible. -/
theorem isDivisible_gimg (hrq : r ≤ q) (hinj : Set.InjOn ends K) {G : Finset E}
    (hG : MIsRGraph r ends G) (hdiv : MIsDivisible q r ends G) :
    IsDivisible q r (gimg q r ends K G) := by
  intro S hS
  rw [← ZMod.natCast_eq_zero_iff, deg_gimg hinj hG, Nat.cast_sum,
    sum_congr rfl (fun i hi => deg_img_cast hrq (hG i hi) hS), ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one]
  exact (ZMod.natCast_eq_zero_iff _ _).2 (card_filter_lift_dvd hdiv hS)

/-- **Root degrees.**  Old-vertex sets have degree at most `fakeBound · mdeg`. -/
theorem deg_gimg_root_le (hrq : r ≤ q) (hinj : Set.InjOn ends K) {G : Finset E}
    (hG : MIsRGraph r ends G) (S₀ : Finset V) :
    deg (gimg q r ends K G) (S₀.map Function.Embedding.inl) ≤ fakeBound q r * mdeg ends G S₀ := by
  rw [deg_gimg hinj hG]
  calc ∑ i ∈ G, deg (img q r ends K i) (S₀.map Function.Embedding.inl)
      ≤ ∑ i ∈ G, if S₀ ⊆ ends i then fakeBound q r else 0 := by
        refine sum_le_sum fun i hi => ?_
        split_ifs with h
        · exact (card_le_card (filter_subset _ _)).trans (card_img_le hrq (hG i hi))
        · rw [deg, card_eq_zero.2 (filter_eq_empty_iff.2 fun f hf hsub => h fun v hv =>
            img_inl hf (hsub (mem_map_of_mem _ hv)))]
    _ = fakeBound q r * mdeg ends G S₀ := by
        rw [← sum_filter, sum_const, smul_eq_mul, mdeg, mul_comm]

/-- **Fresh degrees.**  A set containing a new vertex has degree at most `fakeBound`. -/
theorem deg_gimg_fresh_le (hrq : r ≤ q) {G : Finset E}
    (hG : MIsRGraph r ends G) {S : Finset (XV V E q r)}
    {x : E × Fin (fakeCount q r) × Fin (q - r)} (hx : (Sum.inr x : XV V E q r) ∈ S) :
    deg (gimg q r ends K G) S ≤ fakeBound q r := by
  obtain ⟨i₀, j, t⟩ := x
  have hsub : (gimg q r ends K G).filter (fun f => S ⊆ f) ⊆ img q r ends K i₀ := by
    intro f hf
    obtain ⟨hfG, hSf⟩ := mem_filter.1 hf
    obtain ⟨i, -, hfi⟩ := mem_gimg.1 hfG
    rw [img_fresh_tag hfi (hSf hx)]
    exact hfi
  by_cases hi₀ : i₀ ∈ G
  · exact (card_le_card hsub).trans (card_img_le hrq (hG i₀ hi₀))
  · have : (gimg q r ends K G).filter (fun f => S ⊆ f) = ∅ := by
      refine filter_eq_empty_iff.2 fun f hfG hSf => ?_
      obtain ⟨i, hi, hfi⟩ := mem_gimg.1 hfG
      exact hi₀ (img_fresh_tag hfi (hSf hx) ▸ hi)
    rw [deg, this, card_empty]
    exact Nat.zero_le _

theorem sup_image_gimg (𝒰 : Finset (Finset E)) :
    (𝒰.image (gimg q r ends K)).sup id = gimg q r ends K (𝒰.sup id) := by
  ext f
  simp only [mem_sup, mem_image, id, mem_gimg]
  constructor
  · rintro ⟨_, ⟨W, hW, rfl⟩, hf⟩
    obtain ⟨i, hi, hfi⟩ := mem_gimg.1 hf
    exact ⟨i, ⟨W, hW, hi⟩, hfi⟩
  · rintro ⟨i, ⟨W, hW, hi⟩, hfi⟩
    exact ⟨_, ⟨W, hW, rfl⟩, mem_gimg.2 ⟨i, hi, hfi⟩⟩

end

/-- **The invariant kept for the final embedding.**  After multiplicity reduction:
the reduced graph is a `C · fakeBound`-refined refiner of the lifted `X`; the lifted `X` is the
image of `X`; old-vertex degrees in (the image of) any `G ⊆ X ∪ R` are bounded by
`fakeBound · mdeg(G, ·)`; sets containing a new vertex have degree at most `fakeBound`. -/
structure ReductionInvariant (q r C : ℕ) (ends : E → Finset V) (K X R : Finset E)
    (𝒲 : Finset (Finset E)) : Prop where
  refiner : IsRefinedRefiner q r (C * fakeBound q r) (gimg q r ends K X) (gimg q r ends K R)
    (𝒲.image (gimg q r ends K))
  base : gimg q r ends K X = X.image (lift q r ends)
  deg_root : ∀ G ⊆ X ∪ R, ∀ S₀ : Finset V,
    deg (gimg q r ends K G) (S₀.map Function.Embedding.inl) ≤ fakeBound q r * mdeg ends G S₀
  deg_fresh : ∀ G ⊆ X ∪ R, ∀ S : Finset (XV V E q r),
    ∀ x : E × Fin (fakeCount q r) × Fin (q - r), (Sum.inr x : XV V E q r) ∈ S →
      deg (gimg q r ends K G) S ≤ fakeBound q r

/-- **Multiplicity reduction.**  A `C`-refined multi-refiner `R` of `X`, with `ends` injective on a
set `K ⊇ X` of kept copies, becomes after replacing every copy outside `K` by a fake edge a
`C · fakeBound(q, r)`-refined refiner (with simple edges) of the lifted `X`, and the degree
invariant of `ReductionInvariant` holds. -/
theorem multiplicityReduction {q r C : ℕ} (hrq : r ≤ q) {ends : E → Finset V}
    {X R : Finset E} {𝒲 : Finset (Finset E)} (h : IsMultiRefiner q r C ends X R 𝒲)
    {K : Finset E} (hXK : X ⊆ K) (hinj : Set.InjOn ends K) :
    ReductionInvariant q r C ends K X R 𝒲 := by
  have hD := h.rgraph
  have hsubD : ∀ {G}, G ⊆ X ∪ R → MIsRGraph r ends G := fun hG i hi => hD i (hG hi)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, gimg_eq_image hXK,
    fun G hG S₀ => deg_gimg_root_le hrq hinj (hsubD hG) S₀,
    fun G hG S x hx => deg_gimg_fresh_le hrq (hsubD hG) hx⟩
  · rw [← gimg_union]; exact IsRGraph_gimg hD
  · exact disjoint_gimg hinj (hsubD subset_union_left) (hsubD subset_union_right) h.disjoint
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    exact isDivisible_gimg hrq hinj (hsubD (h.subset W hW)) (h.divisible W hW)
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    rw [← gimg_union]
    exact gimg_mono (h.subset W hW)
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    refine (card_gimg_le hrq hinj (hsubD (h.subset W hW))).trans ?_
    exact Nat.mul_le_mul_right _ (h.card_le W hW)
  · intro f hf
    rw [← gimg_union] at hf
    obtain ⟨i₀, hi₀, hfi₀⟩ := mem_gimg.1 hf
    have hsub : (𝒲.image (gimg q r ends K)).filter (fun W' => f ∈ W') ⊆
        (𝒲.filter (fun W => i₀ ∈ W)).image (gimg q r ends K) := by
      intro W' hW'
      obtain ⟨hW'm, hfW'⟩ := mem_filter.1 hW'
      obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'm
      obtain ⟨i, hi, hfi⟩ := mem_gimg.1 hfW'
      have := img_unique hinj (hD i (h.subset W hW hi)) (hD i₀ hi₀) hfi hfi₀
      exact mem_image.2 ⟨W, mem_filter.2 ⟨hW, this ▸ hi⟩, rfl⟩
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    exact (h.mult_le i₀ hi₀).trans (Nat.le_mul_of_pos_right _ one_le_fakeBound)
  · intro L' hL' hdiv
    rw [gimg_eq_image hXK] at hL'
    set L := X.filter (fun i => lift q r ends i ∈ L') with hLdef
    have hLX : L ⊆ X := filter_subset _ _
    have hLK : L ⊆ K := hLX.trans hXK
    have hgL : gimg q r ends K L = L' := by
      rw [gimg_eq_image hLK]
      ext f
      simp only [mem_image, hLdef, mem_filter]
      constructor
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩; exact hi
      · intro hf
        obtain ⟨i, hi, rfl⟩ := mem_image.1 (hL' hf)
        exact ⟨i, ⟨hi, hf⟩, rfl⟩
    have hLdiv : MIsDivisible q r ends L := by
      intro S₀ hS₀
      have hdeg : mdeg ends L S₀ = deg L' (S₀.map Function.Embedding.inl) := by
        rw [← hgL, deg_gimg hinj (hsubD (hLX.trans subset_union_left))]
        rw [mdeg, card_eq_sum_ones, sum_filter]
        refine sum_congr rfl fun i hi => ?_
        unfold img
        rw [if_pos (hLK hi), deg, filter_singleton, lift]
        simp only [map_subset_map]
        split_ifs <;> simp
      rw [hdeg]
      have := hdiv (S₀.map Function.Embedding.inl) (by rwa [card_map])
      rwa [card_map] at this
    obtain ⟨𝒰, h𝒰, Res, hRes, -, hpw, -, hsup⟩ := h.decomp L hLX hLdiv
    rw [subset_empty.1 hRes, union_empty] at hsup
    refine ⟨𝒰.image (gimg q r ends K), image_subset_image h𝒰, ?_, ?_⟩
    · intro W₁' hW₁' W₂' hW₂' hne
      obtain ⟨W₁, hW₁, rfl⟩ := mem_image.1 (mem_coe.1 hW₁')
      obtain ⟨W₂, hW₂, rfl⟩ := mem_image.1 (mem_coe.1 hW₂')
      have hne' : W₁ ≠ W₂ := fun h' => hne (h' ▸ rfl)
      exact disjoint_gimg hinj (hsubD (h.subset W₁ (h𝒰 hW₁)))
        (hsubD (h.subset W₂ (h𝒰 hW₂))) (hpw hW₁ hW₂ hne')
    · rw [sup_image_gimg, hsup, gimg_union, hgL]

end RefinedAbsorption.MultiRefiner
