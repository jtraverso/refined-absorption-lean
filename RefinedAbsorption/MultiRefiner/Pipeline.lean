module
public import RefinedAbsorption.MultiRefiner.Reduction
public import RefinedAbsorption.Absorber17.Library

/-!
# From multi-refiners to refined omni-absorbers (on an extended vertex set)

Chaining multiplicity reduction (`multiplicityReduction`), the uniform absorber library
(`exists_boundedAttachedAbsorbers`) and the combination step `omniAbsorber_of_refiner_absorbers`:
a `C`-refined multi-refiner of `X` yields a `2 C fakeBound`-refined `K_q^r`-omni-absorber for
(the lifted copy of) `X`, on the vertex set extended by the new vertices of the fake edges and of
the absorbers.

The degree invariant is kept explicit (`omniAbsorber_of_multiRefiner`): for every set `S₀` of old
vertices,
`deg(A, S₀) ≤ fakeBound · mdeg(R, S₀) + B · #{W ∈ 𝒲 : S₀ ⊆ V(W)}`,
where `B = B(q, r, C · fakeBound)` is the uniform absorber bound.  Bringing this down to
`C · max(D, n^{1-1/r} log n)` inside `K_n^r` (the degree budget of Theorem 1.10, i.e.
`RefinerAbsorbersFor q r`) requires embedding the new vertices into `K_n^r` and refiners with the
right degree budget; this is not done here, so the global theorem remains open.
-/

@[expose] public section

set_option synthInstance.maxSize 4096

namespace RefinedAbsorption.MultiRefiner

open Finset Absorber17

section gmap

variable {U W : Type*} [DecidableEq U] [DecidableEq W]

theorem sup_image_gmap (f : U ↪ W) (𝒰 : Finset (Finset (Finset U))) :
    (𝒰.image (RefinedAbsorption.gmap f)).sup id = RefinedAbsorption.gmap f (𝒰.sup id) := by
  ext e
  simp only [mem_sup, mem_image, id, mem_gmap]
  constructor
  · rintro ⟨_, ⟨P, hP, rfl⟩, he⟩
    obtain ⟨e₀, he₀, rfl⟩ := mem_gmap.1 he
    exact ⟨e₀, ⟨P, hP, he₀⟩, rfl⟩
  · rintro ⟨e₀, ⟨P, hP, he₀⟩, rfl⟩
    exact ⟨_, ⟨P, hP, rfl⟩, map_mem_gmap.2 he₀⟩

/-- Refined refiners are transported along injective vertex maps. -/
theorem _root_.RefinedAbsorption.IsRefinedRefiner.gmap {q r C : ℕ} {X R : Finset (Finset U)}
    {𝒲 : Finset (Finset (Finset U))} (h : IsRefinedRefiner q r C X R 𝒲) (f : U ↪ W) :
    IsRefinedRefiner q r C (RefinedAbsorption.gmap f X) (RefinedAbsorption.gmap f R)
      (𝒲.image (RefinedAbsorption.gmap f)) := by
  refine ⟨?_, (disjoint_gmap f).2 h.disjoint, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← gmap_union]; exact h.rgraph.gmap f
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hP'
    exact (h.divisible P hP).gmap f
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hP'
    rw [← gmap_union]; exact gmap_mono f (h.subset P hP)
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hP'
    rw [card_gmap]; exact h.card_le P hP
  · intro e' he'
    rw [← gmap_union] at he'
    obtain ⟨e, he, rfl⟩ := mem_gmap.1 he'
    have hsub : (𝒲.image (RefinedAbsorption.gmap f)).filter (fun P' => e.map f ∈ P') ⊆
        (𝒲.filter (fun P => e ∈ P)).image (RefinedAbsorption.gmap f) := by
      intro P' hP'
      obtain ⟨hP'm, heP'⟩ := mem_filter.1 hP'
      obtain ⟨P, hP, rfl⟩ := mem_image.1 hP'm
      exact mem_image.2 ⟨P, mem_filter.2 ⟨hP, map_mem_gmap.1 heP'⟩, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (h.mult_le e he))
  · intro L' hL' hdiv
    set L := X.filter (fun e => e.map f ∈ L') with hLdef
    have hgL : RefinedAbsorption.gmap f L = L' := by
      ext e'
      simp only [mem_gmap, hLdef, mem_filter]
      constructor
      · rintro ⟨e, ⟨-, he⟩, rfl⟩; exact he
      · intro he'
        obtain ⟨e, he, rfl⟩ := mem_gmap.1 (hL' he')
        exact ⟨e, ⟨he, he'⟩, rfl⟩
    have hLdiv : IsDivisible q r L := by
      intro S hS
      rw [← deg_gmap_map f, hgL]
      have := hdiv (S.map f) (by rwa [card_map])
      rwa [card_map] at this
    obtain ⟨𝒰, h𝒰, hpw, hsup⟩ := h.decomp L (filter_subset _ _) hLdiv
    refine ⟨𝒰.image (RefinedAbsorption.gmap f), image_subset_image h𝒰, ?_, ?_⟩
    · intro P₁' hP₁' P₂' hP₂' hne
      obtain ⟨P₁, hP₁, rfl⟩ := mem_image.1 (mem_coe.1 hP₁')
      obtain ⟨P₂, hP₂, rfl⟩ := mem_image.1 (mem_coe.1 hP₂')
      exact (disjoint_gmap f).2 (hpw hP₁ hP₂ fun h' => hne (h' ▸ rfl))
    · rw [sup_image_gmap, hsup, gmap_union, hgL]

end gmap

/-- The final vertex type: old vertices, new vertices of the fake edges, new vertices of the
absorbers. -/
abbrev OV (V E : Type) (q r : ℕ) := XV V E q r ⊕ (Finset (Finset (XV V E q r)) × ℕ)

/-- Old vertices inside the final vertex type. -/
def oldEmb (V E : Type) (q r : ℕ) : V ↪ OV V E q r :=
  Function.Embedding.inl.trans Function.Embedding.inl

theorem deg_sup_le {U ι : Type*} [DecidableEq U] [DecidableEq ι] (s : Finset ι)
    (G : ι → Finset (Finset U)) (S : Finset U) : deg (s.sup G) S ≤ ∑ i ∈ s, deg (G i) S := by
  rw [deg, sup_eq_biUnion, filter_biUnion]
  exact card_biUnion_le

/-- **Multi-refiner ⇒ refined omni-absorber, with explicit degree invariant.**  Fix
`q > r ≥ 1` and `C ≥ 1`.  There is `B` such that: for every `C`-refined multi-refiner `R` of `X`
with family `𝒲`, and every set `K ⊇ X` of kept copies on which `ends` is injective, there is a
`2 C fakeBound`-refined `K_q^r`-omni-absorber `A` for the lifted copy of `X` (on the extended
vertex type `OV`), such that for every set `S₀` of old vertices
`deg(A, S₀) ≤ fakeBound · mdeg(R, S₀) + B · #{W ∈ 𝒲 : S₀ ⊆ ⋃_{i ∈ W} ends i}`. -/
theorem omniAbsorber_of_multiRefiner {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (C : ℕ) (hC : 1 ≤ C) :
    ∃ B : ℕ, ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (ends : E → Finset V)
      (X R K : Finset E) (𝒲 : Finset (Finset E)), IsMultiRefiner q r C ends X R 𝒲 → X ⊆ K →
      Set.InjOn ends K →
      ∃ (A F : Finset (Finset (OV V E q r))) (QA : Finset (Finset (OV V E q r)) →
          Finset (Finset (OV V E q r))),
        IsOmniAbsorber q r (X.image fun i => (ends i).map (oldEmb V E q r)) A F QA ∧
        IsCRefined (2 * (C * fakeBound q r)) (X.image fun i => (ends i).map (oldEmb V E q r)) A F ∧
        ∀ S₀ : Finset V, deg A (S₀.map (oldEmb V E q r)) ≤
          fakeBound q r * mdeg ends R S₀ + B * (𝒲.filter fun W => S₀ ⊆ W.biUnion ends).card := by
  obtain ⟨B, hB⟩ := exists_boundedAttachedAbsorbers hr hrq (C * fakeBound q r)
  refine ⟨B, fun V E _ _ ends X R K 𝒲 h hXK hinj => ?_⟩
  have hred := multiplicityReduction hrq.le h hXK hinj
  have ref := hred.refiner
  set X' := gimg q r ends K X
  set R' := gimg q r ends K R
  set 𝒲' := 𝒲.image (gimg q r ends K)
  obtain ⟨A, Qon, Qoff, hatt, hbd⟩ :=
    hB (XV V E q r) X' R' 𝒲' ref.rgraph ref.subset ref.divisible ref.card_le
  have hC' : 1 ≤ C * fakeBound q r := Nat.mul_le_mul hC one_le_fakeBound
  obtain ⟨QA, homni, href⟩ :=
    omniAbsorber_of_refiner_absorbers hrq.le hC' (ref.gmap Function.Embedding.inl) hatt
  have hXimg : RefinedAbsorption.gmap Function.Embedding.inl X' =
      X.image fun i => (ends i).map (oldEmb V E q r) := by
    change RefinedAbsorption.gmap _ (gimg q r ends K X) = _
    rw [hred.base]
    ext e
    simp only [mem_gmap, mem_image, lift, oldEmb]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, by rw [map_map]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, by rw [map_map]⟩
  rw [hXimg] at homni href
  refine ⟨_, _, QA, homni, href, fun S₀ => ?_⟩
  set S := S₀.map (oldEmb V E q r) with hS
  -- the refiner part
  have h1 : deg (RefinedAbsorption.gmap Function.Embedding.inl R') S ≤
      fakeBound q r * mdeg ends R S₀ := by
    have : S = (S₀.map Function.Embedding.inl).map Function.Embedding.inl := by
      rw [hS, oldEmb, map_map]
    rw [this, deg_gmap_map]
    exact hred.deg_root R subset_union_right S₀
  -- the absorber part
  have hterm : ∀ W ∈ 𝒲, deg (A (RefinedAbsorption.gmap Function.Embedding.inl
      (gimg q r ends K W))) S ≤ if S₀ ⊆ W.biUnion ends then B else 0 := by
    intro W hW
    have hW' : gimg q r ends K W ∈ 𝒲' := mem_image_of_mem _ hW
    obtain ⟨hbA, hvA⟩ := hbd _ hW'
    split_ifs with hS₀
    · exact (card_le_card (filter_subset _ _)).trans hbA.card_edges
    · rw [deg, card_eq_zero.2 (filter_eq_empty_iff.2 ?_)]
      intro f hf hSf
      apply hS₀
      intro v hv
      have hx : (oldEmb V E q r) v ∈ f := hSf (mem_map_of_mem _ hv)
      rcases mem_union.1 (hvA (subset_vertexSet hf hx)) with h' | h'
      · rw [vertexSet_gmap] at h'
        obtain ⟨y, hy, hyv⟩ := mem_map.1 h'
        simp only [oldEmb, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
          Sum.inl.injEq] at hyv
        subst hyv
        obtain ⟨g, hg, hvg⟩ := mem_sup.1 hy
        obtain ⟨i, hi, hgi⟩ := mem_gimg.1 hg
        exact mem_biUnion.2 ⟨i, hi, img_inl hgi hvg⟩
      · obtain ⟨j, -, hj⟩ := mem_image.1 h'
        simp [oldEmb] at hj
  have h2 : deg ((𝒲'.image (RefinedAbsorption.gmap Function.Embedding.inl)).sup A) S ≤
      B * (𝒲.filter fun W => S₀ ⊆ W.biUnion ends).card := by
    refine (deg_sup_le _ _ _).trans ?_
    rw [image_image]
    refine (sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)).trans ?_
    refine (sum_le_sum fun W hW => hterm W hW).trans ?_
    rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  calc deg (RefinedAbsorption.gmap Function.Embedding.inl R' ∪
        (𝒲'.image (RefinedAbsorption.gmap Function.Embedding.inl)).sup A) S
      ≤ deg (RefinedAbsorption.gmap Function.Embedding.inl R') S +
        deg ((𝒲'.image (RefinedAbsorption.gmap Function.Embedding.inl)).sup A) S := by
        rw [deg, deg, deg, filter_union]; exact card_union_le _ _
    _ ≤ _ := Nat.add_le_add h1 h2

end RefinedAbsorption.MultiRefiner
