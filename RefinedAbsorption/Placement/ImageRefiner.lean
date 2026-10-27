module
public import RefinedAbsorption.MultiRefiner.Basic

/-!
# Replacing copies of a multi-refiner by simple images

Let `R` be a `C`-refined multi-refiner of `X` (copies labelled by `E`), and let `K ⊇ X` be a set of
kept copies.  Suppose every copy `i` is replaced by a simple `r`-graph `img i`
such that kept copies stay themselves (`img i = {ends i}`), images of distinct copies are
edge-disjoint, every image has at most `B` edges, and every image behaves like `ends i` for
divisibility: `deg(img i, S) ≡ [S ⊆ ends i]` modulo `binom(q-|S|, r-|S|)` for `|S| < r`.  Then the
union of images is a `C · B`-refined (simple) refiner of `X` (`isRefinedRefiner_images`), and the
at-most-one-`X`-edge property of the pieces is preserved (`card_filter_images_le`).

This abstracts the multiplicity reduction from the particular images; it applies both to fake
edges on new vertices and to fake edges placed inside `K_n^r`.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The properties required of the images of the copies. -/
structure IsImageSystem (q r B : ℕ) (ends : E → Finset V) (K D : Finset E)
    (img : E → Finset (Finset V)) : Prop where
  keep : ∀ i ∈ K, img i = {ends i}
  rgraph : ∀ i ∈ D, IsRGraph r (img i)
  disj : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (img i) (img j)
  card_le : ∀ i ∈ D, (img i).card ≤ B
  deg_cast : ∀ i ∈ D, ∀ S : Finset V, S.card < r →
    ((deg (img i) S : ℕ) : ZMod ((q - S.card).choose (r - S.card))) =
      if S ⊆ ends i then 1 else 0

variable {q r B : ℕ} {ends : E → Finset V} {K D : Finset E} {img : E → Finset (Finset V)}

theorem IsImageSystem.unique (h : IsImageSystem q r B ends K D img) {i j : E} (hi : i ∈ D)
    (hj : j ∈ D) {f : Finset V} (hfi : f ∈ img i) (hfj : f ∈ img j) : i = j := by
  by_contra hne
  exact disjoint_left.1 (h.disj i hi j hj hne) hfi hfj

omit [DecidableEq E] in
theorem deg_biUnion_images (h : IsImageSystem q r B ends K D img) {G : Finset E} (hG : G ⊆ D)
    (S : Finset V) : deg (G.biUnion img) S = ∑ i ∈ G, deg (img i) S := by
  unfold deg
  rw [filter_biUnion, card_biUnion]
  intro i hi j hj hne
  exact disjoint_filter_filter (h.disj i (hG hi) j (hG hj) hne)

omit [DecidableEq E] in
theorem isDivisible_images (h : IsImageSystem q r B ends K D img) {G : Finset E} (hG : G ⊆ D)
    (hdiv : MIsDivisible q r ends G) : IsDivisible q r (G.biUnion img) := by
  intro S hS
  rw [← ZMod.natCast_eq_zero_iff, deg_biUnion_images h hG, Nat.cast_sum,
    sum_congr rfl (fun i hi => h.deg_cast i (hG hi) S hS), ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one]
  exact (ZMod.natCast_eq_zero_iff _ _).2 (hdiv S hS)

theorem disjoint_images (h : IsImageSystem q r B ends K D img) {G H : Finset E} (hG : G ⊆ D)
    (hH : H ⊆ D) (hGH : Disjoint G H) : Disjoint (G.biUnion img) (H.biUnion img) := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
  obtain ⟨j, hj, hfj⟩ := mem_biUnion.1 hf'
  have := h.unique (hG hi) (hH hj) hfi hfj
  subst this
  exact disjoint_left.1 hGH hi hj

omit [DecidableEq E] in
theorem images_eq_image (h : IsImageSystem q r B ends K D img) {G : Finset E} (hGK : G ⊆ K) :
    G.biUnion img = G.image ends := by
  ext f
  simp only [mem_biUnion, mem_image]
  constructor
  · rintro ⟨i, hi, hf⟩
    rw [h.keep i (hGK hi), mem_singleton] at hf
    exact ⟨i, hi, hf.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [h.keep i (hGK hi)]; exact mem_singleton_self _⟩

theorem sup_image_biUnion (𝒰 : Finset (Finset E)) :
    (𝒰.image fun W => W.biUnion img).sup id = (𝒰.sup id).biUnion img := by
  ext f
  simp only [mem_sup, mem_image, id, mem_biUnion]
  constructor
  · rintro ⟨_, ⟨W, hW, rfl⟩, hf⟩
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact ⟨i, ⟨W, hW, hi⟩, hfi⟩
  · rintro ⟨i, ⟨W, hW, hi⟩, hfi⟩
    exact ⟨_, ⟨W, hW, rfl⟩, mem_biUnion.2 ⟨i, hi, hfi⟩⟩

/-- **Images of a multi-refiner form a simple refined refiner.** -/
theorem isRefinedRefiner_images {C : ℕ} {X R : Finset E} {𝒲 : Finset (Finset E)}
    (hR : IsMultiRefiner q r C ends X R 𝒲) (hXK : X ⊆ K)
    (h : IsImageSystem q r B ends K (X ∪ R) img) (hB : 1 ≤ B) :
    IsRefinedRefiner q r (C * B) (X.image ends) (R.biUnion img)
      (𝒲.image fun W => W.biUnion img) := by
  have hXi : X.biUnion img = X.image ends := images_eq_image h hXK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hXi, ← union_biUnion]
    intro f hf
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact h.rgraph i hi f hfi
  · rw [← hXi]
    exact disjoint_images h subset_union_left subset_union_right hR.disjoint
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    exact isDivisible_images h (hR.subset W hW) (hR.divisible W hW)
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    rw [← hXi, ← union_biUnion]
    exact biUnion_subset_biUnion_of_subset_left _ (hR.subset W hW)
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    refine card_biUnion_le.trans ?_
    calc ∑ i ∈ W, (img i).card ≤ ∑ _i ∈ W, B :=
          sum_le_sum fun i hi => h.card_le i (hR.subset W hW hi)
      _ = W.card * B := by rw [sum_const, smul_eq_mul]
      _ ≤ C * B := Nat.mul_le_mul_right _ (hR.card_le W hW)
  · intro f hf
    rw [← hXi, ← union_biUnion] at hf
    obtain ⟨i₀, hi₀, hfi₀⟩ := mem_biUnion.1 hf
    have hsub : (𝒲.image fun W => W.biUnion img).filter (fun W' => f ∈ W') ⊆
        (𝒲.filter (fun W => i₀ ∈ W)).image (fun W => W.biUnion img) := by
      intro W' hW'
      obtain ⟨hW'm, hfW'⟩ := mem_filter.1 hW'
      obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'm
      obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hfW'
      have := h.unique (hR.subset W hW hi) hi₀ hfi hfi₀
      exact mem_image.2 ⟨W, mem_filter.2 ⟨hW, this ▸ hi⟩, rfl⟩
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    exact (hR.mult_le i₀ hi₀).trans (Nat.le_mul_of_pos_right _ hB)
  · intro L' hL' hdiv
    rw [← hXi] at hL'
    set L := X.filter (fun i => ends i ∈ L') with hLdef
    have hLX : L ⊆ X := filter_subset _ _
    have hLK : L ⊆ K := hLX.trans hXK
    have hgL : L.biUnion img = L' := by
      rw [images_eq_image h hLK]
      ext f
      simp only [mem_image, hLdef, mem_filter]
      constructor
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩; exact hi
      · intro hf
        rw [hXi] at hL'
        obtain ⟨i, hi, rfl⟩ := mem_image.1 (hL' hf)
        exact ⟨i, ⟨hi, hf⟩, rfl⟩
    have hLdiv : MIsDivisible q r ends L := by
      intro S₀ hS₀
      have hdeg : mdeg ends L S₀ = deg L' S₀ := by
        rw [← hgL, deg_biUnion_images h (hLX.trans subset_union_left)]
        rw [mdeg, card_eq_sum_ones, sum_filter]
        refine sum_congr rfl fun i hi => ?_
        rw [h.keep i (hLK hi), deg, filter_singleton]
        split_ifs <;> simp
      rw [hdeg]
      exact hdiv S₀ hS₀
    obtain ⟨𝒰, h𝒰, Res, hRes, -, hpw, -, hsup⟩ := hR.decomp L hLX hLdiv
    rw [subset_empty.1 hRes, union_empty] at hsup
    refine ⟨𝒰.image fun W => W.biUnion img, image_subset_image h𝒰, ?_, ?_⟩
    · intro W₁' hW₁' W₂' hW₂' hne
      obtain ⟨W₁, hW₁, rfl⟩ := mem_image.1 (mem_coe.1 hW₁')
      obtain ⟨W₂, hW₂, rfl⟩ := mem_image.1 (mem_coe.1 hW₂')
      have hne' : W₁ ≠ W₂ := fun h' => hne (h' ▸ rfl)
      exact disjoint_images h (hR.subset W₁ (h𝒰 hW₁)) (hR.subset W₂ (h𝒰 hW₂)) (hpw hW₁ hW₂ hne')
    · rw [sup_image_biUnion, hsup, union_biUnion, hgL]

/-- The at-most-one-`X`-edge property survives taking images. -/
theorem card_filter_images_le {X W : Finset E} (hXK : X ⊆ K)
    (h : IsImageSystem q r B ends K D img) (hWD : W ⊆ D) (hXD : X ⊆ D) :
    ((W.biUnion img).filter (· ∈ X.image ends)).card ≤ (W.filter (· ∈ X)).card := by
  refine (card_le_card ?_).trans (card_image_le (f := ends))
  intro f hf
  obtain ⟨hfW, hfX⟩ := mem_filter.1 hf
  obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hfW
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hfX
  have hfj : ends j ∈ img j := by rw [h.keep j (hXK hj)]; exact mem_singleton_self _
  have := h.unique (hWD hi) (hXD hj) hfi hfj
  subst this
  exact mem_image.2 ⟨i, mem_filter.2 ⟨hi, hj⟩, rfl⟩

end RefinedAbsorption.Placement
