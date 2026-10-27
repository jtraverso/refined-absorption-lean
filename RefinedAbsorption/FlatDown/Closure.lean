module
public import RefinedAbsorption.FlatDown.FlatProof
public import RefinedAbsorption.FlatDown.Small

/-!
# Closing the residue: multi-refiners with empty residue

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, Sections 3–4).  Lean
formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Given a reserve `Z` of `q + r` vertices:

* the anti-edge step (`antiEdgeStep_reserve`) makes the residue `(r-1)`-flat with respect to `Z`;
* `flatStep` lowers flatness one unit at a time, the links being refined inside `Z` by
  `smallRefiner` in lower uniformity (a link inside a set of `q + r` vertices has at most
  `2^(q+r)` distinct edges);
* at flatness `0` the residue lies inside `Z` and `smallRefiner` removes it.

`multiRefiner_exists`: for `1 ≤ r < q` there is a constant `C` such that **every** finite
`r`-multigraph `X` on a vertex set containing `q + r` vertices has a `K_q^r`-multi-refiner with
**empty residue** and constant `C` (after an injective relabelling of the copies).
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.RefineDown

/-- **Composition along a relabelling**: a residual refiner of `X` with residue `Y`, followed by
a multi-refiner of the relabelled residue, gives a multi-refiner of the relabelled `X`. -/
theorem compose_relabel {V E₁ E' : Type*} [DecidableEq V] [DecidableEq E₁] [DecidableEq E']
    {q r C₁ C₂ : ℕ} {ends₁ : E₁ → Finset V} {X R₁ Y : Finset E₁} {𝒲₁ : Finset (Finset E₁)}
    (h₁ : IsResidualMultiRefiner q r C₁ ends₁ X R₁ Y 𝒲₁) (hY : Y ⊆ X ∪ R₁)
    {g : E₁ → E'} (hg : Function.Injective g) {ends' : E' → Finset V}
    (hends : ∀ c, ends' (g c) = ends₁ c) {R₂ : Finset E'} {𝒲₂ : Finset (Finset E')}
    (h₂ : IsMultiRefiner q r C₂ ends' (Y.image g) R₂ 𝒲₂) (hR₂ : ∀ c ∈ R₂, ∀ x, g x ≠ c) :
    IsMultiRefiner q r (C₁ + C₂) ends' (X.image g) (R₁.image g ∪ R₂)
      (𝒲₁.image (image g) ∪ 𝒲₂) := by
  have h₁' := residual_relabel h₁ g ends' (fun c _ => hends c) hg.injOn hY
  refine h₁'.trans h₂ ?_ ?_
  · rw [← image_union]; exact image_subset_image hY
  · rw [disjoint_left]
    intro c hc hc'
    rw [← image_union] at hc'
    obtain ⟨x, -, rfl⟩ := mem_image.1 hc'
    exact hR₂ _ hc x rfl

/-- **Relabelling the new copies of a multi-refiner by natural numbers.** -/
theorem relabel_nat {V E N' : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq N']
    {q r C : ℕ} {e : E → Finset V} {endsN' : N' → Finset V} {X : Finset E} {R' : Finset N'}
    {𝒲' : Finset (Finset (E ⊕ N'))}
    (h : IsMultiRefiner q r C (Sum.elim e endsN') (X.image Sum.inl) (R'.image Sum.inr) 𝒲') :
    ∃ (endsℕ : ℕ → Finset V) (Rℕ : Finset ℕ) (𝒲ℕ : Finset (Finset (E ⊕ ℕ))),
      (∀ n ∈ Rℕ, ∃ y ∈ R', endsℕ n = endsN' y) ∧
      IsMultiRefiner q r C (Sum.elim e endsℕ) (X.image Sum.inl) (Rℕ.image Sum.inr) 𝒲ℕ := by
  classical
  let f : N' → ℕ := fun y => if hy : y ∈ R' then (R'.equivFin ⟨y, hy⟩ : ℕ) else 0
  let endsℕ : ℕ → Finset V := fun n =>
    if hn : n < R'.card then endsN' (R'.equivFin.symm ⟨n, hn⟩) else ∅
  have hf : ∀ y ∈ R', endsℕ (f y) = endsN' y := by
    intro y hy
    have hlt : (R'.equivFin ⟨y, hy⟩ : ℕ) < R'.card := (R'.equivFin ⟨y, hy⟩).2
    simp only [endsℕ, f, dif_pos hy, dif_pos hlt]
    congr 1
    rw [show (⟨(R'.equivFin ⟨y, hy⟩ : ℕ), hlt⟩ : Fin R'.card) = R'.equivFin ⟨y, hy⟩ from rfl,
      Equiv.symm_apply_apply]
  have hfinj : Set.InjOn f R' := by
    intro y hy y' hy' h
    simp only [f, dif_pos (mem_coe.1 hy), dif_pos (mem_coe.1 hy')] at h
    have := R'.equivFin.injective (Fin.ext h)
    simpa using this
  let g : E ⊕ N' → E ⊕ ℕ := Sum.map id f
  have hends : ∀ c ∈ X.image Sum.inl ∪ R'.image Sum.inr,
      Sum.elim e endsℕ (g c) = Sum.elim e endsN' c := by
    intro c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hc; rfl
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
      exact hf y hy
  have hginj : Set.InjOn g ↑(X.image Sum.inl ∪ R'.image Sum.inr) := by
    intro c hc c' hc' h
    simp only [coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hc hc'
    rcases hc with ⟨x, -, rfl⟩ | ⟨y, hy, rfl⟩ <;> rcases hc' with ⟨x', -, rfl⟩ | ⟨y', hy', rfl⟩
    · simpa [g] using h
    · simp [g] at h
    · simp [g] at h
    · simp only [g, Sum.map_inr, Sum.inr.injEq] at h
      rw [hfinj hy hy' h]
  have h' := residual_relabel h g (Sum.elim e endsℕ) hends hginj (empty_subset _)
  refine ⟨endsℕ, R'.image f, 𝒲'.image (image g), ?_, ?_⟩
  · intro n hn
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hn
    exact ⟨y, hy, hf y hy⟩
  · have e1 : (X.image Sum.inl).image g = X.image Sum.inl := by
      rw [image_image]; rfl
    have e2 : (R'.image Sum.inr).image g = (R'.image f).image Sum.inr := by
      rw [image_image, image_image]; rfl
    rw [e1, e2, image_empty] at h'
    exact h'

/-- **Link refiners inside a reserve of `q + r` vertices**, from `smallRefiner` in uniformity
`r - i`: a link inside `Z` has at most `2^(q+r)` distinct edges. -/
theorem linkRefiners_small (q r i : ℕ) (hir : i < r) (hrq : r < q) : ∃ Cl : ℕ,
    ∀ {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Finset V) (Z : Finset V),
      Z.card = q + r → ∀ X : Finset E, MIsRGraph r ends X →
      ∃ (endsN : Finset V → ℕ → Finset V) (RN : Finset V → Finset ℕ)
        (𝒲 : Finset V → Finset (Finset (E ⊕ ℕ))), LinkRefiners q r i Cl ends Z X endsN RN 𝒲 := by
  obtain ⟨Cl, hCl⟩ := smallRefiner (q - i) (r - i) (2 ^ (q + r)) (by omega)
  refine ⟨Cl, ?_⟩
  intro V E _ _ ends Z hZ X hX
  have hex : ∀ T ∈ outParts ends Z i X, ∃ (eN : ℕ → Finset V) (RT : Finset ℕ)
      (WT : Finset (Finset (E ⊕ ℕ))), (∀ n ∈ RT, eN n ⊆ Z) ∧
      IsMultiRefiner (q - i) (r - i) Cl (Sum.elim (lk ends Z) eN)
        ((lnk ends Z X T).image Sum.inl) (RT.image Sum.inr) WT := by
    intro T hT
    have hrg : MIsRGraph (r - i) (lk ends Z) (lnk ends Z X T) := by
      intro x hx
      obtain ⟨hxX, hxT⟩ := mem_filter.1 hx
      have h1 := card_sdiff_add_card_inter (ends x) Z
      rw [hxT, (outParts_card hT).1, hX x hxX] at h1
      show (ends x ∩ Z).card = r - i
      omega
    have hcard : ((lnk ends Z X T).image (lk ends Z)).card ≤ 2 ^ (q + r) := by
      rw [← hZ, ← card_powerset]
      refine card_le_card ?_
      intro s hs
      obtain ⟨x, -, rfl⟩ := mem_image.1 hs
      exact mem_powerset.2 inter_subset_right
    obtain ⟨N', _, endsN', R', 𝒲', hin, href⟩ := hCl (lk ends Z) (lnk ends Z X T) hrg hcard
    obtain ⟨eN, RT, WT, hrel, h⟩ := relabel_nat href
    refine ⟨eN, RT, WT, fun n hn => ?_, h⟩
    obtain ⟨y, hy, hny⟩ := hrel n hn
    obtain ⟨x, -, hx⟩ := mem_image.1 (hin y hy)
    rw [hny, ← hx]
    exact inter_subset_right
  choose! eN RT WT hZin href using hex
  exact ⟨eN, RT, WT, ⟨href, hZin⟩⟩

/-- **Refine down from `i`-flat to empty residue.**  For `i < r < q` there is a constant `C`
such that every `i`-flat `r`-multigraph (with respect to a reserve `Z` of `q + r` vertices) has,
after an injective relabelling, a `K_q^r`-multi-refiner with empty residue and constant `C`,
whose new copies are disjoint from the relabelled old ones. -/
theorem flatDown (q r : ℕ) (hrq : r < q) : ∀ i, i < r → ∃ C : ℕ,
    ∀ {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Finset V) (Z : Finset V),
      Z.card = q + r → ∀ Y : Finset E, MIsRGraph r ends Y → IsFlat i Z ends Y →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset V) (R : Finset E')
        (𝒲 : Finset (Finset E')), Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧
        (∀ c ∈ R, ∀ x, g x ≠ c) ∧ IsMultiRefiner q r C ends' (Y.image g) R 𝒲 := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨C, hC⟩ := smallRefiner q r (2 ^ (q + r)) hrq.le
    refine ⟨C, ?_⟩
    intro V E _ _ ends Z hZ Y hY hflat
    have hcard : (Y.image ends).card ≤ 2 ^ (q + r) := by
      rw [← hZ, ← card_powerset]
      refine card_le_card ?_
      intro s hs
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hs
      have := hflat y hy
      rw [Nat.le_zero, card_eq_zero, sdiff_eq_empty_iff_subset] at this
      exact mem_powerset.2 this
    obtain ⟨N, _, endsN, R, 𝒲, -, h⟩ := hC ends Y hY hcard
    refine ⟨E ⊕ N, inferInstance, Sum.inl, Sum.elim ends endsN, R.image Sum.inr, 𝒲,
      Sum.inl_injective, fun c => rfl, ?_, h⟩
    intro c hc x hx
    obtain ⟨y, -, rfl⟩ := mem_image.1 hc
    simp at hx
  | succ i ih =>
    intro hi
    obtain ⟨C, hC⟩ := ih (by omega)
    obtain ⟨Cl, hCl⟩ := linkRefiners_small q r (i + 1) hi hrq
    refine ⟨flatConst q r Cl + C, ?_⟩
    intro V E _ _ ends Z hZ Y hY hflat
    obtain ⟨endsN, RN, 𝒲, hL⟩ := hCl ends Z hZ Y hY
    obtain ⟨R₁, Y₁, 𝒲₁, h₁, hflat₁, -, hY₁, hR₁, -⟩ :=
      flatStep (Z₀ := fun _ _ => Z) hi hrq hY hflat hL (fun _ _ => subset_rfl) (fun _ _ => hZ)
    have hrg₁ : MIsRGraph r (fEnds ends endsN) Y₁ := fun c hc => h₁.rgraph c (hY₁ hc)
    rw [Nat.add_sub_cancel] at hflat₁
    obtain ⟨E', _, g, ends', R₂, 𝒲₂, hg, hends, hR₂, h₂⟩ :=
      hC (fEnds ends endsN) Z hZ Y₁ hrg₁ hflat₁
    have h := compose_relabel h₁ hY₁ hg hends h₂ hR₂
    refine ⟨E', inferInstance, g ∘ Sum.inl, ends', R₁.image g ∪ R₂, 𝒲₁.image (image g) ∪ 𝒲₂,
      hg.comp Sum.inl_injective, fun c => hends _, ?_, ?_⟩
    · intro c hc x hx
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hR₁ c₁ hc₁ x (hg hx).symm
      · exact hR₂ c hc _ hx
    · rw [← image_image]; exact h

/-- **Multi-refiners with empty residue.**  For `1 ≤ r < q` there is a constant `C` such that
every finite `r`-multigraph `X` on a vertex set containing a set `Z` of `q + r` vertices has,
after an injective relabelling `g` of the copies (preserving their vertex sets), a
`K_q^r`-multi-refiner with empty residue and constant `C`.  `C` depends only on `q` and `r`. -/
theorem multiRefiner_exists (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) : ∃ C : ℕ,
    ∀ {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Finset V) (Z : Finset V),
      Z.card = q + r → ∀ X : Finset E, MIsRGraph r ends X →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset V) (R : Finset E')
        (𝒲 : Finset (Finset E')), Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧
        IsMultiRefiner q r C ends' (X.image g) R 𝒲 := by
  obtain ⟨C, hC⟩ := flatDown q r hrq (r - 1) (by omega)
  refine ⟨1 + q.choose r * fakeModulus q r + 2 + C, ?_⟩
  intro V E _ _ ends Z hZ X hX
  have hQex : ∀ x ∈ X, ∃ Qx ⊆ Z \ ends x, Qx.card = q - r := by
    intro x hx
    refine exists_subset_card_eq ?_
    have := le_card_sdiff (ends x) Z
    rw [hZ, hX x hx] at this
    omega
  choose! Q hQsub hQcard using hQex
  have hQ : ∀ x ∈ X, Q x ⊆ Z ∧ Disjoint (ends x) (Q x) ∧ (Q x).card = q - r := by
    intro x hx
    refine ⟨(hQsub x hx).trans sdiff_subset, ?_, hQcard x hx⟩
    exact disjoint_of_subset_right (hQsub x hx) disjoint_sdiff
  obtain ⟨h₁, hsub, hflat, -⟩ := antiEdgeStep_reserve (Q := Q) hrq hX hQ
  set Y := (aY r ends Q X (fakeModulus q r)).image (Sum.inr : ALab E V → E ⊕ ALab E V) with hYdef
  have hY : Y ⊆ X.image Sum.inl ∪ (aR r ends Q X (fakeModulus q r)).image Sum.inr :=
    (image_subset_image hsub).trans subset_union_right
  have hrgY : MIsRGraph r (aEnds ends) Y := fun c hc => h₁.rgraph c (hY hc)
  have hflatY : IsFlat (r - 1) Z (aEnds ends) Y := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    exact hflat y hy
  obtain ⟨E', _, g, ends', R₂, 𝒲₂, hg, hends, hR₂, h₂⟩ := hC (aEnds ends) Z hZ Y hrgY hflatY
  have h := compose_relabel h₁ hY hg hends h₂ hR₂
  rw [image_image] at h
  exact ⟨E', inferInstance, g ∘ Sum.inl, ends', _, _, hg.comp Sum.inl_injective,
    fun c => hends _, h⟩

end RefinedAbsorption.FlatDown
