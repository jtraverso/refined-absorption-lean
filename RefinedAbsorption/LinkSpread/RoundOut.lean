module
public import RefinedAbsorption.LinkSpread.Comp
public import RefinedAbsorption.LinkSpread.Round

/-!
# The tagged round as a tagged output

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`taggedRound` places the anti-edge round of all fibres at once.  Here its conclusion is packaged as
a `TaggedOutE`: for every tag `T` the round of the fibre of `T` is a residual refiner whose residue
is `(r - i - 1)`-flat with respect to the target reserve `Z`, with new copies inside the current
reserve `Zo`, and with lifted degrees and lifted piece degrees `≤ C · D`
(**`taggedRoundOut`**).
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- Summing over the fibres of a tag map. -/
theorem sum_fibre_sum {n : ℕ} {E : Type} {tg : E → Finset (Fin n)} (X : Finset E)
    (h : E → ℕ) : ∑ T ∈ X.image tg, ∑ x ∈ fibre tg X T, h x = ∑ x ∈ X, h x :=
  sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem _ hx) h

/-- A nonempty union of sets each containing `T`. -/
theorem biUnion_union_left_of_ne {V E : Type} [DecidableEq V] {W : Finset E} (hW : W.Nonempty)
    (T : Finset V) (f : E → Finset V) : W.biUnion (fun c => T ∪ f c) = T ∪ W.biUnion f := by
  obtain ⟨c₀, hc₀⟩ := hW
  ext v
  simp only [mem_biUnion, mem_union]
  constructor
  · rintro ⟨c, hc, hv | hv⟩
    · exact Or.inl hv
    · exact Or.inr ⟨c, hc, hv⟩
  · rintro (hv | ⟨c, hc, hv⟩)
    · exact ⟨c₀, hc₀, Or.inl hv⟩
    · exact ⟨c, hc, Or.inr hv⟩

set_option maxHeartbeats 1000000 in
/-- **The tagged round as a tagged output.** -/
theorem taggedRoundOut (q r i : ℕ) (hir : i + 1 < r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (tg bd : E → Finset (Fin n))
      (Zo Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) → C ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        mdeg (liftEnds tg bd) X J ≤ D * Z.card ^ (r - 1 - J.card)) →
      TaggedOutE q r i (r - i - 1) C tg bd Zo Z X (C * D) := by
  obtain ⟨C, hC, hround⟩ := taggedRound (q - i) (r - i) i (by omega) (by omega)
  refine ⟨2 * C, by omega, ?_⟩
  intro n E _ tg bd Zo Z X D hZ htg hbd htgc hbdc hCZ hXJ
  have hik : i + (r - i) - 1 = r - 1 := by omega
  obtain ⟨j₀, ends', A, hinl, hres, hA, hEd, hpieces, hdegA, hdegE⟩ :=
    hround n tg bd X Z D hbdc htgc (fun x hx => disjoint_of_subset_right (hbd x) (htg x))
      (by omega) (fun J hJ => by rw [hik] at hJ ⊢; exact hXJ J hJ)
  -- the copies of `stepR` and `stepY`
  have hmemR : ∀ (X₀ : Finset E) (c : SC (Fin n) E (q - i) (r - i)),
      c ∈ stepR (q - i) (r - i) bd j₀ X₀ → ∃ x ∈ X₀, ∃ f ∈ Gen.Ed (q - i) (r - i) bd j₀ x,
        c = Sum.inr f := by
    intro X₀ c hc
    obtain ⟨f, rfl, x, hx, hf⟩ := Gen.mem_stepR_iff'.1 hc
    exact ⟨x, hx, f, hf, rfl⟩
  refine ⟨SC (Fin n) E (q - i) (r - i), inferInstance, Sum.inl, fun _ => ends',
    fun T => stepR (q - i) (r - i) bd j₀ (fibre tg X T),
    fun T => stepY (q - i) (r - i) bd (fibre tg X T),
    fun T => stepW (q - i) (r - i) bd j₀ (fibre tg X T), Sum.inl_injective, fun T c => hinl c,
    fun T hT => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · have href := hres (fibre tg X T) (fibre_subset _ _ _)
    rw [map_eq_image] at href
    refine ⟨?_, href.mono (by omega), ?_, (stepY_subset_stepR bd j₀ _).trans subset_union_right,
      ?_⟩
    · intro c hc x hx
      obtain ⟨y, -, f, -, rfl⟩ := hmemR _ c hc
      exact Sum.inl_ne_inr hx
    · intro c hc
      have hcR := stepY_subset_stepR bd j₀ _ hc
      obtain ⟨x, hx, f, hf, rfl⟩ := hmemR _ c hcR
      have hxX := fibre_subset _ _ _ hx
      obtain ⟨hsub, hmeet⟩ := hEd x hxX f hf
      have hcard := href.rgraph (Sum.inr f) (mem_union_right _ hcR)
      obtain ⟨v, hv⟩ := hmeet
      have hvZ : v ∈ ends' (Sum.inr f) ∩ Z :=
        mem_inter.2 ⟨(mem_inter.1 hv).1, (hA x hxX).1 (mem_inter.1 hv).2⟩
      have h1 := card_sdiff_add_card_inter (ends' (Sum.inr f)) Z
      have h2 : 0 < (ends' (Sum.inr f) ∩ Z).card := card_pos.2 ⟨v, hvZ⟩
      show (ends' (Sum.inr f) \ Z).card ≤ r - i - 1
      omega
    · intro c hc
      obtain ⟨x, hx, f, hf, rfl⟩ := hmemR _ c hc
      have hxX := fibre_subset _ _ _ hx
      exact (hEd x hxX f hf).1.trans (union_subset (hbd x) ((hA x hxX).1.trans hZ))
  · -- lifted degrees of the new copies
    have hle : ∀ T ∈ X.image tg, mdeg (fun c => T ∪ ends' c)
        (stepR (q - i) (r - i) bd j₀ (fibre tg X T)) S ≤
        ∑ x ∈ fibre tg X T, ((Gen.Ed (q - i) (r - i) bd j₀ x).filter
          fun f => S ⊆ tg x ∪ ends' (Sum.inr f)).card := by
      intro T _
      unfold mdeg stepR
      rw [filter_map, card_map, filter_biUnion]
      refine card_biUnion_le.trans (sum_le_sum fun x hx => ?_)
      rw [(mem_fibre.1 hx).2]
      exact le_of_eq rfl
    refine (sum_le_sum hle).trans ?_
    rw [sum_fibre_sum X (fun x => ((Gen.Ed (q - i) (r - i) bd j₀ x).filter
      fun f => S ⊆ tg x ∪ ends' (Sum.inr f)).card)]
    refine (hdegE S (by rw [hik]; exact hS)).trans ?_
    exact Nat.mul_le_mul_right _ (by omega)
  · -- lifted piece degrees
    have hle : ∀ T ∈ X.image tg, pdeg (fun c => T ∪ ends' c)
        (stepW (q - i) (r - i) bd j₀ (fibre tg X T)) S ≤
        ∑ x ∈ fibre tg X T, 2 * (if S ⊆ tg x ∪ bd x ∪ A x then 1 else 0) := by
      intro T _
      unfold stepW
      refine (pdeg_union_le _ _ _ S).trans ?_
      have hone : ∀ (P : E → Finset (SC (Fin n) E (q - i) (r - i))),
          (∀ x ∈ fibre tg X T, (P x).biUnion ends' ⊆ bd x ∪ A x) →
          pdeg (fun c => T ∪ ends' c) ((fibre tg X T).image P) S ≤
            ∑ x ∈ fibre tg X T, (if S ⊆ tg x ∪ bd x ∪ A x then 1 else 0) := by
        intro P hP
        unfold pdeg
        rw [filter_image]
        refine card_image_le.trans ?_
        rw [card_eq_sum_ones, sum_filter]
        refine sum_le_sum fun x hx => ?_
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso
          apply h2
          have hTx := (mem_fibre.1 hx).2
          intro v hv
          have := h1 hv
          by_cases hW : (P x).Nonempty
          · rw [biUnion_union_left_of_ne hW] at this
            rcases mem_union.1 this with h | h
            · rw [← hTx] at h; exact mem_union_left _ (mem_union_left _ h)
            · rcases mem_union.1 (hP x hx h) with h' | h'
              · exact mem_union_left _ (mem_union_right _ h')
              · exact mem_union_right _ h'
          · rw [not_nonempty_iff_eq_empty] at hW
            rw [hW, biUnion_empty] at this
            exact absurd this (notMem_empty v)
        · exact Nat.zero_le _
        · exact le_rfl
      have h1 := hone (pieceP (q - i) (r - i) bd j₀) fun x hx =>
        (hpieces x (fibre_subset _ _ _ hx)).1
      have h2 := hone (pieceQ (q - i) (r - i) bd j₀) fun x hx =>
        (hpieces x (fibre_subset _ _ _ hx)).2
      refine (Nat.add_le_add h1 h2).trans (le_of_eq ?_)
      rw [← sum_add_distrib]
      exact sum_congr rfl fun x _ => by ring
    refine (sum_le_sum hle).trans ?_
    rw [sum_fibre_sum X (fun x => 2 * (if S ⊆ tg x ∪ bd x ∪ A x then 1 else 0)), ← mul_sum,
      ← sum_filter, ← card_eq_sum_ones]
    have := hdegA S (by rw [hik]; exact hS)
    calc 2 * (X.filter fun x => S ⊆ tg x ∪ bd x ∪ A x).card ≤ 2 * (C * D) :=
          Nat.mul_le_mul_left _ this
      _ = 2 * C * D := by ring

end RefinedAbsorption.LinkSpread
