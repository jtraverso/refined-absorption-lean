module
public import RefinedAbsorption.General.Defs

/-!
# Local refiners in uniformity `k` with the sublinear additive term

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Theorem 3.8 in the local form used in §4.
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `multiStageSK`: one refine-down stage from sparse link levels with `|U| ≤ K₀ |Z|`.
* `windowStageM_of_levelsS_ge`: the window stage of cost `sharpCost k` for every multiplicity bound.
* `localDescentK`: descent through windows inside a prescribed set.
* `localRefinerK`: a `k`-multigraph inside `Y` has a complete multi-refiner inside `Y ∪ P` whose
  pieces contain at most one old copy, with `(k-1)`-degrees `≤ C (D + sharpPot k |P|)`.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Window
  RefinedAbsorption.Sharp RefinedAbsorption.FlatOmni

set_option maxHeartbeats 2000000 in
/-- **One stage of the multigraph refine-down construction, sparse form, with `|U| ≤ K₀ |Z|`**. -/
theorem multiStageSK {q r : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelS q r i a) (K₀ : ℕ) :
    ∃ Cs C M : ℕ, 1 ≤ M ∧ q + r ≤ Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → U.card ≤ K₀ * Z.card → Cs * D ≤ Z.card →
      1 ≤ D → a Z.card ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
        (R Y : Finset E') (𝒲 : Finset (Finset E')),
        Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
        IsResidualMultiRefiner q r C ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
        (∀ c ∈ Y, ends' c ⊆ Z) ∧ (∀ e, mult ends' Y e ≤ M) ∧ (∀ c ∈ R, ends' c ⊆ U ∪ Z) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ C * D) ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ C * D) := by
  obtain ⟨C₀, hC₀, hround⟩ := Gen.multiRound (q := q) (r := r) (by omega) hrq
  obtain ⟨Cs₂, C₂, hCs₂, hchain⟩ := placedChainS hrq hL (r - 1) (by omega) (K₀ + 1)
  obtain ⟨M, Cm, hM, hmr⟩ := multiplicityReduction_quant q r hrq.le
  set Kp := (K₀ + 1) ^ (r - 1) with hKp
  have hKp1 : 1 ≤ Kp := Nat.one_le_pow _ _ (by omega)
  set D₀ := C₀ * Kp with hD₀
  set A := D₀ + C₂ * D₀ + (M + 2) ^ 2 * (D₀ + C₂ * D₀) with hA
  set P := C₀ * Kp + C₂ * D₀ + Cm * (1 + (M + 2) ^ 2) * (D₀ + C₂ * D₀) with hP
  set C := (C₀ + C₂ + Cm) + A + P with hC
  refine ⟨C₀ + Cs₂ * D₀ + q + r, C, M, hM, by omega, ?_⟩
  intro n E _ ends Z U X D hXr hXU hUZ hZD hD1 haD hdeg
  have hZ : C₀ + Cs₂ * D₀ + q + r ≤ Z.card := le_trans (Nat.le_mul_of_pos_right _ hD1) hZD
  -- density of the roots
  have hXJ : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      mdeg ends X J ≤ (Kp * D) * Z.card ^ (r - 1 - J.card) := by
    intro J hJ
    refine (mdeg_le_pow hXr hXU hdeg hJ).trans ?_
    calc D * U.card ^ (r - 1 - J.card) ≤ D * ((K₀ + 1) * Z.card) ^ (r - 1 - J.card) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) _)
      _ = D * ((K₀ + 1) ^ (r - 1 - J.card) * Z.card ^ (r - 1 - J.card)) := by rw [mul_pow]
      _ ≤ D * (Kp * Z.card ^ (r - 1 - J.card)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by omega) (by omega)))
      _ = Kp * D * Z.card ^ (r - 1 - J.card) := by ring
  -- 1. the round
  obtain ⟨ends₀, R₀, Y₀, 𝒲₀, hends₀, h₀, hY₀R, hR₀fresh, hR₀Z, hR₀loc, hone₀, hdeg₀, hpd₀⟩ :=
    hround n ends X Z (Kp * D) hXr (by omega) hXJ
  have hY₀r : MIsRGraph r ends₀ Y₀ := fun c hc => h₀.rgraph c (mem_union_right _ (hY₀R hc))
  have hY₀flat : IsFlat (r - 1) Z ends₀ Y₀ := by
    intro c hc
    have hcard := hY₀r c hc
    have h1 : 0 < (ends₀ c ∩ Z).card := (hR₀Z c (hY₀R hc)).card_pos
    have := card_sdiff_add_card_inter (ends₀ c) Z
    omega
  have hR₀U : ∀ c ∈ R₀, ends₀ c ⊆ U ∪ Z := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := hR₀loc c hc
    exact hcx.trans (union_subset_union (hXU x hx) subset_rfl)
  have hY₀U : ∀ c ∈ Y₀, ends₀ c ⊆ U ∪ Z := fun c hc => hR₀U c (hY₀R hc)
  have hdegR₀ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₀ R₀ S ≤ D₀ * D := by
    intro S hS; rw [hD₀, mul_assoc]; exact hdeg₀ S hS
  have hdegY₀ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₀ Y₀ S ≤ D₀ * D :=
    fun S hS => (mdeg_mono _ hY₀R S).trans (hdegR₀ S hS)
  have hUZ9 : (U ∪ Z).card ≤ (K₀ + 1) * Z.card := (card_union_le U Z).trans (by nlinarith)
  have hD₀D : 1 ≤ D₀ * D := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- 2. the flat levels
  obtain ⟨E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂fresh, h₂, hY₂flat, hY₂sub, hR₂U,
    hdegR₂, hpdR₂⟩ := hchain n ends₀ Z (U ∪ Z) Y₀ (D₀ * D) hY₀r hY₀flat hY₀U hUZ9
      (by omega) hD₀D (haD.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hKp1)))
      (by rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hZD) hdegY₀
  have hY₂Z : ∀ c ∈ Y₂, ends₂ c ⊆ Z := by
    intro c hc
    have := hY₂flat c hc
    rw [Nat.le_zero, card_eq_zero, sdiff_eq_empty_iff_subset] at this
    exact this
  have hY₂r : MIsRGraph r ends₂ Y₂ := fun c hc => h₂.rgraph c (hY₂sub hc)
  have h02 := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₀
    (hY₀R.trans subset_union_right) h₂ hR₂fresh
  have hone02 := oneX_compose g₂ hg₂ h₀.disjoint hY₀R hone₀ h₂ hR₂fresh
  -- 3. multiplicity reduction
  obtain ⟨N, _, endsN, Rm, Ym, 𝒲m, hRm, hYmR, hm, hmult, hdegm, hparm⟩ := hmr ends₂ Y₂ hY₂r
  set R₀₂ := R₀.image g₂ ∪ R₂ with hR₀₂
  have hY₂R : Y₂ ⊆ R₀₂ := by
    intro c hc
    rcases mem_union.1 (hY₂sub hc) with h | h
    · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 h
      exact mem_union_left _ (mem_image_of_mem _ (hY₀R hc₀))
    · exact mem_union_right _ h
  have hR₀₂fresh : ∀ c ∈ R₀₂, ∀ x : E, g₂ (Sum.inl x) ≠ c := by
    intro c hc x
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 h
      intro hxc
      exact hR₀fresh c₀ hc₀ x (hg₂ hxc).symm
    · exact hR₂fresh c h _
  have hmR : IsResidualMultiRefiner q r Cm (Sum.elim ends₂ endsN) (Y₂.image Sum.inl)
      (Rm.image Sum.inr) Ym 𝒲m := hm
  have hinrfresh : ∀ c ∈ Rm.image (Sum.inr : N → E₂ ⊕ N), ∀ x : E₂, Sum.inl x ≠ c := by
    intro c hc x hx
    obtain ⟨y, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr hx
  have h02m := IsResidualMultiRefiner.compose (Sum.inl : E₂ → E₂ ⊕ N) Sum.inl_injective
    (fun c => rfl) h02 (hY₂R.trans subset_union_right) hmR hinrfresh
  have hone := oneX_compose (Sum.inl : E₂ → E₂ ⊕ N) Sum.inl_injective h02.disjoint hY₂R
    hone02 hmR hinrfresh
  -- assembling
  set g : E → E₂ ⊕ N := fun x => Sum.inl (g₂ (Sum.inl x)) with hgdef
  have hg : Function.Injective g := fun x y hxy =>
    Sum.inl_injective (hg₂ (Sum.inl_injective hxy))
  have hXimg : ((X.map Function.Embedding.inl).image g₂).image (Sum.inl : E₂ → E₂ ⊕ N) =
      X.image g := by
    ext c
    simp only [mem_image, mem_map, Function.Embedding.inl_apply, hgdef]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  rw [hXimg] at h02m hone
  set ends' : E₂ ⊕ N → Finset (Fin n) := Sum.elim ends₂ endsN with hends'
  have hYmRt : Ym ⊆ R₀₂.image (Sum.inl : E₂ → E₂ ⊕ N) ∪ Rm.image Sum.inr :=
    hYmR.trans subset_union_right
  -- degrees
  have hdeg₀₂ : ∀ S : Finset (Fin n), S.card = r - 1 →
      mdeg ends₂ R₀₂ S ≤ D₀ * D + C₂ * (D₀ * D) := by
    intro S hS
    refine (Dense.mdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ (hdegR₂ S hS))
    rw [mdeg_image_eq (A := R₀) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    exact hdegR₀ S hS
  refine ⟨E₂ ⊕ N, inferInstance, g, ends', R₀₂.image Sum.inl ∪ Rm.image Sum.inr, Ym,
    (𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl) ∪ 𝒲m, hg,
    fun c => by simp [hends', hgdef, hends₂, hends₀], ?_, h02m.mono (by omega), hYmRt, ?_,
    hmult, ?_, ?_, hone, ?_⟩
  · intro c hc x hx
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 h
      exact hR₀₂fresh c₂ hc₂ x (Sum.inl_injective hx)
    · obtain ⟨y, -, rfl⟩ := mem_image.1 h
      exact Sum.inl_ne_inr hx
  · intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 (hYmR hc)
    obtain ⟨c₂, hc₂, he⟩ := mem_image.1 (hRm y hy)
    show endsN y ⊆ Z
    rw [← he]; exact hY₂Z c₂ hc₂
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 h
      show ends₂ c₂ ⊆ U ∪ Z
      rcases mem_union.1 hc₂ with h' | h'
      · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 h'
        rw [hends₂]; exact hR₀U c₀ hc₀
      · refine (hR₂U c₂ h').trans ?_
        rw [union_assoc, union_self]
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 h
      obtain ⟨c₂, hc₂, he⟩ := mem_image.1 (hRm y hy)
      show endsN y ⊆ U ∪ Z
      rw [← he]; exact (hY₂Z c₂ hc₂).trans subset_union_right
  · intro S hS
    refine (Dense.mdeg_union_le _ _ _ S).trans ?_
    have e1 : mdeg ends' (R₀₂.image Sum.inl) S = mdeg ends₂ R₀₂ S :=
      mdeg_image_eq (A := R₀₂) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
    have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends₂ Y₂ S := hdegm S
    rw [e1]
    have h4 := hdeg₀₂ S hS
    calc mdeg ends₂ R₀₂ S + mdeg ends' (Rm.image Sum.inr) S
        ≤ (D₀ * D + C₂ * (D₀ * D)) + (M + 2) ^ 2 * (D₀ * D + C₂ * (D₀ * D)) := by
          refine Nat.add_le_add h4 (e2.trans (Nat.mul_le_mul_left _ ?_))
          exact (mdeg_mono _ hY₂R S).trans h4
      _ ≤ C * D := by
          have : (D₀ * D + C₂ * (D₀ * D)) + (M + 2) ^ 2 * (D₀ * D + C₂ * (D₀ * D)) = A * D := by
            rw [hA]; ring
          rw [this]
          exact Nat.mul_le_mul_right _ (by omega)
  · intro S hS
    have hSne : S.Nonempty := by rw [← card_pos, hS]; omega
    have hY₂d : mdeg ends₂ Y₂ S ≤ D₀ * D + C₂ * (D₀ * D) := (mdeg_mono _ hY₂R S).trans (hdeg₀₂ S hS)
    have hm1 : pdeg ends' 𝒲m S ≤ Cm * mdeg ends' (Y₂.image Sum.inl ∪ Rm.image Sum.inr) S :=
      pdeg_le_of_parallel hmR hparm hSne
    have hm2 : mdeg ends' (Y₂.image Sum.inl ∪ Rm.image Sum.inr) S ≤
        (1 + (M + 2) ^ 2) * (D₀ * D + C₂ * (D₀ * D)) := by
      refine (Dense.mdeg_union_le _ _ _ S).trans ?_
      have e1 : mdeg ends' (Y₂.image Sum.inl) S = mdeg ends₂ Y₂ S :=
        mdeg_image_eq (A := Y₂) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
      have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends₂ Y₂ S := hdegm S
      rw [e1]
      calc mdeg ends₂ Y₂ S + mdeg ends' (Rm.image Sum.inr) S
          ≤ (D₀ * D + C₂ * (D₀ * D)) + (M + 2) ^ 2 * (D₀ * D + C₂ * (D₀ * D)) :=
            Nat.add_le_add hY₂d (e2.trans (Nat.mul_le_mul_left _ hY₂d))
        _ = (1 + (M + 2) ^ 2) * (D₀ * D + C₂ * (D₀ * D)) := by ring
    have h0 : pdeg ends₀ 𝒲₀ S ≤ C₀ * (Kp * D) := hpd₀ S hS
    have h2 : pdeg ends₂ 𝒲₂ S ≤ C₂ * (D₀ * D) := hpdR₂ S hS
    calc pdeg ends' ((𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl) ∪ 𝒲m) S
        ≤ pdeg ends' ((𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl)) S + pdeg ends' 𝒲m S :=
          pdeg_union_le _ _ _ _
      _ ≤ (pdeg ends₂ (𝒲₀.image (image g₂)) S + pdeg ends₂ 𝒲₂ S) + pdeg ends' 𝒲m S :=
          Nat.add_le_add_right ((pdeg_image_le Sum.inl (fun c => rfl) _ S).trans
            (pdeg_union_le _ _ _ S)) _
      _ ≤ (C₀ * (Kp * D) + C₂ * (D₀ * D)) +
            Cm * ((1 + (M + 2) ^ 2) * (D₀ * D + C₂ * (D₀ * D))) := by
          refine Nat.add_le_add (Nat.add_le_add ((pdeg_image_le g₂ hends₂ 𝒲₀ S).trans h0) h2) ?_
          exact hm1.trans (Nat.mul_le_mul_left _ hm2)
      _ = P * D := by rw [hP]; ring
      _ ≤ C * D := Nat.mul_le_mul_right _ (by omega)


set_option maxHeartbeats 1000000 in
/-- **Better Refine Down Lemma** (Lemma 3.14) from sparse link levels, for every input
multiplicity bound `M₀ ≥ M`. -/
theorem windowStage_of_sparsify_levelsS_ge {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hS : ∀ M₀ : ℕ, ∃ Cst m₀ : ℕ, EdgeSparsification q r M₀ Cst m₀)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelS q r i (sharpCost r)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ M₀ : ℕ, M ≤ M₀ →
      ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStageM q r M₀ Cst m₀ (sharpCost r) := by
  obtain ⟨Cs, C, M, hM, hCs, hst⟩ := multiStageS (a := sharpCost r) hr hrq (fun i hi hir => by
    rcases Nat.lt_or_ge i (r - 1) with h | h
    · exact hL i hi h
    · obtain rfl : i = r - 1 := by omega
      exact (placedLinkLevel_last q r hr hrq).toS _)
  refine ⟨M, hM, fun M₀ hM₀ => ?_⟩
  obtain ⟨C₁, m₁, hsp⟩ := hS M₀
  obtain ⟨m₂, hm₂⟩ := exists_mul_sharpPot_le hr (8 * Cs * (C₁ + 1))
  set K := C₁ + C * (C₁ + 1) + 1 with hK
  refine ⟨K, m₁ + 4 * Cs + 4 + m₂, by omega, ?_⟩
  intro n E _ ends U X D hXr hXU hU hD1 hXm hdeg
  have hm₁ : m₁ < U.card := by omega
  -- 1. edge sparsification
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hR₁U, hdegY₁, hdegR₁,
    hone₁, hpd₁⟩ := hsp n ends U X D hXr hXU hm₁ hXm hdeg
  have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  have hY₁U : ∀ c ∈ Y₁, ends₁ c ⊆ U := fun c hc => hR₁U c (hY₁R hc)
  -- 2. the window `Z` of a quarter of the size
  obtain ⟨Z, hZU, hZc⟩ := exists_subset_card_eq (Nat.div_le_self U.card 4)
  have hUZ : U.card ≤ 8 * Z.card := by omega
  have hCsZ : Cs ≤ Z.card := by omega
  have h2Z : 2 * Z.card ≤ U.card := by omega
  set s := sharpCost r U.card with hs
  have hs1 : 1 ≤ s := one_le_sharpCost r (by omega)
  have hsZ : sharpCost r Z.card ≤ s := sharpCost_mono (by omega) (card_le_card hZU)
  have hwc : winCost r U.card ≤ s := winCost_le_sharpCost r U.card
  set D₂ := (C₁ + 1) * s with hD₂
  have hD₂1 : 1 ≤ D₂ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hD₂a : sharpCost r Z.card ≤ D₂ := hsZ.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hdegY₁' : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ D₂ := by
    intro S hS
    refine (hdegY₁ S hS).trans ?_
    calc C₁ * winCost r U.card ≤ C₁ * s := Nat.mul_le_mul_left _ hwc
      _ ≤ (C₁ + 1) * s := Nat.mul_le_mul_right _ (by omega)
  have hCsD : Cs * D₂ ≤ Z.card := by
    have h1 : sharpCost r U.card ≤ sharpPot r U.card := by
      have := sharpPot_step (r := r) (by omega) (m := U.card) (m' := 0) (by omega) (by omega)
      simpa [sharpPot] using this
    have h2 := hm₂ U.card (by omega)
    have h3 : 8 * (Cs * D₂) ≤ U.card := by
      calc 8 * (Cs * D₂) = 8 * Cs * (C₁ + 1) * s := by rw [hD₂]; ring
        _ ≤ 8 * Cs * (C₁ + 1) * sharpPot r U.card := Nat.mul_le_mul_left _ h1
        _ ≤ U.card := h2
    have h4 : 0 < Cs * D₂ := Nat.mul_pos (by omega) hD₂1
    rw [hZc]; omega
  -- 3. refine down
  obtain ⟨E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hY₂R, hY₂Z, hY₂m, -, hdegR₂, hone₂,
    hpd₂⟩ := hst n ends₁ Z U Y₁ D₂ hY₁r hY₁U hUZ hCsD hD₂1 hD₂a hdegY₁'
  have h12 := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₁
    (hY₁R.trans subset_union_right) h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂ hR₂f
  rw [image_image] at h12 hone
  have hCK : C₁ + C ≤ K := by
    have : C ≤ C * (C₁ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  refine ⟨E₂, inferInstance, g₂ ∘ g₁, ends₂, R₁.image g₂ ∪ R₂, Y₂, 𝒲₁.image (image g₂) ∪ 𝒲₂, Z,
    hg₂.comp hg₁, fun c => by simp [hends₂, hends₁], ?_, h12.mono hCK,
    hY₂R.trans subset_union_right, h2Z, hY₂Z, fun e => (hY₂m e).trans hM₀, ?_, ?_, hone, ?_⟩
  · intro c hc x
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      intro hx
      exact hR₁f c₁ hc₁ x (hg₂ hx)
    · exact hR₂f c h _
  · intro S hS
    refine (mdeg_mono _ hY₂R S).trans ((hdegR₂ S hS).trans ?_)
    calc C * D₂ = C * (C₁ + 1) * s := by rw [hD₂]; ring
      _ ≤ K * s := Nat.mul_le_mul_right _ (by omega)
  · intro S hS
    refine (Dense.mdeg_union_le _ _ _ S).trans ?_
    rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    have h1 := hdegR₁ S hS
    have h2 := hdegR₂ S hS
    have e : C * D₂ = C * (C₁ + 1) * s := by rw [hD₂]; ring
    have h3 : C₁ * (D + s) + C * (C₁ + 1) * s ≤ K * (D + s) := by
      have : C₁ * (D + s) + C * (C₁ + 1) * s ≤ (C₁ + C * (C₁ + 1)) * (D + s) := by
        nlinarith
      exact this.trans (Nat.mul_le_mul_right _ (by omega))
    omega
  · intro S hS
    refine (pdeg_union_le _ _ _ S).trans ?_
    have h1 := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
    have h2 := hpd₂ S hS
    have e : C * D₂ = C * (C₁ + 1) * s := by rw [hD₂]; ring
    have h3 : C₁ * (D + s) + C * (C₁ + 1) * s ≤ K * (D + s) := by
      have : C₁ * (D + s) + C * (C₁ + 1) * s ≤ (C₁ + C * (C₁ + 1)) * (D + s) := by
        nlinarith
      exact this.trans (Nat.mul_le_mul_right _ (by omega))
    omega

/-- Output of a local refiner construction in uniformity `k`. -/
def LocalOutK (q k C : ℕ) {n : ℕ} {E : Type} (ends : E → Finset (Fin n)) (Z : Finset (Fin n))
    (X : Finset E) (Bd : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
    (R : Finset E') (𝒲 : Finset (Finset E')),
    Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
    IsMultiRefiner q k C ends' (X.image g) R 𝒲 ∧ (∀ c ∈ R, ends' c ⊆ Z) ∧
    (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends' R S ≤ Bd) ∧
    (∀ S : Finset (Fin n), S.card = k - 1 → pdeg ends' 𝒲 S ≤ Bd)

section MapEndsK

variable {m n : ℕ} {E : Type*} [DecidableEq E]

omit [DecidableEq E] in
theorem mdeg_mapEnds_emb_image (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m)) (G : Finset E)
    (S : Finset (Fin m)) : mdeg (mapEnds emb ends) G (S.image emb) = mdeg ends G S := by
  unfold mdeg mapEnds
  congr 1
  exact filter_congr fun c _ => image_subset_image_iff emb.injective

omit [DecidableEq E] in
theorem mdeg_mapEnds_emb_out' (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m)) (G : Finset E)
    (S : Finset (Fin n)) (hv : ∃ v ∈ S, ∀ i, emb i ≠ v) : mdeg (mapEnds emb ends) G S = 0 := by
  obtain ⟨v, hvS, hv⟩ := hv
  unfold mdeg mapEnds
  rw [card_eq_zero, filter_eq_empty_iff]
  intro c _ h
  obtain ⟨i, -, hi⟩ := mem_image.1 (h hvS)
  exact hv i hi

omit [DecidableEq E] in
theorem pdeg_mapEnds_emb_image (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m))
    (𝒲 : Finset (Finset E)) (S : Finset (Fin m)) :
    pdeg (mapEnds emb ends) 𝒲 (S.image emb) = pdeg ends 𝒲 S := by
  unfold pdeg
  congr 1
  refine filter_congr fun W _ => ?_
  rw [biUnion_mapEnds]
  exact image_subset_image_iff emb.injective

omit [DecidableEq E] in
theorem pdeg_mapEnds_emb_out' (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m))
    (𝒲 : Finset (Finset E)) (S : Finset (Fin n)) (hv : ∃ v ∈ S, ∀ i, emb i ≠ v) :
    pdeg (mapEnds emb ends) 𝒲 S = 0 := by
  obtain ⟨v, hvS, hv⟩ := hv
  unfold pdeg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro W _ h
  rw [biUnion_mapEnds] at h
  obtain ⟨i, -, hi⟩ := mem_image.1 (h hvS)
  exact hv i hi

/-- A set inside the range of an embedding is the image of its preimage. -/
theorem exists_preimage_of_range (emb : Fin m ↪ Fin n) (S : Finset (Fin n))
    (hS : ∀ v ∈ S, ∃ i, emb i = v) : ∃ S' : Finset (Fin m), S'.image emb = S ∧ S'.card = S.card := by
  refine ⟨S.preimage emb emb.injective.injOn, ?_, ?_⟩
  · rw [image_preimage]
    exact filter_true_of_mem fun v hv => hS v hv
  · conv_rhs => rw [← show (S.preimage emb emb.injective.injOn).image emb = S from by
      rw [image_preimage]; exact filter_true_of_mem fun v hv => hS v hv]
    rw [card_image_of_injective _ emb.injective]

end MapEndsK

/-- **Descent through windows inside a prescribed set, uniformity `k`.** -/
theorem localDescentK {q k : ℕ} (hk : 2 ≤ k) (hkq : k < q)
    (hL : ∀ j, 1 ≤ j → j < k - 1 → PlacedLinkLevelS q k j (sharpCost k)) (M₀ : ℕ) :
    ∃ C A : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (P : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph k ends X → (∀ x ∈ X, ends x ⊆ P) → 1 ≤ D → (∀ e, mult ends X e ≤ M₀) →
      (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends X S ≤ D) →
      LocalOutK q k C ends P X (A * (D + sharpPot k P.card)) := by
  classical
  obtain ⟨M, -, hst⟩ := windowStage_of_sparsify_levelsS_ge hk hkq
    (edgeSparsification_holds hk hkq) hL
  obtain ⟨Cst, m₀, hCst, hstage⟩ := hst (max M M₀) (le_max_left _ _)
  obtain ⟨Cb, Ab, hbase⟩ := baseRefiner q k hk hkq (max m₀ 1)
  have hwin := windowRefinerM_pot (Φ := sharpPot k) (a := sharpCost k)
    (fun m m' hm h => sharpPot_step (by omega) (by omega) h)
    (fun m hm => one_le_sharpCost k (by omega)) hstage hbase hCst
  set K := Cst + (Cst + Ab) * Cst with hK
  refine ⟨Cst + Cb + (Cst + Cb) + (Cst + Cb), (Cst + Ab) + K, ?_⟩
  intro n E _ ends P X D hXr hXP hD1 hXm hdeg
  set m := P.card with hm
  set emb : Fin m ↪ Fin n := (P.orderEmbOfFin rfl).toEmbedding with hemb
  have hembP : ∀ i, emb i ∈ P := fun i => P.orderEmbOfFin_mem rfl i
  have hPemb : ∀ v ∈ P, ∃ i, emb i = v := by
    intro v hv
    have : v ∈ Set.range (P.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hv
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  set endsS : {c // c ∈ X} → Finset (Fin m) :=
    fun c => (ends c.1).preimage emb emb.injective.injOn with hendsS
  have hmapS : ∀ c : {c // c ∈ X}, (endsS c).image emb = ends c.1 := by
    intro c
    rw [hendsS, image_preimage]
    exact filter_true_of_mem fun v hv => hPemb v (hXP c.1 c.2 hv)
  have hcardS : ∀ c : {c // c ∈ X}, (endsS c).card = k := by
    intro c
    rw [← card_image_of_injective _ emb.injective, hmapS]
    exact hXr c.1 c.2
  have hmultS : ∀ e, mult endsS univ e ≤ max M M₀ := by
    intro e
    refine le_trans ?_ ((hXm (e.image emb)).trans (le_max_right _ _))
    unfold mult
    refine card_le_card_of_injOn (fun c => c.1) (fun c hc => ?_)
      (fun c _ c' _ h => Subtype.ext h)
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hc ⊢
    refine ⟨c.2, ?_⟩
    rw [← hmapS c, hc]
  have hdegS : ∀ S : Finset (Fin m), S.card = k - 1 → mdeg endsS univ S ≤ D := by
    intro S hS
    refine le_trans ?_ (hdeg (S.image emb) (by rw [card_image_of_injective _ emb.injective, hS]))
    unfold mdeg
    refine card_le_card_of_injOn (fun c => c.1) (fun c hc => ?_)
      (fun c _ c' _ h => Subtype.ext h)
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hc ⊢
    refine ⟨c.2, ?_⟩
    rw [← hmapS c]
    exact image_subset_image hc
  obtain ⟨E', _, g, ends'm, R, 𝒲, hg, hends, hfr, hch, -, hdegR, hpd⟩ :=
    hwin m endsS univ univ D (fun c _ => hcardS c) (fun _ _ => subset_univ _) hD1
      (fun e => hmultS e) hdegS
  have hu : (univ : Finset (Fin m)).card = m := by simp
  rw [hu] at hdegR hpd
  have h1 := hch.toResidual
  have h2 := residual_mapEnds h1 emb (fun _ _ => emb.injective.injOn) emb.injective.injOn
    (empty_subset _)
  set ends'' : E ⊕ E' → Finset (Fin n) := Sum.elim ends (mapEnds emb ends'm) with hends''
  have h3 := residual_relabel h2 Sum.inr ends'' (fun c _ => rfl) Sum.inr_injective.injOn
    (empty_subset _)
  rw [image_empty] at h3
  set g'' : E → E ⊕ E' := fun c => if hc : c ∈ X then Sum.inr (g ⟨c, hc⟩) else Sum.inl c
    with hg''
  have hXimg : X.image g'' = ((univ : Finset {c // c ∈ X}).image g).image Sum.inr := by
    ext y
    simp only [mem_image, mem_univ, true_and, hg'']
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨g ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩, by simp [hc]⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c.1, c.2, by simp [c.2]⟩
  have hBd : (Cst + Ab) * D + K * sharpPot k m ≤ ((Cst + Ab) + K) * (D + sharpPot k m) := by
    nlinarith
  refine ⟨E ⊕ E', inferInstance, g'', ends'', R.image Sum.inr, 𝒲.image (image Sum.inr), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro c c' h
    by_cases hc : c ∈ X <;> by_cases hc' : c' ∈ X <;> simp only [hg'', hc, hc', dif_pos,
      dif_neg, not_false_eq_true, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at h
    · exact congrArg Subtype.val (hg h)
    · exact h
  · intro c
    simp only [hg'']
    split_ifs with hc
    · show (ends'm (g ⟨c, hc⟩)).image emb = ends c
      rw [hends]; exact hmapS ⟨c, hc⟩
    · rfl
  · intro y hy x hx
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hy
    simp only [hg''] at hx
    split_ifs at hx with hxX
    exact hfr c' hc' ⟨x, hxX⟩ (Sum.inr_injective hx)
  · rw [hXimg]; exact h3.mono (le_refl _)
  · intro y hy
    obtain ⟨c', -, rfl⟩ := mem_image.1 hy
    intro v hv
    obtain ⟨i, -, rfl⟩ := mem_image.1 hv
    exact hembP i
  · intro S hS
    rw [mdeg_image_eq (A := R) (fun c _ => rfl) Sum.inr_injective.injOn subset_rfl]
    show mdeg (mapEnds emb ends'm) R S ≤ _
    by_cases hv : ∀ v ∈ S, ∃ i, emb i = v
    · obtain ⟨S', rfl, hS'⟩ := exists_preimage_of_range emb S hv
      rw [mdeg_mapEnds_emb_image]
      exact (hdegR S' (hS'.trans hS)).trans hBd
    · push_neg at hv
      rw [mdeg_mapEnds_emb_out' emb ends'm R S hv]
      exact Nat.zero_le _
  · intro S hS
    refine (pdeg_image_le (ends₁ := mapEnds emb ends'm) Sum.inr (fun c => rfl) 𝒲 S).trans ?_
    by_cases hv : ∀ v ∈ S, ∃ i, emb i = v
    · obtain ⟨S', rfl, hS'⟩ := exists_preimage_of_range emb S hv
      rw [pdeg_mapEnds_emb_image]
      exact (hpd S' (hS'.trans hS)).trans hBd
    · push_neg at hv
      rw [pdeg_mapEnds_emb_out' emb ends'm 𝒲 S hv]
      exact Nat.zero_le _

/-- `sharpPot r m ≤ 6 · sharpCost r m` for every `r ≥ 2`. -/
theorem sharpPot_le_six {r : ℕ} (hr : 2 ≤ r) (m : ℕ) : sharpPot r m ≤ 6 * sharpCost r m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sharpPot]
  have h := sharpPot_le_aux hr m hm
  set L : ℕ := Nat.log 2 m with hL
  set x : ℝ := (m : ℝ) ^ (1 - 1 / (r : ℝ)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hθ : (1 : ℝ) / 2 ≤ 1 - 1 / (r : ℝ) := by
    have : 1 / (r : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr'
    linarith
  have hxsq : (m : ℝ) ≤ x ^ 2 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    conv_lhs => rw [← Real.rpow_one (m : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by push_cast; linarith)
  have hpow : 2 ^ L ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hLsq : ((L : ℝ) + 1) ^ 2 ≤ 4 * x ^ 2 := by
    have := (FlatOmni.succ_sq_le_four_pow L).1
    have h' : (L + 1) ^ 2 ≤ 4 * m := this.trans (Nat.mul_le_mul_left _ hpow)
    have h'' : ((L : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) := by exact_mod_cast h'
    linarith
  have hL2 : (L : ℝ) + 1 ≤ 2 * x := by nlinarith
  have hcost : x * ((L : ℝ) + 1) ≤ (sharpCost r m : ℝ) := by
    unfold sharpCost winCost
    push_cast
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  have hfin : (sharpPot r m : ℝ) ≤ 6 * (sharpCost r m : ℝ) := by
    calc (sharpPot r m : ℝ) ≤ ((L : ℝ) + 1) * (4 * x + (L : ℝ) + 1) := h
      _ ≤ ((L : ℝ) + 1) * (6 * x) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = 6 * (x * ((L : ℝ) + 1)) := by ring
      _ ≤ 6 * (sharpCost r m : ℝ) := by linarith
  exact_mod_cast hfin


/-- **Local refiners in uniformity `k`** (sparse form): a `k`-multigraph `L` inside `Y` with
`(k-1)`-degrees `≤ D` has, for every `P` with `|Y| ≤ K |P|`, `Ch · D ≤ |P|` and
`sharpCost k |P| ≤ D`, a complete multi-refiner whose new copies lie inside `Y ∪ P`, whose pieces
contain at most one copy of `L`, and whose new copies and pieces have `(k-1)`-degrees `≤ C · D`. -/
theorem localRefinerK {q k : ℕ} (hk : 2 ≤ k) (hkq : k < q)
    (hL : ∀ j, 1 ≤ j → j < k - 1 → PlacedLinkLevelS q k j (sharpCost k)) (K : ℕ) :
    ∃ C Ch : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Y P : Finset (Fin n)) (L : Finset E) (D : ℕ),
      Y.card ≤ K * P.card → Ch * D ≤ P.card → sharpCost k P.card ≤ D →
      MIsRGraph k ends L → (∀ x ∈ L, ends x ⊆ Y) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends L S ≤ D) →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
        (R : Finset E') (𝒲 : Finset (Finset E')),
        Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
        IsMultiRefiner q k C ends' (L.image g) R 𝒲 ∧ (∀ c ∈ R, ends' c ⊆ Y ∪ P) ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ L.image g)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends' R S ≤ C * D) ∧
        (∀ S : Finset (Fin n), S.card = k - 1 → pdeg ends' 𝒲 S ≤ C * D) := by
  classical
  obtain ⟨Cs, C₁, M, -, -, hst⟩ := multiStageSK (q := q) (r := k) (a := sharpCost k) hk hkq
    (fun i hi hir => by
      rcases Nat.lt_or_ge i (k - 1) with h | h
      · exact hL i hi h
      · have e : i = k - 1 := by omega
        rw [e]
        exact (placedLinkLevel_last q k hk hkq).toS _) K
  obtain ⟨C₂, A, hdesc⟩ := localDescentK hk hkq hL M
  refine ⟨C₁ + C₂ + A * (C₁ + 8), Cs, ?_⟩
  intro n E _ ends Y P L D hYK hCs haD hLr hLY hD1 hdeg
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁P, hY₁m, hR₁U, hdeg₁,
    hone₁, hpd₁⟩ := hst n ends P Y L D hLr hLY hYK hCs hD1 haD hdeg
  have hY₁r : MIsRGraph k ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  set D₁ := (C₁ + 1) * D with hD₁
  have hD₁1 : 1 ≤ D₁ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hdegY₁ : ∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends₁ Y₁ S ≤ D₁ := by
    intro S hS
    refine (mdeg_mono _ hY₁R _).trans ((hdeg₁ S hS).trans ?_)
    exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hR₂P, hdeg₂, hpd₂⟩ :=
    hdesc n ends₁ P Y₁ D₁ hY₁r hY₁P hD₁1 hY₁m hdegY₁
  have h12 := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₁
    (hY₁R.trans subset_union_right) h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂ hR₂f
  rw [image_image] at h12 hone
  have hΦ : sharpPot k P.card ≤ 6 * D := (sharpPot_le_six hk _).trans (by omega)
  have hbound : C₁ * D + A * (D₁ + sharpPot k P.card) ≤ (C₁ + C₂ + A * (C₁ + 8)) * D := by
    have h1 : A * (D₁ + sharpPot k P.card) ≤ A * ((C₁ + 1) * D + 6 * D) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (C₁ + C₂ + A * (C₁ + 8)) * D = C₁ * D + A * ((C₁ + 1) * D + 6 * D) +
        (C₂ * D + A * D) := by ring
    omega
  refine ⟨E₂, inferInstance, g₂ ∘ g₁, ends₂, R₁.image g₂ ∪ R₂, 𝒲₁.image (image g₂) ∪ 𝒲₂,
    hg₂.comp hg₁, fun c => by simp [hends₂, hends₁], ?_, h12.mono (by nlinarith), ?_, hone,
    fun S hS => ?_, fun S hS => ?_⟩
  · intro c hc x
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      intro hx
      exact hR₁f c₁ hc₁ x (hg₂ hx)
    · exact hR₂f c h _
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      rw [hends₂]; exact (hR₁U c₁ hc₁).trans (by rw [union_comm])
    · exact (hR₂P c h).trans subset_union_right
  · refine (Dense.mdeg_union_le _ _ _ _).trans ?_
    rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    have := hdeg₁ S hS
    have := hdeg₂ S hS
    omega
  · refine (pdeg_union_le _ _ _ _).trans ?_
    have := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
    have := hpd₂ S hS
    omega

end RefinedAbsorption.General
