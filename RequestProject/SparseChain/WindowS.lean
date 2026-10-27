module
public import RequestProject.Sharp.Sparsify
public import RequestProject.SparseChain.StageS
public import RequestProject.FlatOmni.SharpBounds

/-!
# Theorem 3.8 from sparse link levels

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Lemma 3.14 and Theorem 3.8.
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

In the window stage the link levels are only applied after edge sparsification, i.e. with degree
parameter `D₂ = O(sharpCost r |U|) = o(|U|)`; so sparse link levels (`PlacedLinkLevelS`, required
only when `Ch · D ≤ |Z|`) suffice.

* **`windowStage_of_sparsify_levelsS`**: as `windowStage_of_sparsify_levels`, from sparse levels.
* **`nativeStrongMultiRefiners_of_levelsS`**: Theorem 3.8 from sparse link levels at `1 ≤ i < r - 1`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Window
  RefinedAbsorption.FlatOmni

/-- **Better Refine Down Lemma** (Lemma 3.14) from sparse link levels. -/
theorem windowStage_of_sparsify_levelsS {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hS : ∀ M₀ : ℕ, ∃ Cst m₀ : ℕ, EdgeSparsification q r M₀ Cst m₀)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelS q r i (sharpCost r)) :
    ∃ M Cst m₀ : ℕ, 1 ≤ M ∧ 1 ≤ Cst ∧ WindowStageM q r M Cst m₀ (sharpCost r) := by
  obtain ⟨Cs, C, M, hM, hCs, hst⟩ := multiStageS (a := sharpCost r) hr hrq (fun i hi hir => by
    rcases Nat.lt_or_ge i (r - 1) with h | h
    · exact hL i hi h
    · obtain rfl : i = r - 1 := by omega
      exact (placedLinkLevel_last q r hr hrq).toS _)
  obtain ⟨C₁, m₁, hsp⟩ := hS M
  obtain ⟨m₂, hm₂⟩ := exists_mul_sharpPot_le hr (8 * Cs * (C₁ + 1))
  set K := C₁ + C * (C₁ + 1) + 1 with hK
  refine ⟨M, K, m₁ + 4 * Cs + 4 + m₂, hM, by omega, ?_⟩
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
    hY₂R.trans subset_union_right, h2Z, hY₂Z, hY₂m, ?_, ?_, hone, ?_⟩
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

/-- **Theorem 3.8 from sparse link levels**: strong multi-refiners with budget
`C · max(D, n^{1-1/r} log n)` exist in uniformity `r` as soon as sparse placed link refiners with
additive term `sharpCost r` exist at the levels `1 ≤ i < r - 1`. -/
theorem nativeStrongMultiRefiners_of_levelsS {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelS q r i (sharpCost r)) :
    NativeStrongMultiRefiners q r :=
  nativeStrongMultiRefiners_of_windowStageM_sharp hr hrq
    (windowStage_of_sparsify_levelsS hr hrq (edgeSparsification_holds hr hrq) hL)

end RefinedAbsorption.Sharp
