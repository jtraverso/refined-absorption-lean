module
public import RequestProject.Sharp.Sparsify

/-!
# The window stage for every multiplicity bound

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Lemma 3.14.  Lean formalization: Juan
Pablo Traverso Gianini, Apache-2.0.

`windowStage_of_sparsify_levels_ge` is `windowStage_of_sparsify_levels` for every multiplicity
bound `M₀ ≥ M` (the edge sparsification accepts any input multiplicity; the residue keeps
multiplicity `≤ M ≤ M₀`).  `windowStageM_two_ge` is the unconditional case `r = 2`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Window

/-- **Better Refine Down Lemma, any input multiplicity** (Delcourt–Postle, Lemma 3.14; the
input multiplicity bound `M₀` may be any number `≥ M`): edge sparsification followed by
the refine-down stage with link levels of additive term `sharpCost r` is a window stage with cost
`sharpCost r`. -/
theorem windowStage_of_sparsify_levels_ge {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hS : ∀ M₀ : ℕ, ∃ Cst m₀ : ℕ, EdgeSparsification q r M₀ Cst m₀)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelA q r i (sharpCost r)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ M₀ : ℕ, M ≤ M₀ →
      ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStageM q r M₀ Cst m₀ (sharpCost r) := by
  obtain ⟨Cs, C, M, hM, hCs, hst⟩ := multiStage (a := sharpCost r) hr hrq (fun i hi hir => by
    rcases Nat.lt_or_ge i (r - 1) with h | h
    · exact hL i hi h
    · obtain rfl : i = r - 1 := by omega
      exact (placedLinkLevel_last q r hr hrq).toA _)
  refine ⟨M, hM, fun M₀ hM₀ => ?_⟩
  obtain ⟨C₁, m₁, hsp⟩ := hS M₀
  set K := C₁ + C * (C₁ + 1) + 1 with hK
  refine ⟨K, m₁ + 4 * Cs + 4, by omega, ?_⟩
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
  -- 3. refine down
  obtain ⟨E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hY₂R, hY₂Z, hY₂m, -, hdegR₂, hone₂,
    hpd₂⟩ := hst n ends₁ Z U Y₁ D₂ hY₁r hY₁U hUZ hCsZ hD₂1 hD₂a hdegY₁'
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

/-- **The window stage for graphs, for every multiplicity bound `M₀ ≥ M`.** -/
theorem windowStageM_two_ge {q : ℕ} (hq : 2 < q) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ M₀ : ℕ, M ≤ M₀ →
      ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStageM q 2 M₀ Cst m₀ (sharpCost 2) :=
  windowStage_of_sparsify_levels_ge le_rfl hq (edgeSparsification_holds le_rfl hq)
    fun i hi h => absurd h (by omega)

end RefinedAbsorption.Sharp
