module
public import RefinedAbsorption.Original2024.FlatOne

/-!
# The flat multi-refiner for a labelled multigraph input (sparse regime)

`Original2024.multiRefinerFlat_two_le` proves the flat multi-refiner conclusion for a *simple*
input `X ⊆ K_n^r`.  Its two stages (refine down into `Z ⊆ Y`, then the local Theorem 3.7 inside
`Y`) already work for labelled multigraphs; **`flatLabelled_two_le`** is the same proof for an
arbitrary labelled multigraph `X` (no injectivity, no multiplicity bound) with
`Δ_{r-1}(X) ≤ D` and `Cf · D ≤ n`, and a prescribed `Y` with `n ≤ 3 |Y|`: every new copy meets
`Y`.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Sharp
  RefinedAbsorption.General RefinedAbsorption.Original2024

set_option maxHeartbeats 4000000 in
/-- **Flat multi-refiners for labelled multigraphs, `q > r ≥ 2`, sparse regime.** -/
theorem flatLabelled_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    ∃ Cf m₁ : ℕ, 1 ≤ Cf ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (X : Finset E) (D : ℕ), m₁ ≤ n → MIsRGraph r ends X →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) → Cf * D ≤ n →
      ∀ Y : Finset (Fin n), n ≤ 3 * Y.card →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
        (R : Finset E') (𝒲 : Finset (Finset E')),
        Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
        IsMultiRefiner q r Cf ends' (X.image g) R 𝒲 ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          mdeg ends' R S ≤ Cf * (D + 1 + sharpCost r n)) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          pdeg ends' 𝒲 S ≤ Cf * (D + 1 + sharpCost r n)) ∧
        (∀ c ∈ R, (ends' c ∩ Y).Nonempty) := by
  have hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelS q r i (sharpCost r) := fun i hi hir => by
    rcases Nat.lt_or_ge i (r - 1) with h | h
    · exact placedLinkLevelS_all r q i hr hrq hi h
    · obtain rfl : i = r - 1 := by omega
      exact (placedLinkLevel_last q r hr hrq).toS _
  obtain ⟨Cs, C₁, M, -, -, hstage⟩ := multiStageS_M hr hrq hL
  have hF : FlatOmniK q r (sharpCost r) :=
    flatOmniK_of_levels hr hrq fun j hj hjr => placedLinkLevelS_all r q j hr hrq hj hjr
  obtain ⟨C₂, Ch, homni⟩ := hF (M + 1)
  set A := Cs + Ch * C₁ + Ch with hA
  obtain ⟨m₀, hm₀⟩ := FlatOmni.exists_mul_sharpPot_le hr (2 * A)
  set Cb := C₁ + C₂ * (C₁ + 1) + C₂ * (C₁ + C₂ * (C₁ + 1)) with hCb
  set Cf := 24 * A + 32 * (Cb + C₁ + C₂ + 1) with hCf
  refine ⟨Cf, 24 * A + 6 * m₀ + 12, by omega, ?_⟩
  intro n E _ ends X Df hn hXr hXD hCD Y hY
  set Dn := Df + 1 with hDn'
  have hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ Dn := by
    intro S hS
    have := hXD S hS
    omega
  -- the two halves of `Y`
  obtain ⟨Z, hZY, hZc⟩ := exists_subset_card_eq (s := Y) (Nat.div_le_self Y.card 2)
  set P := Y \ Z with hP
  have hPc : P.card = Y.card - Z.card := card_sdiff_of_subset hZY
  have hZ6 : n ≤ 6 * Z.card + 3 := by omega
  have hU8 : n ≤ 8 * Z.card := by omega
  have hZP : Z.card ≤ P.card := by omega
  have hZm : m₀ ≤ Z.card := by omega
  have hZ1 : 1 ≤ Z.card := by omega
  have hZn : Z.card ≤ n := (card_le_card (subset_univ Z)).trans (by simp)
  have hPn : P.card ≤ n := (card_le_card (subset_univ P)).trans (by simp)
  set sZ := sharpCost r Z.card with hsZ
  have hsZA : 2 * A * sZ ≤ Z.card := by
    have h1 := hm₀ Z.card hZm
    have h2 : sZ ≤ sharpPot r Z.card := sharpCost_le_sharpPot r hZ1
    have h3 : 2 * A * sZ ≤ 2 * A * sharpPot r Z.card := Nat.mul_le_mul_left _ h2
    omega
  set D' := Dn + sZ with hD'
  have hAD : A * D' ≤ Z.card := by
    have h1 : 24 * (A * Df) ≤ n := by
      rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
    have h2 : A * Dn = A * Df + A := by rw [hDn']; ring
    have : A * D' = A * Dn + A * sZ := by rw [hD']; ring
    have h4 : 2 * (A * sZ) ≤ Z.card := by rw [← mul_assoc]; exact hsZA
    omega
  have hD'1 : 1 ≤ D' := by omega
  have hCsD : Cs * D' ≤ Z.card :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) hAD
  have hChD : Ch * (C₁ * D') ≤ P.card := by
    have : Ch * (C₁ * D') ≤ A * D' := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by rw [hA, mul_comm Ch C₁]; omega)
    omega
  have hCh : Ch ≤ P.card := by
    have : Ch ≤ A * D' := le_trans (by omega) (Nat.mul_le_mul_left A hD'1)
    omega
  -- stage 1: refine down into `Z`
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁Z, hY₁m, -, hdeg₁,
    hone₁, hpd₁, hmeet₁⟩ := hstage n ends Z univ X D' hXr (fun _ _ => subset_univ _)
      (by rw [card_univ, Fintype.card_fin]; exact hU8) hCsD hD'1 (by omega)
      (fun S hS => le_trans (hdeg S hS) (by omega))
  have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  have hdegY₁ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ C₁ * D' :=
    fun S hS => (mdeg_mono _ hY₁R S).trans (hdeg₁ S hS)
  -- stage 2: Theorem 3.7 inside `Z ∪ P`
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hR₂loc, hdeg₂, -, hcl₂, -⟩ :=
    homni n ends₁ Z P Y₁ (C₁ * D') disjoint_sdiff
      (le_trans hZP (Nat.le_mul_of_pos_left _ (by omega))) hCh hChD hY₁r hY₁Z hdegY₁
      (fun e => (hY₁m e).trans (Nat.le_succ M))
  have hcomp := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₁
    (hY₁R.trans subset_union_right) h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂ hR₂f
  rw [image_image] at hcomp hone
  -- the budget
  set Bd := Dn + sharpCost r n with hBd
  have hsZn : sZ ≤ sharpCost r n := sharpCost_mono (by omega) hZn
  have hsPn : sharpCost r P.card ≤ sharpCost r n := sharpCost_mono (by omega) hPn
  have hD'B : D' ≤ Bd := by omega
  have hendsX : ∀ e, ends₂ ((g₂ ∘ g₁) e) = ends e := fun e => by simp [hends₂, hends₁]
  have hdegR : ∀ S : Finset (Fin n), S.card = r - 1 →
      mdeg ends₂ (R₁.image g₂ ∪ R₂) S ≤ (C₁ + C₂ * (C₁ + 1)) * Bd := by
    intro S hS
    refine (Dense.mdeg_union_le _ _ _ S).trans ?_
    rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    have h1 := hdeg₁ S hS
    have h2 := hdeg₂ S hS
    have e1 : C₁ * D' ≤ C₁ * Bd := Nat.mul_le_mul_left _ hD'B
    have e2 : C₂ * (C₁ * D' + sharpCost r P.card) ≤ C₂ * (C₁ * Bd + Bd) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : (C₁ + C₂ * (C₁ + 1)) * Bd = C₁ * Bd + C₂ * (C₁ * Bd + Bd) := by ring
    omega
  have hCbB : (C₁ + C₂ * (C₁ + 1)) * Bd ≤ Cf * Bd := Nat.mul_le_mul_right _ (by omega)
  have hpdeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      pdeg ends₂ (𝒲₁.image (image g₂) ∪ 𝒲₂) S ≤ Cf * Bd := by
    intro S hS
    have hS0 : S.Nonempty := by rw [← card_pos, hS]; omega
    refine (pdeg_union_le _ _ _ S).trans ?_
    have h1 := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
    have h2 := pdeg_le_of_clique h₂ hcl₂ (by omega) hS0
    have h3 : mdeg ends₂ (Y₁.image g₂ ∪ R₂) S ≤ C₁ * Bd + C₂ * (C₁ * Bd + Bd) := by
      refine (Dense.mdeg_union_le _ _ _ S).trans ?_
      rw [mdeg_image_eq (A := Y₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
      have := hdegY₁ S hS
      have := hdeg₂ S hS
      have e1 : C₁ * D' ≤ C₁ * Bd := Nat.mul_le_mul_left _ hD'B
      have e2 : C₂ * (C₁ * D' + sharpCost r P.card) ≤ C₂ * (C₁ * Bd + Bd) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have h4 : C₂ * mdeg ends₂ (Y₁.image g₂ ∪ R₂) S ≤
        C₂ * (C₁ * Bd + C₂ * (C₁ * Bd + Bd)) := Nat.mul_le_mul_left _ h3
    have e1 : C₁ * D' ≤ C₁ * Bd := Nat.mul_le_mul_left _ hD'B
    have e3 : Cb * Bd = C₁ * Bd + C₂ * (C₁ + 1) * Bd +
        C₂ * (C₁ * Bd + C₂ * (C₁ * Bd + Bd)) := by rw [hCb]; ring
    have e4 : Cb * Bd ≤ Cf * Bd := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨E₂, inferInstance, g₂ ∘ g₁, ends₂, R₁.image g₂ ∪ R₂, 𝒲₁.image (image g₂) ∪ 𝒲₂,
    hg₂.comp hg₁, hendsX, ?_, hcomp.mono (by omega), hone, fun S hS => (hdegR S hS).trans hCbB,
    hpdeg, ?_⟩
  · intro c hc x
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      intro hx
      exact hR₁f c₁ hc₁ x (hg₂ hx)
    · exact hR₂f c h _
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      rw [hends₂]
      obtain ⟨v, hv⟩ := hmeet₁ c₁ hc₁
      exact ⟨v, mem_inter.2 ⟨(mem_inter.1 hv).1, hZY (mem_inter.1 hv).2⟩⟩
    · obtain ⟨v, hv⟩ := (hR₂loc c h).2
      exact ⟨v, mem_inter.2 ⟨(mem_inter.1 hv).1, sdiff_subset (mem_inter.1 hv).2⟩⟩

end RefinedAbsorption.Faithful2024
