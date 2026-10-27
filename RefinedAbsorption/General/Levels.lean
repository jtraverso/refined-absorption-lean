module
public import RefinedAbsorption.General.EmbedGen
public import RefinedAbsorption.General.FlatOmniK
public import RefinedAbsorption.General.StageS
public import RefinedAbsorption.Placement.Existence

/-!
# The sparse link levels in every uniformity, and Theorem 3.8

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Lemma 4.1, Theorem 4.4, Lemma 3.13 and
Theorem 3.8, by induction on the uniformity.  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

* `taggedLinkRefinersS_gen`: the sparse tagged link level `i` of `r`-graphs from the higher levels
  `j > i` and from Theorem 3.7 in uniformity `r - i`.
* **`placedLinkLevelS_all`**: all sparse link levels `PlacedLinkLevelS q r i (sharpCost r)`,
  `1 ≤ i < r - 1`, by induction on `r` and downward induction on `i`.
* **`nativeStrongMultiRefiners_all`**: Theorem 3.8 for every `q > r ≥ 2`.
* **`steinerExistence`**: the Existence Conjecture for Steiner systems.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread RefinedAbsorption.Sharp
  RefinedAbsorption.Local RefinedAbsorption.Window

/-- `sharpCost` grows with the uniformity. -/
theorem sharpCost_le_of_le {k r m m' : ℕ} (hk : 2 ≤ k) (hkr : k ≤ r) (h : m ≤ m') :
    sharpCost k m ≤ sharpCost r m' := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr' : (k : ℝ) ≤ r := by exact_mod_cast hkr
  have hkr' : 1 / (r : ℝ) ≤ 1 / (k : ℝ) := one_div_le_one_div_of_le (by linarith) hr'
  have hk2 : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
  have h1 : winCost k m ≤ winCost r m := by
    unfold winCost
    apply Nat.ceil_mono
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h0 : (1 : ℝ) - 1 / (k : ℝ) ≠ 0 := by linarith
      have h2 : (1 : ℝ) - 1 / (r : ℝ) ≠ 0 := by linarith
      rw [Nat.cast_zero, Real.zero_rpow h0, Real.zero_rpow h2]
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      exact Real.rpow_le_rpow_of_exponent_le this (by linarith)
  have h2 := winCost_mono (r := r) (by omega) h
  unfold sharpCost
  exact Nat.mul_le_mul (h1.trans h2) (Nat.succ_le_succ (Nat.log_mono_right h))

/-- **Sparse tagged link level `i` of `r`-graphs, with additive term `sharpCost r`.** -/
theorem taggedLinkRefinersS_gen {q r i : ℕ} (hi : 1 ≤ i) (hir : i + 2 ≤ r) (hrq : r < q)
    (hL : ∀ j, i < j → j < r - 1 → PlacedLinkLevelS q r j (sharpCost r))
    (hF : FlatOmniK (q - i) (r - i) (sharpCost (r - i))) :
    TaggedLinkRefinersS q r i (sharpCost r) := by
  intro K
  obtain ⟨Cr, M, Cs, Cst, -, hstage⟩ := taggedStage0S (q := q) (r := r) (i := i)
    (a := sharpCost r) (by omega) hrq
    (fun j hj hjr => by
      rcases Nat.lt_or_ge (i + j) (r - 1) with h | h
      · exact hL (i + j) (by omega) h
      · have e : i + j = r - 1 := by omega
        rw [e]
        exact (placedLinkLevel_last q r (by omega) hrq).toS _) (2 * K + 4)
  obtain ⟨C, Ch, hemb⟩ := flatEmbedGen hi hir (sharpCost (r - i)) hF
    (fun m m' h => sharpCost_le_of_le (by omega) (by omega) h) (K + 1) M
  refine ⟨3 * (C + Cr), 4 * (Cs + Ch + q + K + 4) + 2 * (Ch * Cst), Cst + C * (Cst + 1), ?_⟩
  intro n E _ tg bd Z U X D htg hbd htgc hbdc hXU hUK hZq hD1 haD hChD hdeg
  have hCh : 4 * (Cs + Ch + q + K + 4) ≤ Z.card :=
    le_trans (by omega) (le_trans (Nat.le_mul_of_pos_right _ hD1) hChD)
  obtain ⟨Z₁, hZ₁Z, hZ₁c⟩ := exists_subset_card_eq (s := Z) (n := Z.card / 2)
    (Nat.div_le_self _ _)
  have hZ2 : (Z \ Z₁).card = Z.card - Z.card / 2 := by rw [card_sdiff_of_subset hZ₁Z, hZ₁c]
  have hUZ : (U ∪ Z).card ≤ (2 * K + 4) * Z₁.card := by
    have h1 := card_union_le U Z
    rw [hZ₁c]
    have h2 : (K + 1) * Z.card ≤ (2 * K + 4) * (Z.card / 2) := by
      have : Z.card ≤ 2 * (Z.card / 2) + 1 := by omega
      nlinarith
    nlinarith
  have haZ₁ : sharpCost r Z₁.card ≤ D :=
    (sharpCost_mono (by omega) (card_le_card hZ₁Z)).trans haD
  have hCsD : Cs * D ≤ Z₁.card := by
    rw [hZ₁c]
    have : 2 * (Cs * D) ≤ Z.card := by
      refine le_trans ?_ hChD
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨Bd₁, hBd₁, hout⟩ := hstage n tg bd Z Z₁ (U ∪ Z) X D hZ₁Z htg hbd htgc hbdc
    subset_union_right (fun x hx => (hXU x hx).trans subset_union_left) hUZ (by omega) hD1
    haZ₁ hCsD hdeg
  have hChB : Ch * Bd₁ ≤ (Z \ Z₁).card := by
    rw [hZ2]
    have h1 : Ch * Bd₁ ≤ Ch * Cst * D := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hBd₁
    have h2 : 2 * (Ch * Cst * D) ≤ Z.card := by
      calc 2 * (Ch * Cst * D) = (2 * (Ch * Cst)) * D := by ring
        _ ≤ (4 * (Cs + Ch + q + K + 4) + 2 * (Ch * Cst)) * D :=
            Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        _ ≤ Z.card := hChD
    omega
  have hUt : ∀ T ∈ X.image tg, T ⊆ U := by
    intro T hT
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hT
    exact subset_union_left.trans (hXU x hx)
  obtain ⟨Bd₂, hBd₂, href⟩ := hout.prepend' (C := C + Cr) (by omega) htg htgc
    (fun Bd₂ => Bd₂ ≤ C * (Bd₁ + sharpCost r Z.card))
    (fun E₁ _ tg₁ bd₁ X₁ h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨Bd₂, hB, hR⟩ := hemb n Z Z₁ U tg₁ bd₁ X₁ Bd₁ hZ₁Z (by omega) hChB
        (by
          rw [hZ₁c, hZ2]
          have : Z.card / 2 ≤ Z.card - Z.card / 2 := by omega
          exact this.trans (Nat.le_mul_of_pos_left _ (by omega)))
        (hUK.trans (Nat.mul_le_mul_right _ (by omega)))
        (fun x hx => hUt _ (h5 (mem_image_of_mem _ hx))) h1 h2 h3 h4 h6 h7
      exact ⟨Bd₂, hB, hR.mono (by omega) fun _ _ => le_rfl⟩)
  refine ⟨Bd₁ + Bd₂, ?_, href.toTaggedRefOutE⟩
  have : C * (Bd₁ + sharpCost r Z.card) ≤ C * (Cst * D + D) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **All sparse link levels** with additive term `sharpCost r`. -/
theorem placedLinkLevelS_all :
    ∀ r q i : ℕ, 2 ≤ r → r < q → 1 ≤ i → i < r - 1 → PlacedLinkLevelS q r i (sharpCost r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
    intro q i hr hrq hi hir
    -- downward induction on `i`
    suffices h : ∀ t, ∀ i, 1 ≤ i → i < r - 1 → r - 1 - i = t →
        PlacedLinkLevelS q r i (sharpCost r) from h _ i hi hir rfl
    intro t
    induction t using Nat.strong_induction_on with
    | _ t iht =>
      intro i hi hir ht
      refine placedLinkLevelS_of_taggedS (taggedLinkRefinersS_gen hi (by omega) hrq
        (fun j hij hjr => iht (r - 1 - j) (by omega) j (by omega) hjr rfl) ?_)
      refine flatOmniK_of_levels (by omega) (by omega) fun j hj hjk => ?_
      exact ihr (r - i) (by omega) (q - i) j (by omega) (by omega) hj hjk

/-- **Theorem 3.8 (Multi-Refiner Theorem)** for every `q > r ≥ 2`: strong `C`-refined
multi-refiners with budget `C · max(D, n^{1-1/r} log n)` whenever `Δ_{r-1}(X) ≤ D ≤ n / C`. -/
theorem nativeStrongMultiRefiners_all {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    NativeStrongMultiRefiners q r :=
  nativeStrongMultiRefiners_of_levelsS hr hrq fun i hi hir =>
    placedLinkLevelS_all r q i hr hrq hi hir

/-- **The Existence Conjecture for Steiner systems** (Keevash; proof by refined absorption,
Delcourt–Postle). -/
theorem steinerExistence : SteinerExistenceConjecture :=
  steinerExistence_of_native fun _ _ hr hrq => nativeStrongMultiRefiners_all hr hrq

end RefinedAbsorption.General
