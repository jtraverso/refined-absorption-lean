module
public import RequestProject.SparseChain.FlatEmbedS
public import RequestProject.SparseChain.WindowS
public import RequestProject.Local.LevelOneSharp

/-!
# Theorem 3.8 for `3`-graphs

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, §4 (Lemma 4.1, Theorem 4.4) for
`r = 3`, and Theorem 3.7 for graphs (with flatness and clique pieces).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `taggedLinkRefinersS_three_one`, `placedLinkLevelS_three_one`: the sparse link level `1` of
  `3`-graphs with additive term `sharpCost 3`, from sparse flat local refiners for graphs (same
  construction as `taggedLinkRefinersA_three_one`).
* **`nativeStrongMultiRefiners_three`**: Theorem 3.8 for `3`-graphs, unconditionally: strong
  multi-refiners with budget `C · max(D, n^{2/3} log n)` for every `q > 3`.
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread RefinedAbsorption.Sharp

/-- **Sparse link level `1` of `3`-graphs, tagged form, with additive term `sharpCost 3`.** -/
theorem taggedLinkRefinersS_three_one {q : ℕ} (hq : 3 < q) (a : ℕ → ℕ)
    (hF : FlatGraphRefinersS (q - 1) a) (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost 3 m') :
    TaggedLinkRefinersS q 3 1 (sharpCost 3) := by
  intro K
  obtain ⟨Cr, M, Cs, Cst, -, hstage⟩ := taggedStage0 (q := q) (r := 3) (i := 1) (by norm_num) hq
    (fun j hj hj3 => by
      obtain rfl : j = 1 := by omega
      exact placedLinkLevel_last q 3 (by norm_num) hq) (2 * K + 4)
  obtain ⟨C, Ch, hemb⟩ := flatEmbedTaggedS a hF ha (K + 1) M
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
  obtain ⟨Bd₁, hBd₁, hout⟩ := hstage n tg bd Z Z₁ (U ∪ Z) X D hZ₁Z htg hbd htgc hbdc
    subset_union_right (fun x hx => (hXU x hx).trans subset_union_left) hUZ (by omega) hD1
    (by omega) hdeg
  have hChB : Ch * Bd₁ ≤ (Z \ Z₁).card := by
    rw [hZ2]
    have h1 : Ch * Bd₁ ≤ Ch * Cst * D := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hBd₁
    have h2 : 2 * (Ch * Cst * D) ≤ Z.card := by
      calc 2 * (Ch * Cst * D) = (2 * (Ch * Cst)) * D := by ring
        _ ≤ (4 * (Cs + Ch + q + K + 4) + 2 * (Ch * Cst)) * D :=
            Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        _ ≤ Z.card := hChD
    omega
  have htags : (X.image tg).card ≤ K * Z.card := by
    refine (card_image_tg_le htgc fun x hx => ?_).trans hUK
    exact subset_union_left.trans (hXU x hx)
  obtain ⟨Bd₂, hBd₂, href⟩ := hout.prepend' (C := C + Cr) (by omega) htg htgc
    (fun Bd₂ => Bd₂ ≤ C * (Bd₁ + sharpCost 3 Z.card))
    (fun E₁ _ tg₁ bd₁ X₁ h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨Bd₂, hB, hR⟩ := hemb n Z Z₁ tg₁ bd₁ X₁ Bd₁ hZ₁Z (by omega) hChB
        (by
          rw [hZ₁c, hZ2]
          have : Z.card / 2 ≤ Z.card - Z.card / 2 := by omega
          exact this.trans (Nat.le_mul_of_pos_left _ (by omega)))
        (((card_le_card h5).trans htags).trans (Nat.mul_le_mul_right _ (by omega))) h1 h2 h3 h4
        h6 h7
      exact ⟨Bd₂, hB, hR.mono (by omega) fun _ _ => le_rfl⟩)
  refine ⟨Bd₁ + Bd₂, ?_, href.toTaggedRefOutE⟩
  have : C * (Bd₁ + sharpCost 3 Z.card) ≤ C * (Cst * D + D) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **Sparse link level `1` of `3`-graphs with additive term `sharpCost 3`** (Lemma 4.1 for
`r = 3`, `i = 1`). -/
theorem placedLinkLevelS_three_one {q : ℕ} (hq : 3 < q) (a : ℕ → ℕ)
    (hF : FlatGraphRefinersS (q - 1) a) (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost 3 m') :
    PlacedLinkLevelS q 3 1 (sharpCost 3) :=
  placedLinkLevelS_of_taggedS (taggedLinkRefinersS_three_one hq a hF ha)

/-- **Theorem 3.8 for `3`-graphs** (Delcourt–Postle): for every `q > 3` there is `C ≥ 1` such
that every `3`-graph `X` on `n ≥ n₀` vertices with `Δ₂(X) ≤ D ≤ n / C` has a strong
`C`-refined multi-refiner with budget `≤ C · max(D, n^{2/3} log n)`. -/
theorem nativeStrongMultiRefiners_three {q : ℕ} (hq : 3 < q) : NativeStrongMultiRefiners q 3 :=
  nativeStrongMultiRefiners_of_levelsS (by norm_num) hq fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact placedLinkLevelS_three_one hq (sharpCost 2)
      (flatGraphRefinersS_of_cliqueOmniS (RefinedAbsorption.FlatOmni.flatCliqueOmniAbsorbersS_two
        (by omega)))
      fun _ _ h => sharpCost_two_le_three h

end RefinedAbsorption.Local
