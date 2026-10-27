module
public import RequestProject.Local.FlatEmbedMain
public import RequestProject.Local.StageZero
public import RequestProject.Local.TaggedA
public import RequestProject.LinkSpread.LevelOneFinal

/-!
# Theorem 3.8 for `3`-graphs from the flat theorem for graphs

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, §4 (Lemma 4.1, Theorem 4.4) for
`r = 3`.  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The link level `1` of `3`-graphs with the sublinear additive term `sharpCost 3 |Z|` is built in
two halves:

1. a tagged stage without additive term (`taggedStage0`, unconditional for `r = 3`) moves the
   link graphs of all outside vertices into a common half `Z₁` of the reserve, at cost `O(D)`;
2. the residues are refined by flat local refiners in uniformity `2`, randomly embedded into the
   other half of the reserve (`flatEmbedTagged`).

* **`taggedLinkRefinersA_three_one`**, **`placedLinkLevelA_three_one`**: the link level `1` of
  `3`-graphs with additive term `sharpCost 3`, from `FlatGraphRefiners (q - 1) a` for any additive
  term `a` dominated by `sharpCost 3`.
* **`nativeStrongMultiRefiners_three_of_flat`**: Theorem 3.8 for `r = 3` (strong multi-refiners
  with budget `C · max(D, n^{2/3} log n)`) from the flat Theorem 3.8 for graphs.
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread RefinedAbsorption.Sharp

/-- **Link level `1` of `3`-graphs, tagged form, with additive term `sharpCost 3`.** -/
theorem taggedLinkRefinersA_three_one {q : ℕ} (hq : 3 < q) (a : ℕ → ℕ)
    (hF : FlatGraphRefiners (q - 1) a) (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost 3 m') :
    TaggedLinkRefinersA q 3 1 (sharpCost 3) := by
  intro K
  obtain ⟨Cr, M, Cs, Cst, -, hstage⟩ := taggedStage0 (q := q) (r := 3) (i := 1) (by norm_num) hq
    (fun j hj hj3 => by
      obtain rfl : j = 1 := by omega
      exact placedLinkLevel_last q 3 (by norm_num) hq) (2 * K + 4)
  obtain ⟨C, Ch, hemb⟩ := flatEmbedTagged a hF ha (K + 1) M
  refine ⟨3 * (C + Cr), 4 * (Cs + Ch + q + K + 4), Cst + C * (Cst + 1), ?_⟩
  intro n E _ tg bd Z U X D htg hbd htgc hbdc hXU hUK hZq hD1 haD hCh hdeg
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
  have htags : (X.image tg).card ≤ K * Z.card := by
    refine (card_image_tg_le htgc fun x hx => ?_).trans hUK
    exact subset_union_left.trans (hXU x hx)
  obtain ⟨Bd₂, hBd₂, href⟩ := hout.prepend' (C := C + Cr) (by omega) htg htgc
    (fun Bd₂ => Bd₂ ≤ C * (Bd₁ + sharpCost 3 Z.card))
    (fun E₁ _ tg₁ bd₁ X₁ h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨Bd₂, hB, hR⟩ := hemb n Z Z₁ tg₁ bd₁ X₁ Bd₁ hZ₁Z (by omega)
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

/-- **Link level `1` of `3`-graphs with additive term `sharpCost 3`** (Lemma 4.1 for `r = 3`,
`i = 1`), from the flat theorem for graphs. -/
theorem placedLinkLevelA_three_one {q : ℕ} (hq : 3 < q) (a : ℕ → ℕ)
    (hF : FlatGraphRefiners (q - 1) a) (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost 3 m') :
    PlacedLinkLevelA q 3 1 (sharpCost 3) :=
  placedLinkLevelA_of_taggedA (taggedLinkRefinersA_three_one hq a hF ha)

/-- **Theorem 3.8 for `3`-graphs from the flat Theorem 3.8 for graphs.**  Strong multi-refiners
with budget `C · max(D, n^{2/3} log n)` exist for `3`-graphs as soon as flat local refiners exist
in uniformity `2` with an additive term dominated by `sharpCost 3`. -/
theorem nativeStrongMultiRefiners_three_of_flat {q : ℕ} (hq : 3 < q) (a : ℕ → ℕ)
    (hF : FlatGraphRefiners (q - 1) a) (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost 3 m') :
    NativeStrongMultiRefiners q 3 :=
  nativeStrongMultiRefiners_of_levels (by norm_num) hq fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact placedLinkLevelA_three_one hq a hF ha

end RefinedAbsorption.Local
