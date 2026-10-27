module
public import RequestProject.Window.Descent
public import RequestProject.LinkSpread.LevelOneFinal

/-!
# The window stage with a linear cost

The stage of the refine-down construction already formalised (`StagePropE` at precision `0`)
is a window stage with **linear** cost `a m = m`:

* `windowStage_id_of_stagePropE`: `StagePropE … 0 → WindowStage q r Cst' m₀ id`.  The new window is
  a quarter of the old one; the residue has bounded multiplicity, hence `(r-1)`-degrees `≤ M · |U|`.
* `windowStage_id_of_levelsE`: from the link levels in `ε`-form.
* **`windowStage_id_two`**, **`windowStage_id_three`**: unconditional for `r = 2` and `r = 3`.

So the window format of `Window/Descent.lean` is realised by the existing construction, and the
gap to the exact budget of Theorem 1.10 is exactly the cost of one window: `m` (proved, `r ≤ 3`)
versus `⌈m^{1-1/r}⌉` (needed by `nativeStrongMultiRefiners_of_windowStage`).
-/

@[expose] public section

namespace RefinedAbsorption.Window

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense

/-- **The existing stage is a window stage with linear cost.** -/
theorem windowStage_id_of_stagePropE {q r Cs Cst Cr B M : ℕ} (hr : 1 ≤ r)
    (h : StagePropE q r Cs Cst Cr B M 0) :
    WindowStage q r (Cr + Cst + B + M + 1) (4 * Cs + 4) id := by
  intro n E _ ends U X D hXr hXU hU hD1 hdeg
  obtain ⟨Z, hZU, hZc⟩ := exists_subset_card_eq (Nat.div_le_self U.card 4)
  have hUZ : U.card ≤ 8 * Z.card := by omega
  have hCs : Cs ≤ Z.card := by omega
  obtain ⟨E', _, g, ends', R, Y, 𝒲, Bd, hBd, hg, hends, hRf, h₁, hYR, hYZ, hmult, -, hdegR,
    hone, hpd⟩ := h n ends Z U X D hXr hXU hUZ hCs hD1 hdeg
  simp only [pow_zero, one_mul] at hBd
  have hYr : MIsRGraph r ends' Y := fun c hc => h₁.rgraph c (mem_union_right _ (hYR hc))
  have hZle : Z.card ≤ U.card := card_le_card hZU
  have hBdle : Bd ≤ (Cr + Cst + B + M + 1) * (D + id U.card) := by
    simp only [id]
    nlinarith
  refine ⟨E', inferInstance, g, ends', R, Y, 𝒲, Z, hg, hends, hRf, h₁.mono (by omega), hYR,
    by omega, hYZ, fun S hS => ?_, fun S hS => (hdegR S hS).trans hBdle, hone,
    fun S hS => (hpd S hS).trans hBdle⟩
  refine (mdeg_le_of_mult hYr hYZ hmult S (by omega)).trans ?_
  simp only [id]
  nlinarith

/-- **Window stage with linear cost from the link levels** (`ε`-form). -/
theorem windowStage_id_of_levelsE {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelE q r i) :
    ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStage q r Cst m₀ id := by
  obtain ⟨Cr, B, M, -, h⟩ := multiStageE hr hrq hL
  obtain ⟨Cs, Cst, -, h0⟩ := h 0
  exact ⟨_, _, by omega, windowStage_id_of_stagePropE (by omega) h0⟩

/-- **Window stage with linear cost for graphs** (`r = 2`), unconditional. -/
theorem windowStage_id_two {q : ℕ} (hq : 2 < q) :
    ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStage q 2 Cst m₀ id :=
  windowStage_id_of_levelsE le_rfl hq fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact (placedLinkLevel_last q 2 le_rfl hq).toE

/-- **Window stage with linear cost for `3`-graphs**, unconditional (level `1` is
`taggedLinkRefinersE_one`, level `2` is `placedLinkLevel_last`). -/
theorem windowStage_id_three {q : ℕ} (hq : 3 < q) :
    ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStage q 3 Cst m₀ id := by
  have h2 : PlacedLinkLevelE q 3 2 := (placedLinkLevel_last q 3 (by norm_num) hq).toE
  have h1 : PlacedLinkLevelE q 3 1 :=
    LinkSpread.placedLinkLevelE_of_tagged (LinkSpread.taggedLinkRefinersE_one (by norm_num) hq
      fun j hj hj3 => by
        obtain rfl : j = 1 := by omega
        exact h2)
  refine windowStage_id_of_levelsE (by norm_num) hq fun i hi hi3 => ?_
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · exact h1
  · exact h2

end RefinedAbsorption.Window
