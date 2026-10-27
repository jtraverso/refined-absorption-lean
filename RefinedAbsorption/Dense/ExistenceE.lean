module
public import RefinedAbsorption.Dense.NativeE
public import RefinedAbsorption.Dense.Existence

/-!
# Steiner systems from link levels in `ε`-form

* **`steinerExistenceFor_of_levelsE`**: for `3 ≤ r < q`, Steiner systems `S(r, q, n)` exist for
  all large admissible `n` as soon as `PlacedLinkLevelE q r i` holds for `1 ≤ i < r - 1`.
* **`steinerExistence_of_levelsE`**: the Existence Conjecture for Steiner systems from these
  levels.

`PlacedLinkLevelE` is implied by `PlacedLinkLevel` and by `PlacedLinkLevelA` with a sublinear
additive term, so these statements contain `steinerExistenceFor_of_levels`,
`steinerExistenceFor_of_levelsA` and `steinerExistence_of_levels`.
-/

@[expose] public section

namespace RefinedAbsorption.Dense

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

/-- **Steiner systems from link levels in `ε`-form.** -/
theorem steinerExistenceFor_of_levelsE {q r : ℕ} (hr : 3 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelE q r i) : SteinerExistenceFor q r :=
  steinerExistenceFor_of_weakOmni (by omega) hrq weakReservesLemma
    (weakOmniAbsorberFor_of_native (by omega) hrq
      (nativeWeakStrongMultiRefiners_of_levelsE (by omega) hrq hL)) boostLemma
    nibbleWithReservesGen_proved

/-- **`S(3, q, n)`** exist for all large admissible `n`, provided the single intermediate level
`i = 1` holds in `ε`-form. -/
theorem steinerExistenceFor_threeE {q : ℕ} (hq : 3 < q) (hL : PlacedLinkLevelE q 3 1) :
    SteinerExistenceFor q 3 :=
  steinerExistenceFor_of_levelsE le_rfl hq (fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact hL)

/-- **The Existence Conjecture for Steiner systems**, conditional only on the intermediate link
levels `1 ≤ i < r - 1` (`r ≥ 3`) in `ε`-form. -/
theorem steinerExistence_of_levelsE
    (h : ∀ q r i : ℕ, 3 ≤ r → r < q → 1 ≤ i → i < r - 1 → PlacedLinkLevelE q r i) :
    SteinerExistenceConjecture := by
  intro q r hr hrq
  rcases Nat.eq_or_lt_of_le hr with rfl | hr3
  · exact steinerExistenceFor_two hrq
  · exact steinerExistenceFor_of_levelsE hr3 hrq (fun i hi hir => h q r i hr3 hrq hi hir)

end RefinedAbsorption.Dense
