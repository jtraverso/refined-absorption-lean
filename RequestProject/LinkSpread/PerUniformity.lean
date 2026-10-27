module
public import RequestProject.LinkSpread.LevelOneFinal

/-!
# Steiner systems for a fixed uniformity from the tagged link levels

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`steinerExistence_of_tagged_two` derives the whole Existence Conjecture from the tagged link
levels `2 ≤ i < r - 1` for **all** `q` and `r` at once.  Here the same reduction is stated for one
fixed pair `(q, r)`:

* **`steinerExistenceFor_of_tagged_two`**: for `3 ≤ r < q`, Steiner systems `S(n, q, r)` exist for
  all large admissible `n` as soon as `TaggedLinkRefinersE q r i` holds for `2 ≤ i < r - 1`
  (levels of the same `q` and `r` only).  Level `1` is `taggedLinkRefinersE_one` and the last level
  is `placedLinkLevel_last`; no other hypothesis is used (in particular no nibble hypothesis: the
  nibble with reserves is proved in `RequestProject/Nibble/`).
* **`steinerExistenceFor_four_of_tagged`**: `S(n, q, 4)` from the single level
  `TaggedLinkRefinersE q 4 2`.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

/-- **Steiner systems for fixed `q` and `r`** from the tagged link levels `2 ≤ i < r - 1` of the
same `q` and `r`. -/
theorem steinerExistenceFor_of_tagged_two {q r : ℕ} (hr : 3 ≤ r) (hrq : r < q)
    (h : ∀ i, 2 ≤ i → i < r - 1 → TaggedLinkRefinersE q r i) :
    RefinedAbsorption.Dense.SteinerExistenceFor q r := by
  have hP : ∀ i, 2 ≤ i → i < r - 1 → PlacedLinkLevelE q r i :=
    fun i hi hir => placedLinkLevelE_of_tagged (h i hi hir)
  refine RefinedAbsorption.Dense.steinerExistenceFor_of_levelsE hr hrq fun i hi hir => ?_
  rcases Nat.lt_or_ge i 2 with hi2 | hi2
  · obtain rfl : i = 1 := by omega
    refine placedLinkLevelE_of_tagged (taggedLinkRefinersE_one (by omega) hrq fun j hj hjr => ?_)
    rcases Nat.lt_or_ge (1 + j) (r - 1) with h' | h'
    · exact hP (1 + j) (by omega) h'
    · obtain h'' : 1 + j = r - 1 := by omega
      rw [h'']
      exact (placedLinkLevel_last q r (by omega) hrq).toE
  · exact hP i hi2 hir

/-- **`S(n, q, 4)`** for all large admissible `n`, from the single tagged link level
`TaggedLinkRefinersE q 4 2`. -/
theorem steinerExistenceFor_four_of_tagged {q : ℕ} (hq : 4 < q)
    (h : TaggedLinkRefinersE q 4 2) : RefinedAbsorption.Dense.SteinerExistenceFor q 4 :=
  steinerExistenceFor_of_tagged_two (by norm_num) hq fun i hi hir => by
    obtain rfl : i = 2 := by omega
    exact h

end RefinedAbsorption.LinkSpread
