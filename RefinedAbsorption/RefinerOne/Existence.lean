module
public import RefinedAbsorption.RefinerOne.Instance
public import RefinedAbsorption.Nibble.Bridge

/-!
# Reducing the remaining hypothesis to uniformities `r ≥ 2`

Since the case `r = 1` of `RefinerWithAbsorbers` is proved (`refinerAbsorbersFor_one`), the
Existence Conjecture follows from the instances with `r ≥ 2` alone.
-/

@[expose] public section

namespace RefinedAbsorption

/-- `RefinerWithAbsorbers` follows from its instances with `r ≥ 2`. -/
theorem refinerWithAbsorbers_of_two_le
    (h : ∀ q r : ℕ, 2 ≤ r → r < q → RefinerAbsorbersFor q r) : RefinerWithAbsorbers := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · obtain rfl : r = 1 := by omega
    exact refinerAbsorbersFor_one (by omega)
  · exact h q r hr2 hrq

/-- **The Existence Conjecture** from refined refiners with attached absorbers for `r ≥ 2`. -/
theorem steinerExistence_of_refinerAbsorbers_two_le
    (h : ∀ q r : ℕ, 2 ≤ r → r < q → RefinerAbsorbersFor q r) : SteinerExistenceConjecture :=
  steinerExistence_of_refinerWithAbsorbers (refinerWithAbsorbers_of_two_le h)

end RefinedAbsorption
