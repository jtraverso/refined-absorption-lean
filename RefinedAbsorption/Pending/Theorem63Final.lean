module
public import RefinedAbsorption.Pending.Theorem63
public import RefinedAbsorption.Pending.Theorem63One

/-!
# Theorem 6.3 of arXiv:2402.17855v1, proved

`theorem_6_3 : Faithful2024.Theorem_6_3`, by `theorem_6_3_two_le` (`r ≥ 2`) and
`theorem_6_3_one` (`r = 1`).
-/

@[expose] public section

namespace RefinedAbsorption.Pending

/-- **Theorem 6.3 of arXiv:2402.17855v1** (proved). -/
theorem theorem_6_3 : RefinedAbsorption.Faithful2024.Theorem_6_3 := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_6_3_one (by omega)
  · exact theorem_6_3_two_le h hrq

end RefinedAbsorption.Pending
