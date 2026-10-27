module
public import RequestProject.Placement.Assembly
public import RequestProject.RefinerOne.Existence

/-!
# The Existence Conjecture from the native refine-down construction

With both placements proved (fake edges and absorbers inside `K_n^r`), the only remaining input of
the refined absorption proof is the native construction `NativeStrongMultiRefiners q r` for
`r ≥ 2`.  This file records the resulting conditional statement; it does **not** prove the native
construction.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

/-- **The Existence Conjecture, conditional only on the native refine-down construction.** -/
theorem steinerExistence_of_native
    (h : ∀ q r : ℕ, 2 ≤ r → r < q → NativeStrongMultiRefiners q r) :
    SteinerExistenceConjecture :=
  steinerExistence_of_refinerAbsorbers_two_le fun q r hr hrq =>
    refinerAbsorbersFor_of_native hr hrq (h q r hr hrq)

end RefinedAbsorption.Placement
