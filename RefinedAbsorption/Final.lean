module
public import RefinedAbsorption.Main
public import RefinedAbsorption.General.Levels

/-!
# The main results of the survey, unconditionally

This file collects, without any hypotheses, the results of the survey *Refined Absorption*
(L. Postle) that are proved in this project:

* `theorem_3_8`: the Multi-Refiner Theorem (Theorem 3.8 of Delcourt–Postle) for `q > r ≥ 2`;
* `theorem_1_10`: the refined efficient omni-absorber theorem (Theorem 1.10);
* `theorem_1_7`: existence of absorbers (Theorem 1.7);
* `lemma_2_2`: the boost lemma (Lemma 2.2);
* `corollary_2_4`: the nibble with reserves (Corollary 2.4);
* `existenceConjecture_steiner`: the Existence Conjecture for Steiner systems (`λ = 1`);
* `kirkman`: Kirkman's theorem.
-/

@[expose] public section

namespace RefinedAbsorption.Final

open RefinedAbsorption

/-- **Theorem 3.8 (Multi-Refiner Theorem)** for every `q > r ≥ 2`. -/
theorem theorem_3_8 {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    Placement.NativeStrongMultiRefiners q r :=
  General.nativeStrongMultiRefiners_all hr hrq

/-- Refined refiners with attached absorbers and the required maximum degree exist. -/
theorem refinerWithAbsorbers_holds : RefinerWithAbsorbers :=
  refinerWithAbsorbers_of_two_le fun _ _ hr hrq =>
    Placement.refinerAbsorbersFor_of_native hr hrq (theorem_3_8 hr hrq)

/-- **Theorem 1.10 (Refined efficient omni-absorber, Delcourt–Postle).** -/
theorem theorem_1_10 : RefinedEfficientOmniAbsorber :=
  refinedEfficientOmniAbsorber_of_refinerWithAbsorbers refinerWithAbsorbers_holds

/-- **Theorem 1.7 (existence of absorbers).** -/
theorem theorem_1_7 : AbsorberExistence := Absorber17.absorberExistence

/-- **Lemma 2.2 (Boost).** -/
theorem lemma_2_2 : BoostLemma := boostLemma

/-- **Corollary 2.4 (Nibble with reserves for designs)**, as stated in the survey. -/
theorem corollary_2_4 : NibbleWithReserves := nibbleWithReserves_proved

/-- **The Existence Conjecture for Steiner systems** (`λ = 1`), via the refined absorption proof
of Section 2 of the survey: Theorem 1.10 together with Corollary 2.4. -/
theorem existenceConjecture_steiner : SteinerExistenceConjecture :=
  steinerExistence_of_omniAbsorber_nibbleWithReserves theorem_1_10 corollary_2_4

/-- **Kirkman's theorem.** -/
theorem kirkman : KirkmanTheorem := kirkmanTheorem

end RefinedAbsorption.Final
