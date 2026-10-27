module

public import RequestProject.Extensions.PolynomialResolution
public import RequestProject.Extensions.NashWilliamsSchedule

/-! Axiom and statement check for the quantitative extensions.

The external endpoints `PippengerSpencerPolynomial` (`hPSPoly`) and `NashWilliamsExternal`
(`hNW`) are *definitions* (`Prop`s) and appear as explicit hypotheses of the theorems below;
standard axioms in the output do **not** mean these hypotheses have been discharged. -/

open RefinedAbsorption.Extensions RefinedAbsorption.External

-- External contracts (definitions, not theorems)
#check @PippengerSpencerPolynomial
#print PippengerSpencerPolynomial
#check @NashWilliamsExternal
#print NashWilliamsExternal

-- Endpoint 1: every Steiner system (only external hypothesis: hPSPoly)
#check @steiner_quantitatively_almost_resolvable
#print axioms steiner_quantitatively_almost_resolvable
-- Endpoint 2: existence for admissible n (only external hypothesis: hPSPoly)
#check @exists_quantitatively_almost_resolvable_steiner
#print axioms exists_quantitatively_almost_resolvable_steiner
-- Endpoint 3: Nash–Williams scheduling (external hypotheses: hPSPoly and hNW)
#check @nash_williams_scheduled_decomposition
#print axioms nash_williams_scheduled_decomposition

-- Reusable lemmas
#print axioms two_mul_degree_of_isTriangleDecomposition
#print axioms codegree_le_one_of_isTriangleDecomposition
#print axioms degree_eq_deg_singleton
#print axioms codegree_eq_deg_pair
