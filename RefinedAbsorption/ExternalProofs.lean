module
public import RefinedAbsorption.Extensions.PolynomialExternal
public import RefinedAbsorption.Upstream.PippengerSpencer.Polynomial
public import RequestProject.NW18.PaperIIAssembly

/-! Exact external contracts discharged by pinned proved sources. -/
@[expose] public section
namespace RefinedAbsorption.Assembly
open RefinedAbsorption.External

/-- The pinned Pippenger-Spencer proof discharges the exact retained contract. -/
theorem pippengerSpencerPolynomial : PippengerSpencerPolynomial :=
  Pseudorandom.chromatic_index_polynomial

/-- The pinned Nash-Williams proof discharges the exact retained contract. -/
theorem nashWilliamsExternal : NashWilliamsExternal :=
  NashWilliams18.PaperI.nash_williams_via_paperII

end RefinedAbsorption.Assembly
