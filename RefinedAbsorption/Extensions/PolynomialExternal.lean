module
public import RefinedAbsorption.MathlibImports

/-!
# Explicit external interfaces for the quantitative extensions

This file only contains **definitions** (`Prop`-valued contracts and the vocabulary they are
phrased in).  Nothing here is proved: the two propositions below are used exclusively as explicit
hypotheses (`hPSPoly`, `hNW`) of the theorems in `Extensions/PolynomialResolution.lean` and
`Extensions/NashWilliamsSchedule.lean`.

* `PippengerSpencerPolynomial` transcribes the endpoint
  `PippengerSpencer.chromatic_index_polynomial` of
  `jtraverso/pippenger-spencer@b19273396d369332fb489fe07e61e27c9e7f9233` (`Solution.lean`).
* `NashWilliamsExternal` transcribes the endpoint `NashWilliamsTheorem.nash_williams` of
  `jtraverso/nash-williams-lean@2603197abdbf0a600ec663f6f046f70fbd209d4a`
  (`Challenge.lean` / `Solution.lean`).

The auxiliary definitions (`IsUniform`, `degree`, `codegree`, `IsProperEdgeColouring`,
`IsTriangle`, `IsTriangleDecomposition`, `HasTriangleDecomposition`, `IsTriangleDivisible`) have
the same bodies as in those files, inside the namespaces
`RefinedAbsorption.External.PippengerSpencer` and `RefinedAbsorption.External.NashWilliams`.
The local assembly adapter is therefore expected to be definitional (`Iff.rfl` / `id`) after
replacing the namespace prefix.
-/

@[expose] public section

namespace RefinedAbsorption.External

open Finset

namespace PippengerSpencer

variable {V : Type*} [DecidableEq V]

/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- The degree `deg_H(v)`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- The codegree `deg_H(uv)`: the number of edges containing both `u` and `v`. -/
def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- A proper edge colouring of `H` with `m` colours: edges of the same colour are disjoint. -/
def IsProperEdgeColouring (H : Finset (Finset V)) (m : ℕ) (c : Finset V → Fin m) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → c e = c f → Disjoint e f

end PippengerSpencer

open PippengerSpencer in
/-- **External contract: chromatic index under polynomial codegrees**
(`PippengerSpencer.chromatic_index_polynomial`, proved in the external repository, *not* here).
For `k ≥ 2` and `0 < δ < 1` there are `γ > 0` and `D₀` such that every `k`-uniform hypergraph
with maximum degree at most `D ≥ D₀`, codegrees at most `D^{1-δ}` and at most `exp(D^γ)` edges
has a proper edge colouring with at most `D + D^{1-γ}` colours.  No near-regularity and no lower
bound on degrees is required, but the exponential bound on the number of edges is part of the
contract. -/
def PippengerSpencerPolynomial : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (δ : ℝ), 0 < δ → δ < 1 →
    ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H k → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ D ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (D ^ γ) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ D + D ^ (1 - γ) ∧
        IsProperEdgeColouring H m c

namespace NashWilliams

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A *triangle* of `G` is a 3-clique, i.e. a 3-element set of pairwise adjacent vertices. -/
abbrev IsTriangle (G : SimpleGraph V) (t : Finset V) : Prop := G.IsNClique 3 t

/-- A *triangle decomposition* of `G`: a family `D` of triangles of `G` such that every edge of
`G` lies in exactly one triangle of `D`. -/
def IsTriangleDecomposition (G : SimpleGraph V) (D : Finset (Finset V)) : Prop :=
  (∀ t ∈ D, IsTriangle G t) ∧ ∀ u v, G.Adj u v → ∃! t, t ∈ D ∧ u ∈ t ∧ v ∈ t

/-- `G` admits a triangle decomposition. -/
def HasTriangleDecomposition (G : SimpleGraph V) : Prop :=
  ∃ D, IsTriangleDecomposition G D

/-- `G` is `K₃`-divisible: `3 ∣ e(G)` and every vertex has even degree. -/
def IsTriangleDivisible (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)

end NashWilliams

/-- **External contract: the Nash–Williams theorem for large graphs**
(`NashWilliamsTheorem.nash_williams`, proved in the external repository, *not* here).
There is `N` such that every finite simple graph on `n ≥ N` vertices which is triangle-divisible
and satisfies `3 n ≤ 4 δ(G)` has a triangle decomposition. -/
def NashWilliamsExternal : Prop :=
  ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
      3 * Fintype.card V ≤ 4 * G.minDegree →
        NashWilliams.HasTriangleDecomposition G

end RefinedAbsorption.External
