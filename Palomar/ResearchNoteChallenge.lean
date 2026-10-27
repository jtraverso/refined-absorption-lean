/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
-/
module
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.Zify
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Polynomial.DegreeLT
@[expose] public section
/-! Standalone statements. The expected `sorry` placeholders occur only in
Challenge modules. Source correspondence: provenance/palomar-extractions.json. -/
namespace RefinedAbsorption

variable {V : Type*} [DecidableEq V]

/-- `G` is an `r`-graph (an `r`-uniform hypergraph): every edge has exactly `r` vertices. -/
def IsRGraph (r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∀ e ∈ G, e.card = r

/-- The degree of a vertex set `S` in `G`: the number of edges of `G` containing `S`. -/
def deg (G : Finset (Finset V)) (S : Finset V) : ℕ :=
  (G.filter (fun e => S ⊆ e)).card

/-- `G` is `K_q^r`-divisible if for every `i ∈ {0, …, r-1}` and every `i`-set `S`,
`binom(q-i, r-i)` divides the number of edges of `G` containing `S`. -/
def IsDivisible (q r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∀ S : Finset V, S.card < r → (q - S.card).choose (r - S.card) ∣ deg G S

/-- The edges of the copy of `K_q^r` with vertex set `Q`: the `r`-subsets of `Q`. -/
def cliqueEdges (r : ℕ) (Q : Finset V) : Finset (Finset V) :=
  Q.powersetCard r

/-- The number of cliques of the family `𝒬` containing the (vertex set) `e`. -/
def cliqueMult (𝒬 : Finset (Finset V)) (e : Finset V) : ℕ :=
  (𝒬.filter (fun Q => e ⊆ Q)).card

/-- The set of edges covered by a family of cliques `𝒬`. -/
def coveredEdges (r : ℕ) (𝒬 : Finset (Finset V)) : Finset (Finset V) :=
  𝒬.biUnion (cliqueEdges r)

/-- `𝒬` is a `K_q^r`-decomposition of the `r`-graph `G`: a family of copies of `K_q^r`
such that every edge of `G` lies in exactly one clique of `𝒬` and no other `r`-set lies
in any clique of `𝒬`. -/
structure IsDecomposition (q r : ℕ) (G 𝒬 : Finset (Finset V)) : Prop where
  rgraph : IsRGraph r G
  card_eq : ∀ Q ∈ 𝒬, Q.card = q
  mult_eq : ∀ e : Finset V, e.card = r → cliqueMult 𝒬 e = if e ∈ G then 1 else 0

/-- `𝒬` is a `K_q^r`-packing of `G`: a family of pairwise edge-disjoint copies of `K_q^r`
all of whose edges belong to `G`. -/
structure IsPacking (q r : ℕ) (G 𝒬 : Finset (Finset V)) : Prop where
  card_eq : ∀ Q ∈ 𝒬, Q.card = q
  sub : ∀ Q ∈ 𝒬, cliqueEdges r Q ⊆ G
  mult_le : ∀ e : Finset V, e.card = r → cliqueMult 𝒬 e ≤ 1

/-- The (non-isolated) vertex set `V(G)` of a hypergraph `G`. -/
def vertexSet (G : Finset (Finset V)) : Finset V := G.sup id

/-- `G` admits a `K_q^r`-decomposition. -/
def HasDecomposition (q r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∃ 𝒬, IsDecomposition q r G 𝒬

/-- The complete `r`-graph `K_V^r` on the (finite) vertex type `V`. -/
def completeRGraph (V : Type*) [Fintype V] (r : ℕ) : Finset (Finset V) :=
  (Finset.univ : Finset V).powersetCard r
end RefinedAbsorption
namespace RefinedAbsorption
open Finset
def MaxDegLE {n : ℕ} (r : ℕ) (X : Finset (Finset (Fin n))) (D : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card + 1 = r → (deg X S : ℝ) ≤ D
def MinDegGE {n : ℕ} (r : ℕ) (J : Finset (Finset (Fin n))) (D : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card + 1 = r → D ≤ (deg J S : ℝ)
end RefinedAbsorption
namespace RefinedAbsorption
variable {V : Type*} [DecidableEq V] [Fintype V]
structure IsDesign (q r l : ℕ) (𝒟 : Finset (Finset V)) : Prop where
  card_eq : ∀ B ∈ 𝒟, B.card = q
  mult_eq : ∀ T : Finset V, T.card = r → cliqueMult 𝒟 T = l
abbrev IsSteinerSystem (q r : ℕ) (𝒮 : Finset (Finset V)) : Prop := IsDesign q r 1 𝒮
def DesignDivisibility (n q r l : ℕ) : Prop :=
  ∀ i < r, (q - i).choose (r - i) ∣ l * (n - i).choose (r - i)
end RefinedAbsorption
namespace RefinedAbsorption.Extensions
open Finset
variable {V : Type*} [DecidableEq V]
def IsPartialSteinerSystem (q r : ℕ) (P : Finset (Finset V)) : Prop :=
  (∀ Q ∈ P, Q.card = q) ∧ ∀ T : Finset V, T.card = r → cliqueMult P T ≤ 1
end RefinedAbsorption.Extensions
namespace RefinedAbsorption.Extensions
open Finset
theorem steiner_completion_avoiding {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ P F : Finset (Finset (Fin n)), IsPartialSteinerSystem q r P →
        MaxDegLE r (coveredEdges r P) (ε * n) → IsPartialSteinerSystem q r F →
        ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧ P ⊆ 𝒮 ∧ 𝒮 ∩ F = P ∩ F ∧
          ∀ B₁ ∈ F, Disjoint (cliqueEdges r B₁) (coveredEdges r P) →
            ∀ B₂ ∈ 𝒮 \ P, (B₁ ∩ B₂).card ≤ r := by sorry
theorem steiner_intersection_prescribed {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮₁ : Finset (Finset (Fin n)),
      IsSteinerSystem q r 𝒮₁ → ∀ P ⊆ 𝒮₁, MaxDegLE r (coveredEdges r P) (ε * n) →
        ∃ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₂ ∧ 𝒮₁ ∩ 𝒮₂ = P ∧
          ∀ B₁ ∈ 𝒮₁ \ P, ∀ B₂ ∈ 𝒮₂ \ P, (B₁ ∩ B₂).card ≤ r := by sorry
theorem partialSteiner_intersection_embedding {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {α : Type*}
    [Fintype α] [DecidableEq α] (P : Finset (Finset α)) (hP : IsPartialSteinerSystem q r P) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, DesignDivisibility N q r 1 →
      ∃ (f : α ↪ Fin N) (𝒮₁ 𝒮₂ : Finset (Finset (Fin N))),
        IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
          𝒮₁ ∩ 𝒮₂ = P.map (mapEmbedding f).toEmbedding := by sorry
theorem steiner_intersection_spectrum_poly {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ k : ℕ, (k : ℝ) ≤ c * (n : ℝ) ^ r →
        ∃ 𝒮₁ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
          (𝒮₁ ∩ 𝒮₂).card = k := by sorry
end RefinedAbsorption.Extensions
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
namespace RefinedAbsorption.Assembly
open Finset RefinedAbsorption.Extensions
open RefinedAbsorption.External RefinedAbsorption.External.NashWilliams
open RefinedAbsorption.External.PippengerSpencer
variable {q r : ℕ}
theorem steiner_quantitatively_almost_resolvable
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮 : Finset (Finset (Fin n)),
      IsSteinerSystem q r 𝒮 →
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by sorry
theorem exists_quantitatively_almost_resolvable_steiner
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by sorry
theorem nash_williams_scheduled_decomposition :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → IsTriangleDivisible G → 3 * Fintype.card V ≤ 4 * G.minDegree →
      ∃ T : Finset (Finset V), IsTriangleDecomposition G T ∧
        ∃ (m : ℕ) (c : Finset V → Fin m), IsProperEdgeColouring T m c ∧
          (G.maxDegree : ℝ) / 2 ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (G.maxDegree : ℝ) / 2 + ((G.maxDegree : ℝ) / 2) ^ (1 - γ) := by sorry
end RefinedAbsorption.Assembly
