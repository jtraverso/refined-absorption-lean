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
variable {V : Type*} [DecidableEq V]
structure IsAbsorber (q r : ℕ) (L A : Finset (Finset V)) : Prop where
  divisible : IsDivisible q r L
  independent : ∀ e ∈ A, ¬ e ⊆ vertexSet L
  decomp : HasDecomposition q r A
  decomp_union : HasDecomposition q r (A ∪ L)

/-- **Omni-absorber** (Definition 1.6).  An `r`-graph `A` is a `K_q^r`-omni-absorber for an
`r`-graph `X` with decomposition family `F` and decomposition function `QA` if `X` and `A`
are edge-disjoint and for every `K_q^r`-divisible subgraph `L` of `X`, `QA L ⊆ F` is a
`K_q^r`-decomposition of `A ∪ L`. -/
structure IsOmniAbsorber (q r : ℕ) (X A F : Finset (Finset V))
    (QA : Finset (Finset V) → Finset (Finset V)) : Prop where
  rgraph : IsRGraph r X
  disjoint : Disjoint X A
  subset_family : ∀ L ⊆ X, IsDivisible q r L → QA L ⊆ F
  decomp : ∀ L ⊆ X, IsDivisible q r L → IsDecomposition q r (A ∪ L) (QA L)

/-- **`C`-refined** (Definition 1.9).  An omni-absorber `A` for `X` with decomposition family
`F` is `C`-refined if every edge of `X ∪ A` lies in at most `C` elements of `F`. -/
def IsCRefined (C : ℕ) (X A F : Finset (Finset V)) : Prop :=
  ∀ e ∈ X ∪ A, cliqueMult F e ≤ C
end RefinedAbsorption
namespace RefinedAbsorption
open Finset
variable {U V : Type*} [DecidableEq U] [DecidableEq V]
def gmap (f : U ↪ V) (G : Finset (Finset U)) : Finset (Finset V) :=
  G.map (mapEmbedding f).toEmbedding
end RefinedAbsorption
namespace RefinedAbsorption.Original2024
noncomputable def budget (n r : ℕ) : ℝ := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n
def Theorem_6_1_for (q r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)),
    IsRGraph r G → MinDegGE r G ((1 - ε) * n) → IsDivisible q r G → HasDecomposition q r G
def Theorem_6_1 : Prop := ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_6_1_for q r
theorem theorem_6_1 : Theorem_6_1 := by sorry
end RefinedAbsorption.Original2024
namespace RefinedAbsorption.Faithful2024
open Finset
noncomputable abbrev budget (n r : ℕ) : ℝ := Original2024.budget n r
structure HGraph (α : Type*) where
  verts : Finset α
  edges : Finset (Finset α)

namespace HGraph

variable {α : Type*} [DecidableEq α]

/-- Every edge is a subset of the vertex set. -/
def WF (G : HGraph α) : Prop := ∀ e ∈ G.edges, e ⊆ G.verts

/-- `G` is an `r`-uniform hypergraph. -/
def IsUniform (r : ℕ) (G : HGraph α) : Prop := ∀ e ∈ G.edges, e.card = r ∧ e ⊆ G.verts

/-- `H ⊆ G`: `V(H) ⊆ V(G)` and `E(H) ⊆ E(G)`. -/
def IsSubgraph (H G : HGraph α) : Prop := H.verts ⊆ G.verts ∧ H.edges ⊆ G.edges

/-- `X` is a spanning subhypergraph of `G`: `V(X) = V(G)` and `E(X) ⊆ E(G)`. -/
def IsSpanningSubgraph (X G : HGraph α) : Prop := X.verts = G.verts ∧ X.edges ⊆ G.edges

/-- `Δ(G) = Δ_{r-1}(G)`: the maximum over the `(r-1)`-subsets `S` of `V(G)` of the number of
edges containing `S`. -/
def maxDeg (r : ℕ) (G : HGraph α) : ℕ := (G.verts.powersetCard (r - 1)).sup (deg G.edges)

/-- `δ(G) ≥ D`: every `(r-1)`-subset of `V(G)` lies in at least `D` edges. -/
def MinDegGE (r : ℕ) (G : HGraph α) (D : ℝ) : Prop :=
  ∀ S ⊆ G.verts, S.card + 1 = r → D ≤ (deg G.edges S : ℝ)

end HGraph

section Simple

variable {α : Type*} [DecidableEq α]

/-- `𝒟` is a set of pairwise edge-disjoint copies of `K_q^r` whose union is `G`. -/
def IsCliqueDecomposition (q r : ℕ) (G : Finset (Finset α)) (𝒟 : Finset (Finset α)) : Prop :=
  (∀ Q ∈ 𝒟, Q.card = q) ∧
  (∀ Q₁ ∈ 𝒟, ∀ Q₂ ∈ 𝒟, Q₁ ≠ Q₂ → Disjoint (cliqueEdges r Q₁) (cliqueEdges r Q₂)) ∧
  𝒟.biUnion (cliqueEdges r) = G

/-- **Definition 1.5 (omni-absorber).**  `A` is a `K_q^r`-omni-absorber for `X` with
decomposition family `𝓗` (copies of `K_q^r`, given by their `q`-sets) and decomposition function
`QA`: `V(X) = V(A)`, `X` and `A` are edge-disjoint, every member of `𝓗` is a subgraph of `X ∪ A`
isomorphic to `K_q^r` containing at most one edge of `X`, and for every `K_q^r`-divisible
subgraph `L` of `X`, `QA(L) ⊆ 𝓗` consists of pairwise edge-disjoint cliques with union `L ∪ A`. -/
structure IsOmniAbsorber (q r : ℕ) (X A : HGraph α) (𝓗 : Finset (Finset α))
    (QA : Finset (Finset α) → Finset (Finset α)) : Prop where
  wfX : X.WF
  wfA : A.WF
  verts_eq : X.verts = A.verts
  disjoint : Disjoint X.edges A.edges
  family : ∀ Q ∈ 𝓗, Q.card = q ∧ cliqueEdges r Q ⊆ X.edges ∪ A.edges
  oneX : ∀ Q ∈ 𝓗, ((cliqueEdges r Q).filter (· ∈ X.edges)).card ≤ 1
  sub : ∀ L ⊆ X.edges, IsDivisible q r L → QA L ⊆ 𝓗
  decomp : ∀ L ⊆ X.edges, IsDivisible q r L → IsCliqueDecomposition q r (L ∪ A.edges) (QA L)

/-- **Definition 1.6 (`C`-refined omni-absorber).**  `|𝓗(e)| ≤ C` for every edge `e ∈ X ∪ A`,
where `𝓗(e)` is the set of cliques of `𝓗` having `e` as an edge. -/
def IsCRefinedOmni (r C : ℕ) (X A : HGraph α) (𝓗 : Finset (Finset α)) : Prop :=
  ∀ e ∈ X.edges ∪ A.edges, (𝓗.filter fun Q => e ∈ cliqueEdges r Q).card ≤ C

/-- **Definition 1.8 (refiner).**  `R` is a `K_q^r`-refiner of the `r`-uniform `X` with
refinement family `𝓗` and refinement function `QR`: `R` is `r`-uniform, `V(X) = V(R)`, `X` and
`R` are edge-disjoint, `𝓗` is a family of `K_q^r`-divisible subgraphs of `X ∪ R` with
`|H ∩ X| ≤ 1`, and for every `K_q^r`-divisible subgraph `L` of `X`, `QR(L) ⊆ 𝓗` consists of
pairwise edge-disjoint members with union `L ∪ R`. -/
structure IsRefiner (q r : ℕ) (X R : HGraph α) (𝓗 : Finset (Finset (Finset α)))
    (QR : Finset (Finset α) → Finset (Finset (Finset α))) : Prop where
  unifX : X.IsUniform r
  unifR : R.IsUniform r
  verts_eq : X.verts = R.verts
  disjoint : Disjoint X.edges R.edges
  family : ∀ H ∈ 𝓗, H ⊆ X.edges ∪ R.edges ∧ IsDivisible q r H
  oneX : ∀ H ∈ 𝓗, (H.filter (· ∈ X.edges)).card ≤ 1
  sub : ∀ L ⊆ X.edges, IsDivisible q r L → QR L ⊆ 𝓗
  pairwise : ∀ L ⊆ X.edges, IsDivisible q r L →
    (QR L : Set (Finset (Finset α))).PairwiseDisjoint id
  cover : ∀ L ⊆ X.edges, IsDivisible q r L → (QR L).sup id = L ∪ R.edges

/-- **Definition 1.9 (`C`-refined family)** of subgraphs of `G`: `|𝓗(e)| ≤ C` for every edge
`e ∈ G` and `max{v(H), e(H)} ≤ C` for every `H ∈ 𝓗`. -/
structure IsCRefinedFamily (C : ℕ) (G : Finset (Finset α)) (𝓗 : Finset (Finset (Finset α))) :
    Prop where
  mult_le : ∀ e ∈ G, (𝓗.filter fun H => e ∈ H).card ≤ C
  verts_le : ∀ H ∈ 𝓗, (vertexSet H).card ≤ C
  card_le : ∀ H ∈ 𝓗, H.card ≤ C

/-- **Definition 1.10 (`C`-refined refiner).**  The refinement family of `R` (a family of
subgraphs of `X ∪ R`) is `C`-refined. -/
def IsCRefinedRefiner (C : ℕ) (X R : HGraph α) (𝓗 : Finset (Finset (Finset α))) : Prop :=
  IsCRefinedFamily C (X.edges ∪ R.edges) 𝓗

/-- **Definition 1.10 (refinement degree).**  `Δ(𝓗) = max { Δ_𝓗(S) : S ∈ binom(V(R), r-1) }`
with `Δ_𝓗(S) = |{H ∈ 𝓗 : S ⊆ V(H)}|`. -/
def refDegree (r : ℕ) (R : HGraph α) (𝓗 : Finset (Finset (Finset α))) : ℕ :=
  (R.verts.powersetCard (r - 1)).sup fun S => (𝓗.filter fun H => S ⊆ vertexSet H).card

end Simple

/-- **Theorem 1.7 (Refined Omni-Absorber Theorem)** of arXiv:2402.17855v1: for all integers
`q > r ≥ 1` there are an integer `C ≥ 1` and a real `ε ∈ (0,1)` such that: if `G` is an
`r`-uniform hypergraph on `n` vertices with `δ(G) ≥ (1-ε)n`, and `X` is a spanning
subhypergraph of `G` with `Δ(X) ≤ n/C`, then with `Δ := max{Δ(X), n^{1-1/r} log n}` there is a
`C`-refined `K_q^r`-omni-absorber `A ⊆ G` for `X` with `Δ(A) ≤ C · Δ`.  The vertex type is
arbitrary and `n = |V(G)|`. -/
def Theorem_1_7 : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ {α : Type} [DecidableEq α] (G X : HGraph α),
      G.IsUniform r → G.MinDegGE r ((1 - ε) * G.verts.card) →
      X.IsSpanningSubgraph G → (X.maxDeg r : ℝ) ≤ G.verts.card / C →
      ∃ (A : HGraph α) (𝓗 : Finset (Finset α)) (QA : Finset (Finset α) → Finset (Finset α)),
        IsOmniAbsorber q r X A 𝓗 QA ∧ IsCRefinedOmni r C X A 𝓗 ∧ A.IsSubgraph G ∧
        (A.maxDeg r : ℝ) ≤ C * max (X.maxDeg r : ℝ) (budget G.verts.card r)

/-- **Theorem 1.11 (Refiner Theorem)** of arXiv:2402.17855v1: for all integers `q > r ≥ 1` there
are an integer `C ≥ 1` and a real `ε ∈ (0,1)` such that: if `G` is an `r`-uniform hypergraph on
`n` vertices with `δ(G) ≥ (1-ε)n`, and `X` is a spanning subhypergraph of `G` with
`Δ(X) ≤ n/C`, then with `Δ := max{Δ(X), n^{1-1/r} log n}` there is a `C`-refined
`K_q^r`-refiner `R ⊆ G` of `X` with refinement family `𝓗` such that `Δ(𝓗) ≤ C · Δ` (the
refinement degree of the **family**). -/
def Theorem_1_11 : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ {α : Type} [DecidableEq α] (G X : HGraph α),
      G.IsUniform r → G.MinDegGE r ((1 - ε) * G.verts.card) →
      X.IsSpanningSubgraph G → (X.maxDeg r : ℝ) ≤ G.verts.card / C →
      ∃ (R : HGraph α) (𝓗 : Finset (Finset (Finset α)))
        (QR : Finset (Finset α) → Finset (Finset (Finset α))),
        IsRefiner q r X R 𝓗 QR ∧ IsCRefinedRefiner C X R 𝓗 ∧ R.IsSubgraph G ∧
        (refDegree r R 𝓗 : ℝ) ≤ C * max (X.maxDeg r : ℝ) (budget G.verts.card r)
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Degree of the vertex `v` in the multi-hypergraph `G` (number of copies containing `v`). -/
def vdeg (ends : E → Finset V) (G : Finset E) (v : V) : ℕ := (G.filter fun e => v ∈ ends e).card

/-- Codegree of the vertices `u, v` in `G` (number of copies containing both). -/
def codeg2 (ends : E → Finset V) (G : Finset E) (u v : V) : ℕ :=
  (G.filter fun e => u ∈ ends e ∧ v ∈ ends e).card

/-- A matching: pairwise vertex-disjoint copies. -/
def IsMatchingL (ends : E → Finset V) (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (ends e) (ends f)

/-- **Definition 2.6 (`A`-perfect matching).**  A matching of `G` is `A`-perfect if every vertex
of `A` is in an edge of the matching. -/
def IsAPerfectMatching (ends : E → Finset V) (G M : Finset E) (A : Finset V) : Prop :=
  M ⊆ G ∧ IsMatchingL ends M ∧ ∀ a ∈ A, ∃ e ∈ M, a ∈ ends e

/-- **Definition 2.7 (bipartite hypergraph).**  `G = (A, B)` with vertex set `VG` is bipartite with
parts `A` and `B` if `V(G) = A ∪ B` and every edge of `G` contains exactly one vertex from `A`. -/
def IsBipartiteHyp (ends : E → Finset V) (VG : Finset V) (G : Finset E) (A B : Finset V) : Prop :=
  VG = A ∪ B ∧ (∀ e ∈ G, ends e ⊆ VG) ∧ ∀ e ∈ G, (ends e ∩ A).card = 1

/-- **Theorem 2.8 of arXiv:2402.17855v1 (Nibble with Reserves)** (statement).  For each integer
`r ≥ 2` and real `β ∈ (0,1)` there exist an integer `D_β ≥ 0` and a real `α ∈ (0,1)` such that the
following holds for all `D ≥ D_β`.  Let `G` be an `r`-uniform (multi-)hypergraph with codegrees at
most `D^{1-β}` such that `G` is the edge-disjoint union of `G₁` and `G₂`, where `G₂ = (A, B)` is a
bipartite hypergraph (vertex set `V₂`) such that every vertex of `B` has degree at most `D` in
`G₂` and every vertex of `A` has degree at least `D^{1-α}` in `G₂`, and `G₁` is a hypergraph (vertex
set `V₁`) with `V(G₁) ∩ V(G₂) = A` such that every vertex of `G₁` has degree at most `D` in `G₁` and
every vertex of `A` has degree at least `D (1 - D^{-β})` in `G₁`.  Then there exists an
`A`-perfect matching of `G`. -/
def Theorem_2_8 : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → β < 1 → ∃ (Dβ : ℕ) (α : ℝ), 0 < α ∧ α < 1 ∧
    ∀ D : ℝ, (Dβ : ℝ) ≤ D →
    ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (ends : E → Finset V)
      (V₁ V₂ A B : Finset V) (G₁ G₂ : Finset E),
      (∀ e ∈ G₁ ∪ G₂, (ends e).card = r) →
      (∀ u v : V, u ≠ v → (codeg2 ends (G₁ ∪ G₂) u v : ℝ) ≤ D ^ (1 - β)) →
      Disjoint G₁ G₂ →
      IsBipartiteHyp ends V₂ G₂ A B →
      (∀ b ∈ B, (vdeg ends G₂ b : ℝ) ≤ D) →
      (∀ a ∈ A, D ^ (1 - α) ≤ (vdeg ends G₂ a : ℝ)) →
      (∀ e ∈ G₁, ends e ⊆ V₁) → V₁ ∩ V₂ = A →
      (∀ v ∈ V₁, (vdeg ends G₁ v : ℝ) ≤ D) →
      (∀ a ∈ A, D * (1 - D ^ (-β)) ≤ (vdeg ends G₁ a : ℝ)) →
      ∃ M : Finset E, IsAPerfectMatching ends (G₁ ∪ G₂) M A
def Theorem_6_2_ambient : Prop :=
∀ q r : ℕ, 1 ≤ r → r < q → ∀ (m : ℕ) (L : Finset (Finset (Fin m))), IsRGraph r L →
    IsDivisible q r L → ∃ (h : ℕ) (A Q₁ Q₂ : Finset (Finset (Fin m ⊕ Fin h))),
      IsAbsorber q r (RefinedAbsorption.gmap Function.Embedding.inl L) A ∧
      IsDecomposition q r A Q₁ ∧
      IsDecomposition q r (A ∪ RefinedAbsorption.gmap Function.Embedding.inl L) Q₂ ∧
      (∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ r) ∧
      ∀ t ∈ A, ¬ t ⊆ (univ : Finset (Fin m)).map Function.Embedding.inl
def Theorem_6_3 : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ (n₀ : ℕ) (ε : ℝ), 0 < ε ∧ ∀ n ≥ n₀,
    ∀ G : Finset (Finset (Fin n)), IsRGraph r G → IsDivisible q r G →
      MinDegGE r G ((1 - ε) * n) → ∀ Q₁ : Finset (Finset (Fin n)), IsPacking q r G Q₁ →
        ∃ Q₂ : Finset (Finset (Fin n)), IsDecomposition q r G Q₂ ∧
          ∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ r
theorem theorem_1_7 : Theorem_1_7 := by sorry
theorem theorem_1_11 : Theorem_1_11 := by sorry
theorem theorem_6_2_ambient : Theorem_6_2_ambient := by sorry
end RefinedAbsorption.Faithful2024
namespace RefinedAbsorption.Pending
theorem theorem_2_8 : RefinedAbsorption.Faithful2024.Theorem_2_8 := by sorry
theorem theorem_6_3 : RefinedAbsorption.Faithful2024.Theorem_6_3 := by sorry
end RefinedAbsorption.Pending
