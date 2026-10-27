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
/-- `Δ_{r-1}(X) ≤ D`: every `(r-1)`-set lies in at most `D` edges of `X`. -/
def MaxDegLE {n : ℕ} (r : ℕ) (X : Finset (Finset (Fin n))) (D : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card + 1 = r → (deg X S : ℝ) ≤ D
/-- `δ_{r-1}(J) ≥ D`: every `(r-1)`-set lies in at least `D` edges of `J`. -/
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
/-- The image of a hypergraph (or clique family) under an injective vertex map. -/
def gmap (f : U ↪ V) (G : Finset (Finset U)) : Finset (Finset V) :=
  G.map (mapEmbedding f).toEmbedding
end RefinedAbsorption
namespace RefinedAbsorption.Original2024
/-- The degree budget `n^{1-1/r} log n` of the article. -/
noncomputable def budget (n r : ℕ) : ℝ := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n
/-- **Theorem 6.1 (minimum degree version of the Existence Conjecture, `λ = 1`)** for fixed
`q, r`: there are `ε > 0` and `n₀` such that every `K_q^r`-divisible `r`-graph `G` on `n ≥ n₀`
vertices with `δ_{r-1}(G) ≥ (1-ε) n` has a `K_q^r`-decomposition. -/
def Theorem_6_1_for (q r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)),
    IsRGraph r G → MinDegGE r G ((1 - ε) * n) → IsDivisible q r G → HasDecomposition q r G
/-- **Theorem 6.1**, for all `q > r ≥ 1`. -/
def Theorem_6_1 : Prop := ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_6_1_for q r
/-- **Theorem 6.1** for all `q > r ≥ 1`. -/
theorem theorem_6_1 : Theorem_6_1 := by sorry
end RefinedAbsorption.Original2024
namespace RefinedAbsorption.Faithful2024
open Finset
/-- The degree budget `n^{1-1/r} log n` (same as `Original2024.budget`). -/
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
/-- The source article's Theorem 6.2, with independence of the whole old
ambient vertex set written explicitly in addition to the support-based
IsAbsorber contract. -/
def Theorem_6_2_ambient : Prop :=
∀ q r : ℕ, 1 ≤ r → r < q → ∀ (m : ℕ) (L : Finset (Finset (Fin m))), IsRGraph r L →
    IsDivisible q r L → ∃ (h : ℕ) (A Q₁ Q₂ : Finset (Finset (Fin m ⊕ Fin h))),
      IsAbsorber q r (RefinedAbsorption.gmap Function.Embedding.inl L) A ∧
      IsDecomposition q r A Q₁ ∧
      IsDecomposition q r (A ∪ RefinedAbsorption.gmap Function.Embedding.inl L) Q₂ ∧
      (∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ r) ∧
      ∀ t ∈ A, ¬ t ⊆ (univ : Finset (Fin m)).map Function.Embedding.inl
/-- **Theorem 6.3 of arXiv:2402.17855v1** (statement).  For `q > r ≥ 1` there are `n₀` and
`ε > 0` such that every `K_q^r`-divisible `r`-graph `G` on `v(G) = n ≥ n₀` vertices with
`δ(G) ≥ (1 - ε) n`, and every `K_q^r`-packing `Q₁` of `G`, admit a `K_q^r`-decomposition `Q₂` of `G`
with `|V(Q₁) ∩ V(Q₂)| ≤ r` for all `Q₁ ∈ Q₁`, `Q₂ ∈ Q₂`. -/
def Theorem_6_3 : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ (n₀ : ℕ) (ε : ℝ), 0 < ε ∧ ∀ n ≥ n₀,
    ∀ G : Finset (Finset (Fin n)), IsRGraph r G → IsDivisible q r G →
      MinDegGE r G ((1 - ε) * n) → ∀ Q₁ : Finset (Finset (Fin n)), IsPacking q r G Q₁ →
        ∃ Q₂ : Finset (Finset (Fin n)), IsDecomposition q r G Q₂ ∧
          ∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ r
/-- **Theorem 1.7 of arXiv:2402.17855v1 (Refined Omni-Absorber Theorem)**, faithful form. -/
theorem theorem_1_7 : Theorem_1_7 := by sorry
/-- **Theorem 1.11 of arXiv:2402.17855v1 (Refiner Theorem)**, faithful form: the bound is on the
refinement degree `Δ(𝓗)` of the family. -/
theorem theorem_1_11 : Theorem_1_11 := by sorry
/-- The same construction as Pending.theorem_6_2 exposes ambient independence. -/
theorem theorem_6_2_ambient : Theorem_6_2_ambient := by sorry
end RefinedAbsorption.Faithful2024
namespace RefinedAbsorption.Pending
/-- **Theorem 2.8 of arXiv:2402.17855v1 (Nibble with Reserves).** -/
theorem theorem_2_8 : RefinedAbsorption.Faithful2024.Theorem_2_8 := by sorry
/-- **Theorem 6.3 of arXiv:2402.17855v1** (proved). -/
theorem theorem_6_3 : RefinedAbsorption.Faithful2024.Theorem_6_3 := by sorry
end RefinedAbsorption.Pending
namespace RefinedAbsorption
variable {V : Type*} [DecidableEq V] [Fintype V]
/-- A design with parameters `(|V|, q, r, l)`: a set of `q`-subsets of `V` such that every
`r`-subset of `V` lies in exactly `l` of them. -/
structure IsDesign (q r l : ℕ) (𝒟 : Finset (Finset V)) : Prop where
  card_eq : ∀ B ∈ 𝒟, B.card = q
  mult_eq : ∀ T : Finset V, T.card = r → cliqueMult 𝒟 T = l
/-- A `(|V|, q, r)`-Steiner system: every `r`-subset lies in exactly one block. -/
abbrev IsSteinerSystem (q r : ℕ) (𝒮 : Finset (Finset V)) : Prop := IsDesign q r 1 𝒮
/-- The divisibility conditions for designs with parameters `(n, q, r, l)`:
`binom(q-i, r-i) ∣ l · binom(n-i, r-i)` for all `0 ≤ i ≤ r-1`. -/
def DesignDivisibility (n q r l : ℕ) : Prop :=
  ∀ i < r, (q - i).choose (r - i) ∣ l * (n - i).choose (r - i)
end RefinedAbsorption
namespace RefinedAbsorption
/-- **Theorem 1.10 (Refined efficient omni-absorber, Delcourt–Postle).**  For `q > r ≥ 1`
there is `C ≥ 1` such that: if `X ⊆ K_n^r` has `Δ_{r-1}(X) ≤ D ≤ n / C`, then there is a
`C`-refined `K_q^r`-omni-absorber `A` for `X` with
`Δ_{r-1}(A) ≤ C · max(D, n^{1-1/r} log n)`.  (Theorem 1.8 is the same statement without
refinedness.)  Not proved here; `RequestProject/OmniFromRefiner.lean` derives it from refined
refiners with attached absorbers (`refinedEfficientOmniAbsorber_of_refinerWithAbsorbers`). -/
def RefinedEfficientOmniAbsorber : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, ∀ X : Finset (Finset (Fin n)),
    ∀ D : ℝ, IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      ∃ A F : Finset (Finset (Fin n)), ∃ QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n)),
        IsOmniAbsorber q r X A F QA ∧ IsCRefined C X A F ∧
          MaxDegLE r A (C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n))
/-- **Conjecture 1.1 (Existence Conjecture)**, proved by Keevash (Theorem 1.2), and again by
Glock–Kühn–Lo–Osthus and by Delcourt–Postle via refined absorption.  For `q > r ≥ 2` and
`λ ≥ 1`, if `n` is large enough and `binom(q-i, r-i) ∣ λ binom(n-i, r-i)` for all
`0 ≤ i ≤ r-1`, then a design with parameters `(n, q, r, λ)` exists. -/
def ExistenceConjecture : Prop :=
  ∀ q r l : ℕ, 2 ≤ r → r < q → 1 ≤ l → ∃ n₀, ∀ n ≥ n₀, DesignDivisibility n q r l →
    ∃ 𝒟 : Finset (Finset (Fin n)), IsDesign q r l 𝒟
/-- **The Existence Conjecture (Conjecture 1.1, Keevash's theorem) for every `λ ≥ 1`**, with
simple designs, proved by refined absorption. -/
theorem existenceConjecture_proved : ExistenceConjecture := by sorry
/-- **The Existence Conjecture for Steiner systems** (`λ = 1`): for `q > r ≥ 2` and `n` large
enough satisfying the divisibility conditions, an `(n, q, r)`-Steiner system exists. -/
def SteinerExistenceConjecture : Prop :=
  ∀ q r : ℕ, 2 ≤ r → r < q → ∃ n₀, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
    ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮
end RefinedAbsorption
namespace RefinedAbsorption.Final
open RefinedAbsorption
/-- **Theorem 1.10 (Refined efficient omni-absorber, Delcourt–Postle).** -/
theorem theorem_1_10 : RefinedEfficientOmniAbsorber := by sorry
/-- **The Existence Conjecture for Steiner systems** (`λ = 1`), via the refined absorption proof
of Section 2 of the survey: Theorem 1.10 together with Corollary 2.4. -/
theorem existenceConjecture_steiner : SteinerExistenceConjecture := by sorry
end RefinedAbsorption.Final
namespace RefinedAbsorption

open Finset

variable {n : ℕ} {ι : Type*}

/-- The vertex set `V(H)` of a subgraph `H` (a set of edge copies) of the multigraph `ends`. -/
def subVerts [DecidableEq ι] (ends : ι → Finset (Fin n)) (H : Finset ι) : Finset (Fin n) :=
  H.biUnion ends

/-- The image of an edge of a supergraph under the embedding `f` of its new vertices. -/
def embedEdge {m : ℕ} (f : Fin m → Fin n) (e : Finset (Fin n ⊕ Fin m)) : Finset (Fin n) :=
  e.image (Sum.elim id f)

/-- **Definition 3.6 (supergraph system)**, for `W = (W_H : H ∈ ℋ)`: every `W_H` is an `r`-graph
containing `H`, and its old vertices lie in `V(H)`. -/
structure IsSupergraphSystem [DecidableEq ι] (r : ℕ) (ends : ι → Finset (Fin n))
    (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) : Prop where
  uniform : ∀ H ∈ ℋ, ∀ e ∈ W H, e.card = r
  super : ∀ H ∈ ℋ, ∀ x ∈ H, (ends x).map Function.Embedding.inl ∈ W H
  roots : ∀ H ∈ ℋ, ∀ e ∈ W H, e.toLeft ⊆ subVerts ends H

/-- `W` is edge-intersecting: for every edge `e` of `W_H` there is an edge `f` of `H` with
`e ∩ V(J) ⊆ f` (Remark 3.3 and Definition 3.6). -/
def IsEdgeIntersecting (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) : Prop :=
  ∀ H ∈ ℋ, ∀ e ∈ W H, ∃ x ∈ H, e.toLeft ⊆ ends x

/-- `W` is `C`-bounded: `e(W_H) ≤ C` and `v(W_H) = |V(H)| + m_H ≤ C` for all `H ∈ ℋ`. -/
def IsCBounded [DecidableEq ι] (C : ℕ) (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι))
    (m : Finset ι → ℕ) (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) : Prop :=
  ∀ H ∈ ℋ, (W H).card ≤ C ∧ (subVerts ends H).card + m H ≤ C

/-- `ℋ` is a `C`-refined family of subgraphs of `J`: every edge copy of `J` lies in at most `C`
members of `ℋ`. -/
def IsCRefinedFamily [DecidableEq ι] (C : ℕ) (ℋ : Finset (Finset ι)) : Prop :=
  ∀ x : ι, (ℋ.filter (fun H => x ∈ H)).card ≤ C

/-- **Definition 3.7**: `f` embeds `W_H` into `G ∖ (E(J) ∖ E(H))`.  The map `Sum.elim id f` is
injective on `V(W_H)` (i.e. `f` is injective and avoids `V(H)`), every edge of `W_H` is mapped to
an edge of `G`, and every edge containing a new vertex is mapped outside `E(J)`.  (Such an image
contains a vertex outside `V(H)`, so it can never be an edge of `H`; hence this is the same as
avoiding `E(J) ∖ E(H)`.) -/
def IsHostEmbedding [DecidableEq ι] (G : Finset (Finset (Fin n))) (ends : ι → Finset (Fin n))
    (H : Finset ι) {m : ℕ} (WH : Finset (Finset (Fin n ⊕ Fin m))) (f : Fin m → Fin n) : Prop :=
  Function.Injective f ∧ (∀ i, f i ∉ subVerts ends H) ∧
    ∀ e ∈ WH, embedEdge f e ∈ G ∧ (e.toRight.Nonempty → ∀ y, embedEdge f e ≠ ends y)

/-- The image `φ(W)` of the whole supergraph system. -/
def systemImage [DecidableEq ι] (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (φ : (H : Finset ι) → Fin (m H) → Fin n) : Finset (Finset (Fin n)) :=
  ℋ.biUnion (fun H => (W H).image (embedEdge (φ H)))
end RefinedAbsorption
namespace RefinedAbsorption.FaithfulSurvey2025
open Finset RefinedAbsorption
variable {n : ℕ} {ι : Type*} [DecidableEq ι]
def sysMap (m : Finset ι → ℕ) (Ψ : (H : Finset ι) → Fin (m H) → Fin n) :
    Fin n ⊕ (Σ H : Finset ι, Fin (m H)) → Fin n :=
  Sum.elim id fun p => Ψ p.1 p.2

/-- The vertex set `V(⋃𝒲)` of the union of the supergraphs: the old vertices `⋃_{H ∈ ℋ} V(H)`
(which contain every old vertex of every `W_H`, by `IsSupergraphSystem.roots`) and the new
vertices `(H, i)` of the supergraphs `W_H`, `H ∈ ℋ`. -/
def sysVerts (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ) :
    Set (Fin n ⊕ (Σ H : Finset ι, Fin (m H))) :=
  {x | (∃ a, x = Sum.inl a ∧ ∃ H ∈ ℋ, a ∈ subVerts ends H) ∨ (∃ p, x = Sum.inr p ∧ p.1 ∈ ℋ)}

/-- **Definition 3.7 of the survey, literally**: an embedding of the supergraph system `𝒲` into `G`
is a map `φ : V(⋃𝒲) ↪ V(G)` (injective on all of `V(⋃𝒲)`) fixing `V(J)` and preserving edges. -/
def IsGlobalEmbedding (G : Finset (Finset (Fin n))) (ends : ι → Finset (Fin n))
    (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (Ψ : (H : Finset ι) → Fin (m H) → Fin n) : Prop :=
  Set.InjOn (sysMap m Ψ) (sysVerts ends ℋ m) ∧ ∀ H ∈ ℋ, ∀ e ∈ W H, embedEdge (Ψ H) e ∈ G

/-- Per-piece embeddings into `G ∖ (E(J) ∖ E(H))` (the notion of the project, Definition 3.7 for
the single supergraph `W_H`). -/
def IsPiecewiseHostEmbedding (G : Finset (Finset (Fin n))) (ends : ι → Finset (Fin n))
    (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (φ : (H : Finset ι) → Fin (m H) → Fin n) : Prop :=
  ∀ H ∈ ℋ, IsHostEmbedding G ends H (W H) (φ H)

/-- The new edges of different supergraphs have distinct images. -/
def NewEdgesDistinct (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (φ : (H : Finset ι) → Fin (m H) → Fin n) : Prop :=
  ∀ H₁ ∈ ℋ, ∀ H₂ ∈ ℋ, H₁ ≠ H₂ → ∀ e₁ ∈ W H₁, ∀ e₂ ∈ W H₂,
    e₁.toRight.Nonempty → e₂.toRight.Nonempty → embedEdge (φ H₁) e₁ ≠ embedEdge (φ H₂) e₂
open Classical in
/-- `Δ_{r-1}(J)` of the multi-`r`-graph `J` (all copies of the finite label type, counted with
multiplicity). -/
noncomputable def jMaxDeg (r : ℕ) {ι : Type*} [Fintype ι] (ends : ι → Finset (Fin n)) : ℕ :=
  ((univ : Finset (Finset (Fin n))).filter fun S => S.card + 1 = r).sup fun S =>
    (univ.filter fun x => S ⊆ ends x).card
open Classical in
/-- **Lemma 3.8 of the survey, read literally** (with Definition 3.7 as printed: one map
`φ : V(⋃𝒲) ↪ V(G)` fixing `V(J)`): `∀ C > r ≥ 1, γ ∈ (0,1] ∃ C' ≥ 1`: for `G ⊆ K_n^r`, a
multi-`r`-graph `J` with `Simple(J) ⊆ G` and `Δ(J) ≤ n/C'`, a `C`-refined family `ℋ` of subgraphs of
`J` and a `C`-bounded edge-intersecting supergraph system `𝒲` for `ℋ` such that every `W_H` has at
least `γ n^{|V(W_H) ∖ V(H)|}` embeddings into `G ∖ (E(J) ∖ E(H))`, there is an embedding `φ` of `𝒲`
into `G` with `Δ_{r-1}(φ(𝒲)) ≤ C' Δ_{r-1}(J)`.  **This statement is false**
(`not_generalEmbeddingLemmaLiteral`). -/
def GeneralEmbeddingLemmaLiteral : Prop :=
  ∀ (C r : ℕ), 1 ≤ r → r < C → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n : ℕ) (G : Finset (Finset (Fin n))) (ι : Type) [Fintype ι] [DecidableEq ι]
      (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
      (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))),
      1 ≤ n → IsRGraph r G → (∀ x, (ends x).card = r) → (∀ x, ends x ∈ G) →
      (jMaxDeg r ends : ℝ) ≤ n / C' →
      IsCRefinedFamily C ℋ → IsSupergraphSystem r ends ℋ m W → IsEdgeIntersecting ends ℋ m W →
      IsCBounded C ends ℋ m W →
      (∀ H ∈ ℋ, γ * (n : ℝ) ^ (m H) ≤
        ((univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)).card : ℝ)) →
      ∃ Ψ : (H : Finset ι) → Fin (m H) → Fin n,
        IsGlobalEmbedding G ends ℋ m W Ψ ∧
        ∀ S : Finset (Fin n), S.card + 1 = r →
          (((systemImage ℋ m W Ψ).filter (fun f => S ⊆ f)).card : ℝ) ≤ C' * jMaxDeg r ends
open Classical in
/-- **Lemma 3.8 of the survey, per-piece variant** (the notion of the project, restated with the
names of this file): the conclusion asks for per-piece embeddings (each `φ H` injective, avoiding
`V(H)` and `E(J) ∖ E(H)`) with distinct images of the new edges of different supergraphs, instead
of the global injectivity of the printed Definition 3.7. -/
def GeneralEmbeddingLemmaPiecewise : Prop :=
  ∀ (C r : ℕ), 1 ≤ r → r < C → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n : ℕ) (G : Finset (Finset (Fin n))) (ι : Type) [Fintype ι] [DecidableEq ι]
      (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
      (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) (D : ℝ),
      1 ≤ n → IsRGraph r G → (∀ x, (ends x).card = r) → (∀ x, ends x ∈ G) →
      (∀ S : Finset (Fin n), S.card + 1 = r →
        ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D) →
      D ≤ n / C' →
      IsCRefinedFamily C ℋ → IsSupergraphSystem r ends ℋ m W → IsEdgeIntersecting ends ℋ m W →
      IsCBounded C ends ℋ m W →
      (∀ H ∈ ℋ, γ * (n : ℝ) ^ (m H) ≤
        ((univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)).card : ℝ)) →
      ∃ φ : (H : Finset ι) → Fin (m H) → Fin n,
        IsPiecewiseHostEmbedding G ends ℋ m W φ ∧ NewEdgesDistinct ℋ m W φ ∧
        ∀ S : Finset (Fin n), S.card + 1 = r →
          (((systemImage ℋ m W φ).filter (fun f => S ⊆ f)).card : ℝ) ≤ C' * D
/-- **The literal reading of Lemma 3.8 of the survey is false.**  Take `C = 3`, `r = 2`,
`γ = 1/2`.  For any `C'`, let `k = ⌈C'⌉ + 2`, `n = 2k`, `G = K_n^2`, `J` the perfect matching,
`ℋ` the single edges of `J` and `W_H` the triangle on `H` with one new vertex.  All hypotheses
hold (`Δ(J) = 1 ≤ n/C'`, each `W_H` has `n - 2 ≥ n/2` embeddings into `G ∖ (E(J) ∖ E(H))`), but an
injective map on `V(⋃𝒲) ⊇ V(J) = Fin n` fixing `V(J)` has no room for any new vertex. -/
theorem not_generalEmbeddingLemmaLiteral : ¬ GeneralEmbeddingLemmaLiteral := by sorry
/-- **Lemma 3.8 of the survey, per-piece variant: proved** (adapter from the existing
`RefinedAbsorption.generalEmbeddingLemma`). -/
theorem generalEmbedding_piecewise : GeneralEmbeddingLemmaPiecewise := by sorry
end RefinedAbsorption.FaithfulSurvey2025
namespace RefinedAbsorption.Extensions
open Finset
variable {V : Type*} [DecidableEq V]
/-- A **partial Steiner system** with parameters `(q, r)`: a family of `q`-sets such that every
`r`-set lies in at most one of them. -/
def IsPartialSteinerSystem (q r : ℕ) (P : Finset (Finset V)) : Prop :=
  (∀ Q ∈ P, Q.card = q) ∧ ∀ T : Finset V, T.card = r → cliqueMult P T ≤ 1
end RefinedAbsorption.Extensions
namespace RefinedAbsorption.Extensions
open Finset
/-- **Completion avoiding a partial Steiner system.** -/
theorem steiner_completion_avoiding {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ P F : Finset (Finset (Fin n)), IsPartialSteinerSystem q r P →
        MaxDegLE r (coveredEdges r P) (ε * n) → IsPartialSteinerSystem q r F →
        ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧ P ⊆ 𝒮 ∧ 𝒮 ∩ F = P ∩ F ∧
          ∀ B₁ ∈ F, Disjoint (cliqueEdges r B₁) (coveredEdges r P) →
            ∀ B₂ ∈ 𝒮 \ P, (B₁ ∩ B₂).card ≤ r := by sorry
/-- **Prescribed intersection with a given Steiner system.**  For `q > r ≥ 1` there are `ε > 0`
and `n₀` such that for every `n ≥ n₀`, every `(n, q, r)`-Steiner system `𝒮₁` and every subfamily
`P ⊆ 𝒮₁` whose covered `r`-graph has maximum `(r-1)`-degree at most `ε n`, there is a Steiner
system `𝒮₂` whose blocks in common with `𝒮₁` are exactly those of `P`; moreover a block of
`𝒮₁ \ P` and a block of `𝒮₂ \ P` always share at most `r` points. -/
theorem steiner_intersection_prescribed {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮₁ : Finset (Finset (Fin n)),
      IsSteinerSystem q r 𝒮₁ → ∀ P ⊆ 𝒮₁, MaxDegLE r (coveredEdges r P) (ε * n) →
        ∃ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₂ ∧ 𝒮₁ ∩ 𝒮₂ = P ∧
          ∀ B₁ ∈ 𝒮₁ \ P, ∀ B₂ ∈ 𝒮₂ \ P, (B₁ ∩ B₂).card ≤ r := by sorry
/-- **Every finite partial Steiner system is the exact intersection of two Steiner systems.**
Let `q > r ≥ 1` and let `P` be a partial Steiner system on a finite set `α`.  For every
sufficiently large admissible `N` there are an injection `f : α ↪ Fin N` and two
`(N, q, r)`-Steiner systems whose common blocks are exactly the images of the blocks of `P`. -/
theorem partialSteiner_intersection_embedding {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {α : Type*}
    [Fintype α] [DecidableEq α] (P : Finset (Finset α)) (hP : IsPartialSteinerSystem q r P) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, DesignDivisibility N q r 1 →
      ∃ (f : α ↪ Fin N) (𝒮₁ 𝒮₂ : Finset (Finset (Fin N))),
        IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
          𝒮₁ ∩ 𝒮₂ = P.map (mapEmbedding f).toEmbedding := by sorry
/-- **Polynomial form of the intersection spectrum.**  For `q > r ≥ 1` there are `c > 0` and `n₀`
such that for every admissible `n ≥ n₀` and every `k ≤ c n^r` there are two
`(n, q, r)`-Steiner systems with exactly `k` blocks in common.  (Every Steiner system has
`binom(n,r)/binom(q,r) = Θ(n^r)` blocks, so this is the right order of magnitude.) -/
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
/-- Every sufficiently large Steiner system has a block colouring with
`R ≤ m ≤ R + R^(1-γ)`, where `R` is its point degree and `0 < γ < 1`.
Blocks of one colour form a partial parallel class. The external colouring
contract is discharged by `pippengerSpencerPolynomial`. -/
theorem steiner_quantitatively_almost_resolvable
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮 : Finset (Finset (Fin n)),
      IsSteinerSystem q r 𝒮 →
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by sorry
/-- Such a coloured Steiner system exists at every sufficiently large
admissible order. The design existence theorem and the external colouring
theorem are both proved inputs in the assembled library. -/
theorem exists_quantitatively_almost_resolvable_steiner
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by sorry
/-- A sufficiently large triangle-divisible graph at the exact Nash–Williams
threshold admits a triangle decomposition scheduled in at most
`Δ(G)/2 + (Δ(G)/2)^(1-γ)` rounds. Triangles in each round are vertex-disjoint;
the rounds need not be spanning triangle factors. Both external contracts
are discharged by their pinned proofs. -/
theorem nash_williams_scheduled_decomposition :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → IsTriangleDivisible G → 3 * Fintype.card V ≤ 4 * G.minDegree →
      ∃ T : Finset (Finset V), IsTriangleDecomposition G T ∧
        ∃ (m : ℕ) (c : Finset V → Fin m), IsProperEdgeColouring T m c ∧
          (G.maxDegree : ℝ) / 2 ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (G.maxDegree : ℝ) / 2 + ((G.maxDegree : ℝ) / 2) ^ (1 - γ) := by sorry
end RefinedAbsorption.Assembly
