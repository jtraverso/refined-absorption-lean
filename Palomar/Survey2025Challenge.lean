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
