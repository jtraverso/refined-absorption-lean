module
public import RequestProject.Original2024.Flat

/-!
# Faithful statements of the original article (Delcourt–Postle, arXiv:2402.17855v1)

M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*,
arXiv:2402.17855v1 (27 Feb 2024).  **All numbers in this namespace are those of the 2024
article**, not of the survey.

This file is a strictly additive layer: nothing in `RefinedAbsorption.Original2024`,
`RefinedAbsorption` (survey interface) or elsewhere is changed.  The definitions here transcribe the
definitions of the article *with all the conditions of the article inside the contract*:

* hypergraphs carry their own vertex set (`HGraph`), so `V(X) = V(A)` is an equality of vertex sets
  (isolated vertices allowed), not of non-isolated supports;
* the omni-absorber contract (Definition 1.5) contains `|H ∩ X| ≤ 1` for every clique `H` of the
  decomposition family; the refiner contract (Definition 1.8) contains `|H ∩ X| ≤ 1` for every
  member of the refinement family;
* `C`-refined families (Definition 1.9) bound `|H(e)|`, `v(H)` and `e(H)`;
* the refinement degree `Δ(H)` (Definition 1.10) is a separate quantity (`refDegree`).

For the multigraph theorems (Theorems 3.7 and 3.8) a multi-hypergraph is given by labelled copies:
a type `E` of edge labels and `ends : E → Finset (Fin n)`.  The multiplicity of an `r`-set is the
number of labels with that vertex set (`MultiRefiner.mult`); no injectivity is required, so this is
an arbitrary multi-hypergraph.  The vertex set of `X` is `Fin n` (every vertex counts, so
`v(X) = n`, isolated vertices included).  The output multi-hypergraph `A` or `R` lives on a label
type `E'` together with an injective relabelling `g : E → E'` with `ends' (g c) = ends c`; thus
`X.image g` is `X` itself with the same multiplicities.

## Contents

* `multBound q r` = `M(q,r)` (Definition 3.5).
* `mmaxDeg`, `mrefDeg`: `Δ_{r-1}` of a labelled multigraph and the refinement degree of a family.
* `IsCliqueCopy`, `IsMultiOmniAbsorberF`, `IsCRefinedMultiOmni` (Definitions 1.5, 1.6, 3.1).
* `IsMultiRefinerF`, `IsCRefinedMultiFamily` (Definitions 1.8, 1.9, 1.10, 3.2).
* `Theorem_3_7_for`, `Theorem_3_8_conclusion`, `Theorem_3_8_for` (Theorems 3.7 and 3.8, with the
  multigraph input of multiplicity at most `M(q,r)`, `v(X) ≥ C`, a *prescribed* `Y` with
  `|Y| ≥ v(X)/3`, and flatness exactly as in Definition 3.6: `|e \ Y| ≤ r - 1` for every edge `e`
  of `A` (resp. `R`)).
* `HGraph`, `IsOmniAbsorber`, `IsCRefinedOmni`, `IsRefiner`, `IsCRefinedFamily`, `refDegree`,
  `Theorem_1_7`, `Theorem_1_11` (simple hypergraphs with vertex sets; host `G` on `n` vertices).
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner

/-- **Definition 3.5.**  `M(q,r) = lcm { binom(q-i, r-i) : i ∈ {0, …, r-1} }`. -/
def multBound (q r : ℕ) : ℕ := (range r).lcm fun i => (q - i).choose (r - i)

/-! ## Multi-hypergraphs given by labelled copies -/

section Multi

variable {α E : Type*} [DecidableEq α] [DecidableEq E]

/-- `Δ_{r-1}(X)` of a labelled multi-hypergraph on the finite vertex type `α`: the maximum over all
`(r-1)`-sets `S` of the number of copies containing `S` (counted with multiplicity). -/
def mmaxDeg [Fintype α] (r : ℕ) (ends : E → Finset α) (X : Finset E) : ℕ :=
  ((univ : Finset (Finset α)).filter fun S => S.card + 1 = r).sup (mdeg ends X)

/-- Refinement degree `Δ_𝒲(S)` of an `(r-1)`-set `S`: the number of members `W` of the family
with `S ⊆ V(W)` (Definition 1.10, Definition 3.10). -/
def mrefDegAt (ends : E → Finset α) (𝒲 : Finset (Finset E)) (S : Finset α) : ℕ :=
  (𝒲.filter fun W => S ⊆ W.biUnion ends).card

/-- Refinement degree `Δ(𝒲)` of a family: the maximum of `Δ_𝒲(S)` over all `(r-1)`-sets `S` of
the (ambient) vertex set. -/
def mrefDeg [Fintype α] (r : ℕ) (ends : E → Finset α) (𝒲 : Finset (Finset E)) : ℕ :=
  ((univ : Finset (Finset α)).filter fun S => S.card + 1 = r).sup (mrefDegAt ends 𝒲)

/-- A sub-multigraph `W` is a copy of `K_q^r`: its copies are pairwise distinct and their vertex
sets are exactly the `r`-subsets of a `q`-set `Q`. -/
def IsCliqueCopy (q r : ℕ) (ends : E → Finset α) (W : Finset E) : Prop :=
  ∃ Q : Finset α, Q.card = q ∧ Set.InjOn ends W ∧ W.image ends = Q.powersetCard r

/-- **Definitions 1.5 and 3.1 (multi-omni-absorber).**  `A` is a `K_q^r`-multi-omni-absorber for
`X` with decomposition family `𝒬`: `V(X) = V(A) = U` (all copies lie in `U`), `X ∪ A` is an
`r`-uniform multi-hypergraph, `X` and `A` are edge-disjoint (no common copy), `𝒬` is a family of
sub-multigraphs of `X ∪ A` each isomorphic to `K_q^r` with `|H ∩ X| ≤ 1`, and for every
`K_q^r`-divisible `L ⊆ X` some pairwise edge-disjoint `Q_A(L) ⊆ 𝒬` has union `L ∪ A`. -/
structure IsMultiOmniAbsorberF (q r : ℕ) (U : Finset α) (ends : E → Finset α)
    (X A : Finset E) (𝒬 : Finset (Finset E)) : Prop where
  ambient : ∀ c ∈ X ∪ A, ends c ⊆ U
  rgraph : ∀ c ∈ X ∪ A, (ends c).card = r
  disjoint : Disjoint X A
  family_sub : ∀ W ∈ 𝒬, W ⊆ X ∪ A
  family_clique : ∀ W ∈ 𝒬, IsCliqueCopy q r ends W
  oneX : ∀ W ∈ 𝒬, (W ∩ X).card ≤ 1
  decomp : ∀ L ⊆ X, MIsDivisible q r ends L →
    ∃ 𝒟 ⊆ 𝒬, (𝒟 : Set (Finset E)).PairwiseDisjoint id ∧ 𝒟.sup id = L ∪ A

/-- **Definition 1.6 (`C`-refined).**  Every edge (copy) of `X ∪ A` lies in at most `C` members
of the decomposition family. -/
def IsCRefinedMultiOmni (C : ℕ) (X A : Finset E) (𝒬 : Finset (Finset E)) : Prop :=
  ∀ c ∈ X ∪ A, (𝒬.filter fun W => c ∈ W).card ≤ C

/-- **Definitions 1.8 and 3.2 (multi-refiner).**  `R` is a `K_q^r`-multi-refiner of `X` with
refinement family `𝒲`: `V(X) = V(R) = U`, `X ∪ R` is an `r`-uniform multi-hypergraph, `X` and `R`
are edge-disjoint, `𝒲` is a family of `K_q^r`-divisible sub-multigraphs of `X ∪ R` with
`|H ∩ X| ≤ 1`, and for every `K_q^r`-divisible `L ⊆ X` some pairwise edge-disjoint
`Q_R(L) ⊆ 𝒲` has union `L ∪ R`. -/
structure IsMultiRefinerF (q r : ℕ) (U : Finset α) (ends : E → Finset α)
    (X R : Finset E) (𝒲 : Finset (Finset E)) : Prop where
  ambient : ∀ c ∈ X ∪ R, ends c ⊆ U
  rgraph : ∀ c ∈ X ∪ R, (ends c).card = r
  disjoint : Disjoint X R
  family_sub : ∀ W ∈ 𝒲, W ⊆ X ∪ R
  family_div : ∀ W ∈ 𝒲, MIsDivisible q r ends W
  oneX : ∀ W ∈ 𝒲, (W ∩ X).card ≤ 1
  decomp : ∀ L ⊆ X, MIsDivisible q r ends L →
    ∃ 𝒟 ⊆ 𝒲, (𝒟 : Set (Finset E)).PairwiseDisjoint id ∧ 𝒟.sup id = L ∪ R

/-- **Definition 1.9 (`C`-refined family)**, for a family `𝒲` of sub-multigraphs of `G`:
`|𝒲(e)| ≤ C` for every edge `e ∈ G`, and `max{v(H), e(H)} ≤ C` for every `H ∈ 𝒲`
(`v(H)` is the number of vertices spanned by the copies of `H`). -/
structure IsCRefinedMultiFamily (C : ℕ) (ends : E → Finset α) (G : Finset E)
    (𝒲 : Finset (Finset E)) : Prop where
  mult_le : ∀ c ∈ G, (𝒲.filter fun W => c ∈ W).card ≤ C
  verts_le : ∀ W ∈ 𝒲, (W.biUnion ends).card ≤ C
  card_le : ∀ W ∈ 𝒲, W.card ≤ C

end Multi

/-- The degree budget `n^{1-1/r} log n` (same as `Original2024.budget`). -/
noncomputable abbrev budget (n r : ℕ) : ℝ := Original2024.budget n r

/-- `Δ = max{Δ(X), v(X)^{1-1/r} log v(X)}` for a labelled multigraph on `Fin n`. -/
noncomputable def bigDelta (r : ℕ) {n : ℕ} {E : Type*} [DecidableEq E] (ends : E → Finset (Fin n))
    (X : Finset E) : ℝ :=
  max (mmaxDeg r ends X : ℝ) (budget n r)

/-- **Theorem 3.7 (Refined Multi-Omni-Absorber Theorem)** of arXiv:2402.17855v1, for fixed
`q, r`: there is an integer `C ≥ 1` such that for every `r`-uniform multi-hypergraph `X` on
`v(X) = n ≥ C` vertices of multiplicity at most `M(q,r)`, with
`Δ := max{Δ(X), v(X)^{1-1/r} log v(X)}`, and every `Y ⊆ V(X)` with `|Y| ≥ v(X)/3`, there is a
`C`-refined `K_q^r`-multi-omni-absorber `A` for `X` with `Δ(A) ≤ C·Δ` and `A` `(r-1)`-flat to `Y`
(`|e \ Y| ≤ r - 1` for every edge `e` of `A`). -/
def Theorem_3_7_for (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (X : Finset E), MIsRGraph r ends X → (∀ e, mult ends X e ≤ multBound q r) → C ≤ n →
    ∀ Y : Finset (Fin n), (n : ℝ) / 3 ≤ Y.card →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (A : Finset E') (𝒬 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧
      IsMultiOmniAbsorberF q r (univ : Finset (Fin n)) ends' (X.image g) A 𝒬 ∧
      IsCRefinedMultiOmni C (X.image g) A 𝒬 ∧
      (mmaxDeg r ends' A : ℝ) ≤ C * bigDelta r ends X ∧
      Original2024.IsFlatTo (r - 1) Y ends' A

/-- **Theorem 3.7**, for all `q > r ≥ 1`. -/
def Theorem_3_7 : Prop := ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_3_7_for q r

/-- The conclusion of **Theorem 3.8 (Multi-Refiner Theorem)** of arXiv:2402.17855v1, for fixed
`q, r`: there is an integer `C ≥ 1` such that for every `r`-uniform multi-hypergraph `X` on
`v(X) = n ≥ C` vertices of multiplicity at most `M(q,r)` and every `Y ⊆ V(X)` with
`|Y| ≥ v(X)/3`, there is a `C`-refined `K_q^r`-multi-refiner `R` of `X` with refinement family
`𝒲` such that `Δ(𝒲) ≤ C · max{Δ(X), v(X)^{1-1/r} log v(X)}` and `R` is `(r-1)`-flat to `Y`.
There is **no** hypothesis `Δ(X) ≤ v(X)/C`. -/
def Theorem_3_8_conclusion (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (X : Finset E), MIsRGraph r ends X → (∀ e, mult ends X e ≤ multBound q r) → C ≤ n →
    ∀ Y : Finset (Fin n), (n : ℝ) / 3 ≤ Y.card →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R : Finset E') (𝒲 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧
      IsMultiRefinerF q r (univ : Finset (Fin n)) ends' (X.image g) R 𝒲 ∧
      IsCRefinedMultiFamily C ends' (X.image g ∪ R) 𝒲 ∧
      (mrefDeg r ends' 𝒲 : ℝ) ≤ C * bigDelta r ends X ∧
      Original2024.IsFlatTo (r - 1) Y ends' R

/-- **Theorem 3.8** of arXiv:2402.17855v1 in the inductive form of the article: *suppose
Theorem 3.7 holds for all `r' ∈ [r-1]`*; then the conclusion of Theorem 3.8 holds for `q, r`.
The hypothesis is Theorem 3.7 (not Theorem 1.11) in every lower uniformity `r'` (for every
`q' > r'`, which covers the link parameters `(q-i, r-i)` used in §4). -/
def Theorem_3_8_for (q r : ℕ) : Prop :=
  (∀ q' r' : ℕ, 1 ≤ r' → r' < r → r' < q' → Theorem_3_7_for q' r') → Theorem_3_8_conclusion q r

/-! ## Simple hypergraphs with vertex sets (Section 1) -/

/-- A hypergraph with an explicit vertex set (isolated vertices allowed). -/
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

end RefinedAbsorption.Faithful2024
