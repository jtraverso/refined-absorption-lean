module
public import RefinedAbsorption.Final

/-!
# Interface for the original article (Delcourt–Postle 2024)

M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*,
arXiv:2402.17855v1.

This file states, as Lean definitions and `Prop`s, the notions and theorems of the **original
article** that this project targets.  They are kept apart from the survey interface
(`RequestProject/Statements.lean`, `RequestProject/Final.lean`, survey arXiv:2510.19978): the
theorem numbers below are those of the 2024 article, not of the survey.

## Ambient vertex sets

In the article a hypergraph has its own vertex set, and the condition `V(X) = V(A)` in the
definitions of omni-absorbers and refiners compares *ambient* vertex sets: `X` is a spanning
subgraph of a host graph `G` on `n` vertices, and the omni-absorber (or refiner) lives on the same
vertex set.  The survey formalization `RefinedAbsorption.IsRefiner` instead uses
`vertexSet X = vertexSet R`, where `vertexSet` collects the *non-isolated* vertices.  That is a
strictly stronger condition, and it is **not** used here.  Every structure below takes the ambient
vertex set `U` as an explicit parameter and only asks that all edges lie in `U` (`IsRGraphOn`).
For the theorems, the ambient vertex set is `Finset.univ : Finset (Fin n)`, i.e. the vertex set
of the host `G`.

## Contents

* `IsRGraphOn`: `r`-graph on an ambient vertex set.
* `IsOmniAbsorberOn` (Definition 1.5: omni-absorber with decomposition family and function).
* `IsRefinedOmni` (Definition 1.6: `C`-refined), and the additional structural property
  `OneXEdgePerClique` (every clique of the common decomposition family contains at most one edge
  of `X`).
* `IsRefinerOn` (Definition 1.8: refiner with decomposition family and function),
  `IsRefinedRefinerOn` (Definition 1.9: `C`-refined refiner: pieces with at most `C` edges and at
  most `C` vertices, every edge in at most `C` pieces), `OneXEdgePerPiece`.
* `IsMultiRefinerOn` (Definition 1.10: the multigraph form of the refiner, with labelled copies,
  as produced by Theorem 3.8).
* Theorems: `Theorem_1_4` (absorber existence, Glock–Kühn–Lo–Osthus), `Theorem_1_7_for`
  (refined efficient omni-absorber inside a dense host), `Theorem_1_11_for` (refined efficient
  refiner inside a dense host), `Theorem_3_8_for` (multi-refiner theorem, with the
  lower-uniformity hypothesis), `Theorem_6_1_for` (minimum degree version of the Existence
  Conjecture, `λ = 1`).

Degree conventions: `MaxDegLE r X D` is `Δ_{r-1}(X) ≤ D` and `MinDegGE r G D` is
`δ_{r-1}(G) ≥ D`, both over all `(r-1)`-subsets of the ambient set `Fin n`.  The bound
`Δ(X) ≤ n / C` is expressed with an auxiliary real `D` with `Δ(X) ≤ D ≤ n / C`; the conclusion
bounds `Δ(A)` by `C · max(D, n^{1-1/r} log n)`.  Taking `D = Δ(X)` gives the literal statement,
and the `D`-form follows from the literal one, so the two are equivalent.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset

section Defs

variable {α : Type*} [DecidableEq α]

/-- `G` is an `r`-graph on the ambient vertex set `U`: every edge is an `r`-subset of `U`. -/
def IsRGraphOn (r : ℕ) (U : Finset α) (G : Finset (Finset α)) : Prop :=
  ∀ e ∈ G, e.card = r ∧ e ⊆ U

/-- **Definition 1.5 (omni-absorber).**  `A` is a `K_q^r`-omni-absorber for `X` (both on the
ambient vertex set `U`, i.e. `V(X) = V(A) = U`) with decomposition family `F` and decomposition
function `QA` if `X` and `A` are edge-disjoint, `F` is a family of copies of `K_q^r` (given by
their vertex sets) in `X ∪ A`, and for every `K_q^r`-divisible `L ⊆ X`, `QA L ⊆ F` is a
`K_q^r`-decomposition of `A ∪ L`. -/
structure IsOmniAbsorberOn (q r : ℕ) (U : Finset α) (X A F : Finset (Finset α))
    (QA : Finset (Finset α) → Finset (Finset α)) : Prop where
  graphX : IsRGraphOn r U X
  graphA : IsRGraphOn r U A
  disjoint : Disjoint X A
  family : ∀ Q ∈ F, Q.card = q ∧ cliqueEdges r Q ⊆ X ∪ A
  subset_family : ∀ L ⊆ X, IsDivisible q r L → QA L ⊆ F
  decomp : ∀ L ⊆ X, IsDivisible q r L → IsDecomposition q r (A ∪ L) (QA L)

/-- **Definition 1.6 (`C`-refined omni-absorber).**  Every edge of `X ∪ A` lies in at most `C`
cliques of the decomposition family `F`. -/
def IsRefinedOmni (C : ℕ) (X A F : Finset (Finset α)) : Prop :=
  ∀ e ∈ X ∪ A, cliqueMult F e ≤ C

/-- Every clique of the decomposition family contains at most one edge of `X`. -/
def OneXEdgePerClique (r : ℕ) (X F : Finset (Finset α)) : Prop :=
  ∀ Q ∈ F, ((cliqueEdges r Q).filter (· ∈ X)).card ≤ 1

/-- **Definition 1.8 (refiner).**  `R` is a `K_q^r`-refiner of `X` (both on the ambient vertex
set `U`) with decomposition family `F` and decomposition function `QR` if `X` and `R` are
edge-disjoint, `F` is a family of `K_q^r`-divisible subgraphs of `X ∪ R`, and for every
`K_q^r`-divisible `L ⊆ X`, `QR L ⊆ F` is a decomposition of `R ∪ L` into pairwise edge-disjoint
members of `F`. -/
structure IsRefinerOn (q r : ℕ) (U : Finset α) (X R : Finset (Finset α))
    (F : Finset (Finset (Finset α))) (QR : Finset (Finset α) → Finset (Finset (Finset α))) :
    Prop where
  graphX : IsRGraphOn r U X
  graphR : IsRGraphOn r U R
  disjoint : Disjoint X R
  family : ∀ H ∈ F, H ⊆ X ∪ R ∧ IsDivisible q r H
  subset_family : ∀ L ⊆ X, IsDivisible q r L → QR L ⊆ F
  pairwise : ∀ L ⊆ X, IsDivisible q r L → (QR L : Set (Finset (Finset α))).PairwiseDisjoint id
  cover : ∀ L ⊆ X, IsDivisible q r L → (QR L).sup id = R ∪ L

/-- **Definition 1.9 (`C`-refined refiner).**  Every member of the decomposition family has at
most `C` edges and at most `C` vertices, and every edge of `X ∪ R` lies in at most `C` members. -/
structure IsRefinedRefinerOn (C : ℕ) (X R : Finset (Finset α)) (F : Finset (Finset (Finset α))) :
    Prop where
  mult_le : ∀ e ∈ X ∪ R, (F.filter (fun H => e ∈ H)).card ≤ C
  card_le : ∀ H ∈ F, H.card ≤ C
  vert_le : ∀ H ∈ F, (vertexSet H).card ≤ C

/-- Every member of the decomposition family of a refiner contains at most one edge of `X`. -/
def OneXEdgePerPiece (X : Finset (Finset α)) (F : Finset (Finset (Finset α))) : Prop :=
  ∀ H ∈ F, (H.filter (· ∈ X)).card ≤ 1

/-- **Definition 1.10 (`C`-refined multi-refiner).**  The multigraph form of Definitions
1.8–1.9: copies (edges with multiplicity) are labelled by a type `E` with vertex sets `ends`,
all inside the ambient set `U`; `R` is a `C`-refined multi-refiner of `X` with family `𝒲` in the
sense of `MultiRefiner.IsMultiRefiner`. -/
def IsMultiRefinerOn (q r C : ℕ) (U : Finset α) {E : Type*} [DecidableEq E] (ends : E → Finset α)
    (X R : Finset E) (𝒲 : Finset (Finset E)) : Prop :=
  (∀ i ∈ X ∪ R, ends i ⊆ U) ∧ MultiRefiner.IsMultiRefiner q r C ends X R 𝒲

end Defs

/-- The degree budget `n^{1-1/r} log n` of the article. -/
noncomputable def budget (n r : ℕ) : ℝ := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n

/-! ### The theorems of the article -/

/-- **Theorem 1.4 (Glock–Kühn–Lo–Osthus, existence of absorbers).**  For `q > r ≥ 1`, every
`K_q^r`-divisible `r`-graph `L` has a `K_q^r`-absorber (on a possibly larger vertex set).  This is
the survey's `AbsorberExistence`; it is proved in this project (`Absorber17.absorberExistence`). -/
def Theorem_1_4 : Prop := AbsorberExistence

/-- **Theorem 1.7 (refined efficient omni-absorber in a dense host)** for fixed `q, r`: there
are an integer `C ≥ 1` and `ε > 0` such that if `G` is an `r`-graph on `n` vertices with
`δ_{r-1}(G) ≥ (1-ε) n` and `X` is a spanning subgraph of `G` with `Δ(X) ≤ n / C`, then there is a
`C`-refined `K_q^r`-omni-absorber `A ⊆ G` for `X` with
`Δ(A) ≤ C · max(Δ(X), n^{1-1/r} log n)`. -/
def Theorem_1_7_for (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G X : Finset (Finset (Fin n))) (D : ℝ),
    IsRGraph r G → MinDegGE r G ((1 - ε) * n) → X ⊆ G → MaxDegLE r X D → D ≤ n / C →
    ∃ (A F : Finset (Finset (Fin n))) (QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
      IsOmniAbsorberOn q r univ X A F QA ∧ A ⊆ G ∧ IsRefinedOmni C X A F ∧
      MaxDegLE r A (C * max D (budget n r))

/-- Theorem 1.7 together with the structural property that every clique of the decomposition
family contains at most one edge of `X` (a strengthening of `Theorem_1_7_for`). -/
def Theorem_1_7_strong_for (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G X : Finset (Finset (Fin n))) (D : ℝ),
    IsRGraph r G → MinDegGE r G ((1 - ε) * n) → X ⊆ G → MaxDegLE r X D → D ≤ n / C →
    ∃ (A F : Finset (Finset (Fin n))) (QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
      IsOmniAbsorberOn q r univ X A F QA ∧ A ⊆ G ∧ IsRefinedOmni C X A F ∧
      MaxDegLE r A (C * max D (budget n r)) ∧ OneXEdgePerClique r X F

/-- **Theorem 1.7**, for all `q > r ≥ 1`. -/
def Theorem_1_7 : Prop := ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_1_7_for q r

/-- **Theorem 1.11 (refined efficient refiner in a dense host)** for fixed `q, r`: there are an
integer `C ≥ 1` and `ε > 0` such that if `G` is an `r`-graph on `n` vertices with
`δ_{r-1}(G) ≥ (1-ε) n` and `X` is a spanning subgraph of `G` with `Δ(X) ≤ n / C`, then there is a
`C`-refined `K_q^r`-refiner `R ⊆ G` of `X` with `Δ(R) ≤ C · max(Δ(X), n^{1-1/r} log n)`. -/
def Theorem_1_11_for (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G X : Finset (Finset (Fin n))) (D : ℝ),
    IsRGraph r G → MinDegGE r G ((1 - ε) * n) → X ⊆ G → MaxDegLE r X D → D ≤ n / C →
    ∃ (R : Finset (Finset (Fin n))) (F : Finset (Finset (Finset (Fin n))))
      (QR : Finset (Finset (Fin n)) → Finset (Finset (Finset (Fin n)))),
      IsRefinerOn q r univ X R F QR ∧ R ⊆ G ∧ IsRefinedRefinerOn C X R F ∧
      MaxDegLE r R (C * max D (budget n r))

/-- Theorem 1.11 together with: every piece contains at most one edge of `X`, and every
`(r-1)`-set lies in the vertex sets of at most `C · max(Δ(X), n^{1-1/r} log n)` pieces (the
family degree needed to attach absorbers). -/
def Theorem_1_11_strong_for (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G X : Finset (Finset (Fin n))) (D : ℝ),
    IsRGraph r G → MinDegGE r G ((1 - ε) * n) → X ⊆ G → MaxDegLE r X D → D ≤ n / C →
    ∃ (R : Finset (Finset (Fin n))) (F : Finset (Finset (Finset (Fin n))))
      (QR : Finset (Finset (Fin n)) → Finset (Finset (Finset (Fin n)))),
      IsRefinerOn q r univ X R F QR ∧ R ⊆ G ∧ IsRefinedRefinerOn C X R F ∧
      MaxDegLE r R (C * max D (budget n r)) ∧ OneXEdgePerPiece X F ∧
      ∀ S : Finset (Fin n), S.card + 1 = r →
        ((F.filter fun H => S ⊆ vertexSet H).card : ℝ) ≤ C * max D (budget n r)

/-- **Theorem 1.11**, for all `q > r ≥ 1`. -/
def Theorem_1_11 : Prop := ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_1_11_for q r

/-- The conclusion of the multi-refiner theorem (Theorem 3.8) for fixed `q, r`: there is
`C ≥ 1` such that for all large `n`, every `X ⊆ K_n^r` with `Δ(X) ≤ D ≤ n / C` is the image of the
labelled copies `Xl` of a strong `C`-refined multi-refiner `R` on `Fin n` (Definition 1.10 plus:
every piece has at most one copy of `X`, `Δ(R)` and the family degree are at most
`C · B`) with budget `B ≤ C · max(D, n^{1-1/r} log n)`.  This is the project's
`Placement.NativeStrongMultiRefiners`, restated with the ambient vertex set `Fin n`. -/
def MultiRefinerConclusion (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)), ∀ D : ℝ,
    IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
    ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (K Xl R : Finset E)
      (𝒲 : Finset (Finset E)) (B : ℕ),
      Xl.image ends = X ∧ (B : ℝ) ≤ C * max D (budget n r) ∧
      IsMultiRefinerOn q r C (univ : Finset (Fin n)) ends Xl R 𝒲 ∧
      Placement.IsStrongMultiRefiner q r C ends K Xl R 𝒲 B

/-- **Theorem 3.8 (multi-refiner theorem)** for fixed `q, r`, in the inductive form of the
article: assuming the refiner theorem (Theorem 1.11) in every smaller uniformity, the
multi-refiner conclusion holds in uniformity `r`. -/
def Theorem_3_8_for (q r : ℕ) : Prop :=
  (∀ q' r' : ℕ, 1 ≤ r' → r' < r → r' < q' → Theorem_1_11_for q' r') → MultiRefinerConclusion q r

/-- **Theorem 6.1 (minimum degree version of the Existence Conjecture, `λ = 1`)** for fixed
`q, r`: there are `ε > 0` and `n₀` such that every `K_q^r`-divisible `r`-graph `G` on `n ≥ n₀`
vertices with `δ_{r-1}(G) ≥ (1-ε) n` has a `K_q^r`-decomposition. -/
def Theorem_6_1_for (q r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)),
    IsRGraph r G → MinDegGE r G ((1 - ε) * n) → IsDivisible q r G → HasDecomposition q r G

/-- **Theorem 6.1**, for all `q > r ≥ 1`. -/
def Theorem_6_1 : Prop := ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_6_1_for q r

end RefinedAbsorption.Original2024
