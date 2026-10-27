module
public import Mathlib

/-!
# Section 2.2 of arXiv:2402.17855v1: Definitions 2.6, 2.7 and Theorem 2.8 (Nibble with Reserves)

Multi-hypergraphs are given by labelled copies `ends : E → Finset V` (parallel copies allowed);
degrees and codegrees count copies.

* `IsMatchingL`, `IsAPerfectMatching` — Definition 2.6;
* `IsBipartiteHyp` — Definition 2.7 (as printed: `V(G) = A ∪ B` and every edge contains exactly one
  vertex of `A`; the printed definition does not require `A ∩ B = ∅`, and neither does this one);
* `Theorem_2_8` — **Theorem 2.8 (Nibble with Reserves)**, the general statement for an `r`-uniform
  (multi-)hypergraph `G = G₁ ⊔ G₂`.

`Theorem_2_8` is **not proved** here.  The project proves specialised consumers of nibble with
reserves for clique hypergraphs (`RefinedAbsorption.NibbleWithReserves`,
`RefinedAbsorption.NibbleWithReservesGen`, `NibbleWithReservesMulti`) and a general pseudo-random
matching theorem without reserves (`RefinedAbsorption.Nibble.localNibble`); none of them is the
general statement below, and they are not presented as a substitute.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset

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

end RefinedAbsorption.Faithful2024
