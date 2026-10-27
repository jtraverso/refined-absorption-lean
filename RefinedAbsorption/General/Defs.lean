module
public import RefinedAbsorption.SparseChain.ThreeGraphs

/-!
# Flat clique omni-absorbers in every uniformity (definition)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Theorem 3.7 (Refined Multi-Omni-Absorber
Theorem with the flatness conclusion (2)) and Remark 3.9 (the pieces are cliques), in the local form
used in §4.  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`FlatOmniK q k a`: every `k`-multigraph `L` of bounded multiplicity inside `Y`, with
`(k-1)`-degrees `≤ d`, has, for every set `P` of new vertices disjoint from `Y` with
`|Y| ≤ K |P|` and `Ch · d ≤ |P|`, a complete `K_q^k`-multi-refiner inside `Y ∪ P` such that

* every new copy meets `P` (flatness);
* the new copies have `(k-1)`-degrees `≤ C (d + a |P|)` and multiplicities `≤ C`;
* every piece is a clique: every `k`-subset of the span of a piece carries a copy of the piece;
* the span of every piece meets `Y` in at most `k` vertices (each piece contains at most one
  copy of `L`).
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.FlatDown
  RefinedAbsorption.Sharp RefinedAbsorption.RefineDown

/-- **Flat clique omni-absorbers in uniformity `k`, sparse form** (see the module docstring). -/
def FlatOmniK (q k : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ C Ch : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (Y P : Finset (Fin n)) (L : Finset E) (d : ℕ),
    Disjoint Y P → Y.card ≤ K * P.card → Ch ≤ P.card → Ch * d ≤ P.card →
    MIsRGraph k ends L → (∀ x ∈ L, ends x ⊆ Y) →
    (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends L S ≤ d) →
    (∀ e, mult ends L e ≤ K) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R : Finset E') (𝒲 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsMultiRefiner q k C ends' (L.image g) R 𝒲 ∧
      (∀ c ∈ R, ends' c ⊆ Y ∪ P ∧ (ends' c ∩ P).Nonempty) ∧
      (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends' R S ≤ C * (d + a P.card)) ∧
      (∀ e, mult ends' R e ≤ C) ∧
      (∀ W ∈ 𝒲, ∀ S ⊆ W.biUnion ends', S.card = k → ∃ c ∈ W, ends' c = S) ∧
      (∀ W ∈ 𝒲, (W.biUnion ends' ∩ Y).card ≤ k)

end RefinedAbsorption.General
