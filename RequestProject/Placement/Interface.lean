module
public import RequestProject.MultiRefiner.Basic

/-!
# The strong intermediate interface

The structures `IsRefinedRefiner` and `IsOmniAbsorber` used by the consumers proved earlier are
deliberately weak: they do not remember the extra invariants of the original construction.  The
final embedding step needs them, so we record them here in stronger structures, which project to
the weak ones (`IsStrongRefiner.toRefinedRefiner`), so all proved consumers keep working.

* **at most one `X`-edge** per piece (`oneX`): each piece of the family contains at most one edge
  (copy) of `X`;
* **degree budgets**: `Δ_{r-1}(X) ≤ D` and `Δ_{r-1}(R) ≤ C · D`;
* **refinement degree** (`pieceDeg`): every `(r-1)`-set lies in the vertex sets of at most
  `C · D` pieces.  This is the root-family degree needed to place absorbers on the pieces with
  the Partial Clique Embedding Lemma.

`IsStrongMultiRefiner` is the labelled-multigraph analogue (copies labelled by `E`, with a set
`K ⊇ X` of kept copies on which `ends` is injective).
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner

/-- **Strong refined refiner** on `Fin n` with degree budget `D`. -/
structure IsStrongRefiner (q r C : ℕ) {n : ℕ} (X R : Finset (Finset (Fin n)))
    (𝒲 : Finset (Finset (Finset (Fin n)))) (D : ℕ) : Prop where
  refiner : IsRefinedRefiner q r C X R 𝒲
  oneX : ∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1
  degX : ∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ D
  degR : ∀ S : Finset (Fin n), S.card = r - 1 → deg R S ≤ C * D
  pieceDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
    (𝒲.filter fun W => S ⊆ vertexSet W).card ≤ C * D

theorem IsStrongRefiner.toRefinedRefiner {q r C n : ℕ} {X R : Finset (Finset (Fin n))}
    {𝒲 : Finset (Finset (Finset (Fin n)))} {D : ℕ} (h : IsStrongRefiner q r C X R 𝒲 D) :
    IsRefinedRefiner q r C X R 𝒲 := h.refiner

/-- **Strong multi-refiner** (labelled copies) on `Fin n` with degree budget `D`. -/
structure IsStrongMultiRefiner (q r C : ℕ) {n : ℕ} {E : Type*} [DecidableEq E]
    (ends : E → Finset (Fin n)) (K X R : Finset E) (𝒲 : Finset (Finset E)) (D : ℕ) : Prop where
  refiner : IsMultiRefiner q r C ends X R 𝒲
  keep : X ⊆ K
  inj : Set.InjOn ends K
  oneX : ∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1
  degX : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D
  degR : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends R S ≤ C * D
  pieceDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
    (𝒲.filter fun W => S ⊆ W.biUnion ends).card ≤ C * D

end RefinedAbsorption.Placement
