module
public import RequestProject.MultiRefiner.Basic

/-!
# Restricting a residual multi-refiner to a sub-multigraph

A residual multi-refiner of `X` is also one of every `X' ⊆ X`: keep the pieces that lie inside
`X' ∪ R`.  The decompositions needed for a divisible `L ⊆ X'` only use pieces inside `R ∪ L`.
Hence one *universal* refiner of a complete multigraph serves every sub-multigraph at once.
-/

@[expose] public section

namespace RefinedAbsorption.MultiRefiner

open Finset

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- **Restriction of a residual multi-refiner** to a sub-multigraph `X' ⊆ X`. -/
theorem IsResidualMultiRefiner.restrict {q r C : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) {X' : Finset E}
    (hX' : X' ⊆ X) :
    IsResidualMultiRefiner q r C ends X' R Y (𝒲.filter fun W => W ⊆ X' ∪ R) where
  rgraph i hi := h.rgraph i (union_subset_union hX' subset_rfl hi)
  disjoint := disjoint_of_subset_left hX' h.disjoint
  divisible W hW := h.divisible W (mem_filter.1 hW).1
  subset W hW := (mem_filter.1 hW).2
  card_le W hW := h.card_le W (mem_filter.1 hW).1
  mult_le i hi := by
    refine le_trans (card_le_card fun W hW => ?_) (h.mult_le i (union_subset_union hX' subset_rfl hi))
    simp only [mem_filter] at hW ⊢
    exact ⟨hW.1.1, hW.2⟩
  decomp L hL hdiv := by
    obtain ⟨𝒰, h𝒰, Res, hRes, hdivRes, hpw, hdisj, heq⟩ := h.decomp L (hL.trans hX') hdiv
    refine ⟨𝒰, fun U hU => mem_filter.2 ⟨h𝒰 hU, ?_⟩, Res, hRes, hdivRes, hpw, hdisj, heq⟩
    have h1 : U ⊆ 𝒰.sup id := le_sup (f := id) hU
    have h2 : 𝒰.sup id ⊆ R ∪ L := heq ▸ subset_union_left
    intro x hx
    rcases mem_union.1 (h2 (h1 hx)) with hxR | hxL
    · exact mem_union_right _ hxR
    · exact mem_union_left _ (hL hxL)

/-- **Restriction of a multi-refiner** (empty residue) to a sub-multigraph. -/
theorem IsMultiRefiner.restrict {q r C : ℕ} {ends : E → Finset V} {X R : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsMultiRefiner q r C ends X R 𝒲) {X' : Finset E}
    (hX' : X' ⊆ X) : IsMultiRefiner q r C ends X' R (𝒲.filter fun W => W ⊆ X' ∪ R) :=
  IsResidualMultiRefiner.restrict h hX'

end RefinedAbsorption.MultiRefiner
