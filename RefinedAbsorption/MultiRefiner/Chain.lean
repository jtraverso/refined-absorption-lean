module
public import RefinedAbsorption.MultiRefiner.Basic

/-!
# Chains of residual refiners with a uniform refinement constant

`IsResidualMultiRefiner.trans` adds the refinement constants of the two refiners.  Chaining `t`
refine-down stages with it gives a constant growing linearly in `t`, while the refine-down
iteration of the survey (Section 3.4) uses `Θ(log n)` stages.

Here we keep track of *where* each copy lies.  When the residue of every stage consists of copies
created in that stage (`Y ⊆ R`), every copy is touched by the pieces of at most two consecutive
stages: the stage creating it and, if it lies in the residue, the next one.  This gives a
constant that does not depend on the number of stages.

* `IsChainRefiner q r A B P ends X R Y 𝒲`: a residual refiner of `X` with residue `Y ⊆ R`, pieces
  of size `≤ P`, every copy of `X` in at most `A` pieces, every copy of `R` in at most `A + B`
  pieces and every copy of the residue `Y` in at most `B` pieces.
* `IsChainRefiner.ofResidual`: a single stage with constant `C` and `Y ⊆ R` is a chain refiner
  with `A = B = P = C`.
* **`IsChainRefiner.trans`**: appending a stage with constant `C ≤ min(A, B, P)` keeps the *same*
  parameters `A, B, P`.
* `IsChainRefiner.toResidual`: a chain refiner is a residual refiner with constant `P + A + B`,
  whatever the number of stages.
-/

@[expose] public section

namespace RefinedAbsorption.MultiRefiner

open Finset

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- **Chain refiner**: a residual refiner whose residue consists of its own copies, with
separate refinement bounds for the copies of `X`, of `R` and of the residue. -/
structure IsChainRefiner (q r A B P : ℕ) (ends : E → Finset V) (X R Y : Finset E)
    (𝒲 : Finset (Finset E)) : Prop where
  base : IsResidualMultiRefiner q r (P + A + B) ends X R Y 𝒲
  card_le : ∀ W ∈ 𝒲, W.card ≤ P
  residue_sub : Y ⊆ R
  multX : ∀ i ∈ X, (𝒲.filter (fun W => i ∈ W)).card ≤ A
  multR : ∀ i ∈ R, (𝒲.filter (fun W => i ∈ W)).card ≤ A + B
  multY : ∀ i ∈ Y, (𝒲.filter (fun W => i ∈ W)).card ≤ B

/-- A chain refiner is a residual refiner with constant `P + A + B`, independently of the number
of stages it was built from. -/
theorem IsChainRefiner.toResidual {q r A B P : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsChainRefiner q r A B P ends X R Y 𝒲) :
    IsResidualMultiRefiner q r (P + A + B) ends X R Y 𝒲 := h.base

/-- **One stage.**  A residual refiner with constant `C` whose residue consists of its own
copies is a chain refiner with `A = B = P = C`. -/
theorem IsChainRefiner.ofResidual {q r C : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (hY : Y ⊆ R) :
    IsChainRefiner q r C C C ends X R Y 𝒲 where
  base := h.mono (by omega)
  card_le := h.card_le
  residue_sub := hY
  multX i hi := h.mult_le i (mem_union_left _ hi)
  multR i hi := (h.mult_le i (mem_union_right _ hi)).trans (by omega)
  multY i hi := h.mult_le i (mem_union_right _ (hY hi))

/-- Pieces of a residual refiner only contain copies of `X ∪ R`. -/
theorem IsResidualMultiRefiner.filter_mem_eq_empty {q r C : ℕ} {ends : E → Finset V}
    {X R Y : Finset E} {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲)
    {i : E} (hi : i ∉ X ∪ R) : 𝒲.filter (fun W => i ∈ W) = ∅ :=
  filter_eq_empty_iff.2 fun W hW hiW => hi (h.subset W hW hiW)

/-- **Appending a stage keeps the parameters.**  If the chain `R₁` refines `X` with residue
`Y ⊆ R₁`, and a stage `R₂` with constant `C ≤ min(A, B, P)` (sharing no copy with `X ∪ R₁`)
refines `Y` with residue `Z ⊆ R₂`, then `R₁ ∪ R₂` is a chain refiner of `X` with residue `Z` and
the same parameters `A, B, P`. -/
theorem IsChainRefiner.trans {q r A B P C : ℕ} {ends : E → Finset V} {X R₁ Y R₂ Z : Finset E}
    {𝒲₁ 𝒲₂ : Finset (Finset E)} (h₁ : IsChainRefiner q r A B P ends X R₁ Y 𝒲₁)
    (h₂ : IsResidualMultiRefiner q r C ends Y R₂ Z 𝒲₂) (hCA : C ≤ A) (hCB : C ≤ B)
    (hCP : C ≤ P) (hZ : Z ⊆ R₂) (hR₂ : Disjoint R₂ (X ∪ R₁)) :
    IsChainRefiner q r A B P ends X (R₁ ∪ R₂) Z (𝒲₁ ∪ 𝒲₂) := by
  have hYR : Y ⊆ X ∪ R₁ := h₁.residue_sub.trans subset_union_right
  have ht := h₁.base.trans h₂ hYR hR₂
  have hXR₁ : Disjoint X R₁ := h₁.base.disjoint
  -- refinement counts, split by origin of the copy
  have hcnt : ∀ i, (𝒲₁ ∪ 𝒲₂).filter (fun W => i ∈ W) =
      𝒲₁.filter (fun W => i ∈ W) ∪ 𝒲₂.filter (fun W => i ∈ W) := fun i => filter_union _ _ _
  have hX₂ : ∀ i ∈ X, 𝒲₂.filter (fun W => i ∈ W) = ∅ := by
    intro i hi
    apply h₂.filter_mem_eq_empty
    rw [mem_union, not_or]
    exact ⟨fun hY => disjoint_left.1 hXR₁ hi (h₁.residue_sub hY),
      fun hR => disjoint_left.1 hR₂ hR (mem_union_left _ hi)⟩
  have hR₂₁ : ∀ i ∈ R₂, 𝒲₁.filter (fun W => i ∈ W) = ∅ :=
    fun i hi => h₁.base.filter_mem_eq_empty (disjoint_left.1 hR₂ hi)
  have hcR₂ : ∀ i ∈ R₂, ((𝒲₁ ∪ 𝒲₂).filter (fun W => i ∈ W)).card ≤ C := by
    intro i hi
    rw [hcnt, hR₂₁ i hi, empty_union]
    exact h₂.mult_le i (mem_union_right _ hi)
  have hmultR : ∀ i ∈ R₁ ∪ R₂, ((𝒲₁ ∪ 𝒲₂).filter (fun W => i ∈ W)).card ≤ A + B := by
    intro i hi
    rcases mem_union.1 hi with hi | hi
    · rw [hcnt]
      refine (card_union_le _ _).trans ?_
      by_cases hiY : i ∈ Y
      · have h1 := h₁.multY i hiY
        have h2 := h₂.mult_le i (mem_union_left _ hiY)
        omega
      · have hi₂ : i ∉ Y ∪ R₂ := by
          rw [mem_union, not_or]
          exact ⟨hiY, fun h => disjoint_left.1 hR₂ h (mem_union_right _ hi)⟩
        rw [h₂.filter_mem_eq_empty hi₂, card_empty, add_zero]
        exact h₁.multR i hi
    · exact (hcR₂ i hi).trans (by omega)
  refine ⟨?_, ?_, hZ.trans subset_union_right, ?_, hmultR, ?_⟩
  · refine { ht with card_le := fun W hW => ?_, mult_le := fun i hi => ?_ }
    · rcases mem_union.1 hW with hW | hW
      · exact (h₁.card_le W hW).trans (by omega)
      · exact (h₂.card_le W hW).trans (by omega)
    · rcases mem_union.1 hi with hi | hi
      · rw [hcnt, hX₂ i hi, union_empty]
        exact (h₁.multX i hi).trans (by omega)
      · exact (hmultR i hi).trans (by omega)
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · exact h₁.card_le W hW
    · exact (h₂.card_le W hW).trans hCP
  · intro i hi
    rw [hcnt, hX₂ i hi, union_empty]
    exact h₁.multX i hi
  · intro i hi
    exact (hcR₂ i (hZ hi)).trans hCB

end RefinedAbsorption.MultiRefiner
