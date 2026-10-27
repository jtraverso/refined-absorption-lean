module
public import RefinedAbsorption.Dense.Stage
public import RefinedAbsorption.MultiRefiner.Chain

/-!
# Multigraph refiners inside a reserve, by iterated stages

Starting from a labelled `r`-multigraph `X` whose copies lie in a set `Z`, we apply stages
(`multiStage`) into nested reserves `Z ⊇ Z₁ ⊇ Z₂ ⊇ …`, each a quarter of the previous one, until
the reserve has bounded size, and finish with multiplicity reduction and the finite step.

* `IsChainRefiner.prepend`: a stage (residual refiner whose residue consists of its own copies)
  followed by a complete chain refiner of its residue is a complete chain refiner, *with the same
  constants*.  Hence the refinedness of the final refiner does not depend on the number of
  stages.
* `denseRefiner`: every `X` inside `Z` with `(r-1)`-degrees `≤ D` has a complete refiner with all
  copies inside `Z` and `(r-1)`-degrees `≤ A · D + B · |Z|`.  After the first stage the residue
  has multiplicity `≤ M`, hence degree `≤ M · |Z₁|`, and the reserves shrink geometrically, so the
  degrees of the later stages sum to `O(|Z|)`.
* **`stagedRefiner`**: for every `t`, the same with `(r-1)`-degrees
  `≤ C_t · D + B · |Z| / 2^t` (stated as `2^t · deg ≤ 2^t · C_t · D + B · |Z|`): the first `t`
  stages keep the residue sparse (degree `O(D)`), and only then the dense bound is used.  The
  refinedness constant `C` and `B` do not depend on `t`.

Everything is conditional on placed link refiners at the levels `1, …, r - 1`, which are proved
for `r = 2`.
-/

@[expose] public section

namespace RefinedAbsorption.Dense

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

theorem _root_.RefinedAbsorption.MultiRefiner.IsChainRefiner.mono' {q r A B P A' B' P' : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsChainRefiner q r A B P ends X R Y 𝒲) (hA : A ≤ A')
    (hB : B ≤ B') (hP : P ≤ P') : IsChainRefiner q r A' B' P' ends X R Y 𝒲 where
  base := h.base.mono (by omega)
  card_le W hW := (h.card_le W hW).trans hP
  residue_sub := h.residue_sub
  multX i hi := (h.multX i hi).trans hA
  multR i hi := (h.multR i hi).trans (by omega)
  multY i hi := (h.multY i hi).trans hB

/-- **Prepending a stage.**  A residual refiner `R₁` of `X` with constant `C₁ ≤ C` whose residue
`Y₁` consists of its own copies, followed by a complete chain refiner `R₂` of `Y₁` with constants
`C, C, C`, is a complete chain refiner of `X` with the same constants. -/
theorem _root_.RefinedAbsorption.MultiRefiner.IsChainRefiner.prepend {q r C₁ C : ℕ} {ends : E → Finset V} {X R₁ Y₁ R₂ : Finset E}
    {𝒲₁ 𝒲₂ : Finset (Finset E)} (h₁ : IsResidualMultiRefiner q r C₁ ends X R₁ Y₁ 𝒲₁)
    (hY₁ : Y₁ ⊆ R₁) (hC : C₁ ≤ C) (h₂ : IsChainRefiner q r C C C ends Y₁ R₂ ∅ 𝒲₂)
    (hR₂ : Disjoint R₂ (X ∪ R₁)) :
    IsChainRefiner q r C C C ends X (R₁ ∪ R₂) ∅ (𝒲₁ ∪ 𝒲₂) := by
  have ht := h₁.trans h₂.base (hY₁.trans subset_union_right) hR₂
  have hXR₁ : Disjoint X R₁ := h₁.disjoint
  have hcnt : ∀ i, (𝒲₁ ∪ 𝒲₂).filter (fun W => i ∈ W) =
      𝒲₁.filter (fun W => i ∈ W) ∪ 𝒲₂.filter (fun W => i ∈ W) := fun i => filter_union _ _ _
  have hX₂ : ∀ i ∈ X, 𝒲₂.filter (fun W => i ∈ W) = ∅ := by
    intro i hi
    apply h₂.base.filter_mem_eq_empty
    rw [mem_union, not_or]
    exact ⟨fun hY => disjoint_left.1 hXR₁ hi (hY₁ hY),
      fun hR => disjoint_left.1 hR₂ hR (mem_union_left _ hi)⟩
  have hR₂₁ : ∀ i ∈ R₂, 𝒲₁.filter (fun W => i ∈ W) = ∅ :=
    fun i hi => h₁.filter_mem_eq_empty (disjoint_left.1 hR₂ hi)
  have hmultX : ∀ i ∈ X, ((𝒲₁ ∪ 𝒲₂).filter (fun W => i ∈ W)).card ≤ C := by
    intro i hi
    rw [hcnt, hX₂ i hi, union_empty]
    exact (h₁.mult_le i (mem_union_left _ hi)).trans hC
  have hmultR : ∀ i ∈ R₁ ∪ R₂, ((𝒲₁ ∪ 𝒲₂).filter (fun W => i ∈ W)).card ≤ C + C := by
    intro i hi
    rcases mem_union.1 hi with hi | hi
    · rw [hcnt]
      refine (card_union_le _ _).trans ?_
      have h1 := h₁.mult_le i (mem_union_right _ hi)
      by_cases hiY : i ∈ Y₁
      · have h2 := h₂.multX i hiY
        omega
      · have hi₂ : i ∉ Y₁ ∪ R₂ := by
          rw [mem_union, not_or]
          exact ⟨hiY, fun h => disjoint_left.1 hR₂ h (mem_union_right _ hi)⟩
        rw [h₂.base.filter_mem_eq_empty hi₂, card_empty, add_zero]
        omega
    · rw [hcnt, hR₂₁ i hi, empty_union]
      exact h₂.multR i hi
  refine ⟨{ ht with card_le := fun W hW => ?_, mult_le := fun i hi => ?_ }, fun W hW => ?_,
    empty_subset _, hmultX, hmultR, by simp⟩
  · rcases mem_union.1 hW with hW | hW
    · exact (h₁.card_le W hW).trans (by omega)
    · exact (h₂.card_le W hW).trans (by omega)
  · rcases mem_union.1 hi with hi | hi
    · exact (hmultX i hi).trans (by omega)
    · exact (hmultR i hi).trans (by omega)
  · rcases mem_union.1 hW with hW | hW
    · exact (h₁.card_le W hW).trans hC
    · exact h₂.card_le W hW

/-- Prepending a stage after relabelling. -/
theorem _root_.RefinedAbsorption.MultiRefiner.IsChainRefiner.prepend_relabel {E₁ E₂ : Type*} [DecidableEq E₁] [DecidableEq E₂]
    {q r C₁ C : ℕ} {ends₁ : E₁ → Finset V} {ends₂ : E₂ → Finset V} {X R₁ Y₁ : Finset E₁}
    {𝒲₁ : Finset (Finset E₁)} (h₁ : IsResidualMultiRefiner q r C₁ ends₁ X R₁ Y₁ 𝒲₁)
    (hY₁ : Y₁ ⊆ R₁) (hC : C₁ ≤ C) (g : E₁ → E₂) (hg : Function.Injective g)
    (hends : ∀ c, ends₂ (g c) = ends₁ c) {R₂ : Finset E₂} {𝒲₂ : Finset (Finset E₂)}
    (h₂ : IsChainRefiner q r C C C ends₂ (Y₁.image g) R₂ ∅ 𝒲₂)
    (hR₂ : ∀ c ∈ R₂, ∀ x, g x ≠ c) :
    IsChainRefiner q r C C C ends₂ (X.image g) (R₁.image g ∪ R₂) ∅
      (𝒲₁.image (image g) ∪ 𝒲₂) := by
  have h₁' := residual_relabel h₁ g ends₂ (fun c _ => hends c) hg.injOn
    (hY₁.trans subset_union_right)
  refine IsChainRefiner.prepend h₁' (image_subset_image hY₁) hC h₂ ?_
  rw [disjoint_left]
  intro c hc hc'
  rw [← image_union] at hc'
  obtain ⟨x, -, rfl⟩ := mem_image.1 hc'
  exact hR₂ _ hc x rfl

omit [DecidableEq V] in
/-- An `r`-multigraph inside `Z` with multiplicity `≤ M` has `(r-1)`-degrees `≤ M · |Z|`. -/
theorem mdeg_le_of_mult [DecidableEq V] {r M : ℕ} {ends : E → Finset V} {Y : Finset E}
    {Z : Finset V} (hYr : MIsRGraph r ends Y) (hYZ : ∀ c ∈ Y, ends c ⊆ Z)
    (hmult : ∀ e, mult ends Y e ≤ M) (S : Finset V) (hS : S.card + 1 = r) :
    mdeg ends Y S ≤ M * Z.card := by
  have hsub : Y.filter (fun c => S ⊆ ends c) ⊆
      Z.biUnion fun v => Y.filter (fun c => ends c = insert v S) := by
    intro c hc
    obtain ⟨hcY, hSc⟩ := mem_filter.1 hc
    have hcard : (ends c \ S).card = 1 := by
      rw [card_sdiff_of_subset hSc, hYr c hcY]; omega
    obtain ⟨v, hv⟩ := card_eq_one.1 hcard
    have hvc : v ∈ ends c \ S := by rw [hv]; exact mem_singleton_self v
    refine mem_biUnion.2 ⟨v, hYZ c hcY (mem_sdiff.1 hvc).1, mem_filter.2 ⟨hcY, ?_⟩⟩
    ext w
    constructor
    · intro hw
      by_cases hwS : w ∈ S
      · exact mem_insert_of_mem hwS
      · have : w ∈ ends c \ S := mem_sdiff.2 ⟨hw, hwS⟩
        rw [hv, mem_singleton] at this
        rw [this]; exact mem_insert_self _ _
    · intro hw
      rcases mem_insert.1 hw with rfl | hw
      · exact (mem_sdiff.1 hvc).1
      · exact hSc hw
  calc mdeg ends Y S ≤ _ := card_le_card hsub
    _ ≤ ∑ v ∈ Z, (Y.filter (fun c => ends c = insert v S)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ Z, M := sum_le_sum fun v _ => hmult _
    _ = M * Z.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- A multigraph inside `Z` with multiplicity `≤ M` has at most `M · 2^|Z|` copies. -/
theorem card_le_of_mult {M : ℕ} {ends : E → Finset V} {Y : Finset E} {Z : Finset V}
    (hYZ : ∀ c ∈ Y, ends c ⊆ Z) (hmult : ∀ e, mult ends Y e ≤ M) :
    Y.card ≤ M * 2 ^ Z.card := by
  have hsub : Y ⊆ Z.powerset.biUnion fun e => Y.filter (fun c => ends c = e) := by
    intro c hc
    exact mem_biUnion.2 ⟨ends c, mem_powerset.2 (hYZ c hc), mem_filter.2 ⟨hc, rfl⟩⟩
  calc Y.card ≤ _ := card_le_card hsub
    _ ≤ ∑ e ∈ Z.powerset, (Y.filter (fun c => ends c = e)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ Z.powerset, M := sum_le_sum fun e _ => hmult e
    _ = M * 2 ^ Z.card := by rw [sum_const, card_powerset, smul_eq_mul, mul_comm]

end RefinedAbsorption.Dense
