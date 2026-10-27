module
public import RequestProject.OddGrid.StageDiv

/-!
# Label-level decompositions and their composition

`LDecomp Dv X R Y 𝒲`: for every `L ⊆ X` satisfying `Dv`, the set `R ∪ L` is the disjoint union
of pairwise disjoint members of `𝒲` and of a residue `Res ⊆ Y` satisfying `Dv`.  This is the
decomposition clause of `IsResidualMultiRefiner`, at the level of labels.

* `LDecomp.trans`: composition (as `IsResidualMultiRefiner.trans`).
* `stage_ldecomp`: a stage of the grid refiner is an `LDecomp` for divisibility, with any residue
  set containing the residues of divisible inputs.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

section General

variable {Λ : Type} [DecidableEq Λ]

/-- Label-level decomposition property. -/
def LDecomp (Dv : Finset Λ → Prop) (X R Y : Finset Λ) (𝒲 : Finset (Finset Λ)) : Prop :=
  ∀ L ⊆ X, Dv L → ∃ 𝒰 ⊆ 𝒲, ∃ Res ⊆ Y, Dv Res ∧ (𝒰 : Set (Finset Λ)).PairwiseDisjoint id ∧
    Disjoint (𝒰.sup id) Res ∧ 𝒰.sup id ∪ Res = R ∪ L

/-- **Composition of label-level decompositions.** -/
theorem LDecomp.trans {Dv : Finset Λ → Prop} {X R₁ Y R₂ Z : Finset Λ}
    {𝒲₁ 𝒲₂ : Finset (Finset Λ)} (h₁ : LDecomp Dv X R₁ Y 𝒲₁) (h₂ : LDecomp Dv Y R₂ Z 𝒲₂)
    (hs₁ : ∀ W ∈ 𝒲₁, W ⊆ X ∪ R₁) (hR₂ : Disjoint R₂ (X ∪ R₁)) :
    LDecomp Dv X (R₁ ∪ R₂) Z (𝒲₁ ∪ 𝒲₂) := by
  intro L hL hdiv
  obtain ⟨𝒰₁, h𝒰₁, Res₁, hRes₁Y, hRes₁d, hpw₁, hd₁, heq₁⟩ := h₁ L hL hdiv
  obtain ⟨𝒰₂, h𝒰₂, Res₂, hRes₂Z, hRes₂d, hpw₂, hd₂, heq₂⟩ := h₂ Res₁ hRes₁Y hRes₁d
  have hU₁ : ∀ W ∈ 𝒰₁, Disjoint W (R₂ ∪ Res₁) := by
    intro W hW
    have hWsup : W ⊆ 𝒰₁.sup id := le_sup (f := id) hW
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left (hs₁ W (h𝒰₁ hW)) hR₂.symm,
      disjoint_of_subset_left hWsup hd₁⟩
  have hU₂ : ∀ W ∈ 𝒰₂, W ⊆ R₂ ∪ Res₁ := by
    intro W hW
    have : W ⊆ 𝒰₂.sup id ∪ Res₂ := (le_sup (f := id) hW).trans subset_union_left
    rwa [heq₂] at this
  have hRes₂ : Res₂ ⊆ R₂ ∪ Res₁ := by
    have : Res₂ ⊆ 𝒰₂.sup id ∪ Res₂ := subset_union_right
    rwa [heq₂] at this
  refine ⟨𝒰₁ ∪ 𝒰₂, union_subset_union h𝒰₁ h𝒰₂, Res₂, hRes₂Z, hRes₂d, ?_, ?_, ?_⟩
  · intro W hW W' hW' hne
    simp only [coe_union, Set.mem_union, mem_coe] at hW hW'
    rcases hW with hW | hW <;> rcases hW' with hW' | hW'
    · exact hpw₁ hW hW' hne
    · exact disjoint_of_subset_right (hU₂ W' hW') (hU₁ W hW)
    · exact (disjoint_of_subset_right (hU₂ W hW) (hU₁ W' hW')).symm
    · exact hpw₂ hW hW' hne
  · rw [sup_union, show (𝒰₁.sup id ⊔ 𝒰₂.sup id) = 𝒰₁.sup id ∪ 𝒰₂.sup id from rfl,
      disjoint_union_left]
    refine ⟨?_, hd₂⟩
    rw [Finset.disjoint_sup_left]
    exact fun W hW => disjoint_of_subset_right hRes₂ (hU₁ W hW)
  · rw [sup_union, show (𝒰₁.sup id ⊔ 𝒰₂.sup id) = 𝒰₁.sup id ∪ 𝒰₂.sup id from rfl,
      union_assoc, heq₂]
    have : 𝒰₁.sup id ∪ (R₂ ∪ Res₁) = (𝒰₁.sup id ∪ Res₁) ∪ R₂ := by
      ext i; simp only [mem_union]; tauto
    rw [this, heq₁]
    ext i; simp only [mem_union]; tauto

/-- The trivial decomposition. -/
theorem LDecomp.refl (Dv : Finset Λ → Prop) (X : Finset Λ) : LDecomp Dv X ∅ X ∅ := by
  intro L hL hdiv
  exact ⟨∅, subset_rfl, L, hL, hdiv, by simp, by simp, by simp⟩

/-- Enlarging the residue set. -/
theorem LDecomp.mono_residue {Dv : Finset Λ → Prop} {X R Y Y' : Finset Λ}
    {𝒲 : Finset (Finset Λ)} (h : LDecomp Dv X R Y 𝒲) (hY : Y ⊆ Y') : LDecomp Dv X R Y' 𝒲 := by
  intro L hL hdiv
  obtain ⟨𝒰, h𝒰, Res, hRes, h1⟩ := h L hL hdiv
  exact ⟨𝒰, h𝒰, Res, hRes.trans hY, h1⟩

/-- Enlarging the family. -/
theorem LDecomp.mono_family {Dv : Finset Λ → Prop} {X R Y : Finset Λ}
    {𝒲 𝒲' : Finset (Finset Λ)} (h : LDecomp Dv X R Y 𝒲) (hW : 𝒲 ⊆ 𝒲') :
    LDecomp Dv X R Y 𝒲' := by
  intro L hL hdiv
  obtain ⟨𝒰, h𝒰, Res, h1⟩ := h L hL hdiv
  exact ⟨𝒰, h𝒰.trans hW, Res, h1⟩

end General

/-! ### A stage as a label-level decomposition -/

variable {n K : ℕ} [NeZero K] {q : ℕ} {t : ℕ} {I : Finset (Lab n K)} {restF : RestF n K}
  {pw : Lab n K → Finset (Fin n) × ZMod K}

lemma notStage_ne_anti {ℓ : Lab n K} (h : NotStage t ℓ) (ℓ' : Lab n K) : ℓ ≠ .anti t ℓ' := by
  rintro rfl; exact h rfl

lemma notStage_ne_rest {ℓ : Lab n K} (h : NotStage t ℓ) (ℓ' : Lab n K) (k : ℕ) :
    ℓ ≠ .rest t ℓ' k := by
  rintro rfl; exact h rfl

lemma notStage_ne_cp {ℓ : Lab n K} (h : NotStage t ℓ) (e : Finset (Fin n)) (k : ℕ)
    (s : ZMod K) : ℓ ≠ .cp t e k s := by
  rintro rfl; exact h rfl

lemma notStage_ne_cn {ℓ : Lab n K} (h : NotStage t ℓ) (e : Finset (Fin n)) (k : ℕ)
    (s : ZMod K) : ℓ ≠ .cn t e k s := by
  rintro rfl; exact h rfl

/-- The labels of a stage are stage labels. -/
lemma stR_stage {x : Lab n K} (hx : x ∈ stR t I restF) :
    (∃ ℓ, x = .anti t ℓ) ∨ (∃ ℓ k, x = .rest t ℓ k) ∨ (∃ e k s, x = .cp t e k s) ∨
      (∃ e k s, x = .cn t e k s) := by
  simp only [stR, mem_union, mem_image, mem_biUnion] at hx
  rcases hx with (⟨ℓ, -, rfl⟩ | hx) | ⟨e, -, hx⟩
  · exact Or.inl ⟨ℓ, rfl⟩
  · obtain ⟨ℓ, -, k, -, rfl⟩ := mem_restSet.1 hx
    exact Or.inr (Or.inl ⟨ℓ, k, rfl⟩)
  · rcases mem_chR hx with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨e, k, s, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨e, k, s, rfl⟩))

lemma notStage_notMem_stR {ℓ : Lab n K} (h : NotStage t ℓ) : ℓ ∉ stR t I restF := by
  intro hx
  rcases stR_stage hx with ⟨ℓ', h'⟩ | ⟨ℓ', k, h'⟩ | ⟨e, k, s, h'⟩ | ⟨e, k, s, h'⟩
  · exact notStage_ne_anti h _ h'
  · exact notStage_ne_rest h _ _ h'
  · exact notStage_ne_cp h _ _ _ h'
  · exact notStage_ne_cn h _ _ _ h'

lemma disjoint_stR (hI : ∀ ℓ ∈ I, NotStage t ℓ) {Ls : Finset (Lab n K)} (hLs : Ls ⊆ I) :
    Disjoint (stR t I restF) Ls := by
  rw [Finset.disjoint_right]
  exact fun ℓ hℓ => notStage_notMem_stR (hI ℓ (hLs hℓ))

/-- Pieces of a stage lie in its inputs and labels. -/
lemma stW_subset {P : Finset (Lab n K)} (hP : P ∈ stW t I restF) : P ⊆ I ∪ stR t I restF := by
  simp only [stW, mem_union, mem_image, mem_biUnion] at hP
  rcases hP with (⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, he, hP⟩
  · intro x hx
    simp only [P1, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_union_left _ hℓ
    · exact mem_union_right _ (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hℓ)))
  · intro x hx
    simp only [P0, mem_insert] at hx
    rcases hx with rfl | hx
    · exact mem_union_right _ (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hℓ)))
    · exact mem_union_right _ (mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨ℓ, hℓ, hx⟩)))
  · intro x hx
    simp only [chW, mem_union, mem_biUnion, mem_filter, mem_product, mem_univ, and_true,
      mem_insert, mem_singleton, mem_image] at hP
    have hcp : ∀ k s, 1 ≤ k → k ≤ slen t I restF e → Lab.cp t e k s ∈ stR t I restF := by
      intro k s h1 h2
      refine mem_union_right _ (mem_biUnion.2 ⟨e, he, ?_⟩)
      simp only [chR, mem_union, mem_image, mem_product, mem_Icc, mem_univ, and_true]
      exact Or.inl (Or.inr ⟨(k, s), ⟨h1, h2⟩, rfl⟩)
    have hcp0 : ∀ s, Lab.cp t e 0 s ∈ stR t I restF → True := fun _ _ => trivial
    have hcpk : ∀ k s, k ≤ slen t I restF e → (k = 0 → s = 0) →
        Lab.cp t e k s ∈ stR t I restF := by
      intro k s h2 h0
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [h0 rfl]
        refine mem_union_right _ (mem_biUnion.2 ⟨e, he, ?_⟩)
        simp [chR]
      · exact hcp k s hk h2
    have hcn : ∀ k s, 1 ≤ k → k ≤ slen t I restF e → Lab.cn t e k s ∈ stR t I restF := by
      intro k s h1 h2
      refine mem_union_right _ (mem_biUnion.2 ⟨e, he, ?_⟩)
      simp only [chR, mem_union, mem_image, mem_product, mem_Icc, mem_univ, and_true]
      exact Or.inr ⟨(k, s), ⟨h1, h2⟩, rfl⟩
    clear hcp0
    rcases hP with ⟨⟨k, s⟩, ⟨hk, hs⟩, rfl | rfl⟩ | ⟨⟨k, s⟩, hk, rfl⟩
    · have hk' := mem_Icc.1 hk
      simp only [chT, if_true, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_union_right _ (hcpk _ _ (by omega) (fun h => hs (by omega)))
      · exact mem_union_right _ (mem_union_left _ (mem_union_right _
          (mem_onPair.1 (item_mem hk)).1))
      · exact mem_union_right _ (hcn _ _ hk'.1 hk'.2)
    · have hk' := mem_Icc.1 hk
      simp only [chT, Bool.false_eq_true, if_false, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_union_right _ (hcpk _ _ (by omega) (fun h => hs (by omega)))
      · exact mem_union_right _ (hcn _ _ hk'.1 hk'.2)
    · have hk' := mem_Icc.1 hk
      simp only [chQ, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_union_right _ (hcn _ _ hk'.1 hk'.2)
      · exact mem_union_right _ (hcp _ _ hk'.1 hk'.2)

/-- The residue carries are labels of the stage. -/
lemma stRes_subset (Ls : Finset (Lab n K)) : stRes t I restF Ls ⊆ stR t I restF := by
  intro x hx
  simp only [stRes, mem_image] at hx
  obtain ⟨e, he, rfl⟩ := hx
  refine mem_union_right _ (mem_biUnion.2 ⟨e, he, ?_⟩)
  rcases Nat.eq_zero_or_pos (slen t I restF e) with h0 | hpos
  · rw [h0, show sig t I restF e Ls = 0 by rw [sig, h0, psum_zero]]
    simp [chR]
  · simp only [chR, mem_union, mem_image, mem_product, mem_Icc, mem_univ, and_true]
    exact Or.inl (Or.inr ⟨(_, _), ⟨hpos, le_rfl⟩, rfl⟩)

variable (hd : q - 1 ∣ K) (hN : q.choose 2 ∣ K)

include hd hN in
lemma ldiv_stW (hpw : StagePW t restF pw) (hP0 : ∀ ℓ ∈ I, LDiv q pw (P0 t restF ℓ))
    {P : Finset (Lab n K)} (hP : P ∈ stW t I restF) : LDiv q pw P := by
  simp only [stW, mem_union, mem_image, mem_biUnion] at hP
  rcases hP with (⟨ℓ, -, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, -, hP⟩
  · exact ldiv_P1 hd hN hpw ℓ
  · exact hP0 ℓ hℓ
  · exact ldiv_chW hd hN hpw hP

include hd hN in
/-- The labels of a stage form a divisible multigraph. -/
lemma ldiv_stR (hpw : StagePW t restF pw) (hI : ∀ ℓ ∈ I, NotStage t ℓ)
    (hP0 : ∀ ℓ ∈ I, LDiv q pw (P0 t restF ℓ)) : LDiv q pw (stR t I restF) := by
  obtain ⟨hsub, hpd, hdj, heq⟩ := stage_decomp (restF := restF) hI ∅ (empty_subset _)
  rw [union_empty] at heq
  rw [← heq]
  refine ldiv_union hdj (ldiv_sup hpd fun P hP => ldiv_stW hd hN hpw hP0 (hsub hP))
    (ldiv_of_wt_zero ?_)
  intro x hx
  simp only [stRes, mem_image] at hx
  obtain ⟨e, -, rfl⟩ := hx
  rw [hpw.cp, sig_eq_sum e ∅ (empty_subset _), sum_empty]

include hd hN in
/-- **A stage is a label-level decomposition.** -/
theorem stage_ldecomp (hpw : StagePW t restF pw) (hI : ∀ ℓ ∈ I, NotStage t ℓ)
    (hP0 : ∀ ℓ ∈ I, LDiv q pw (P0 t restF ℓ)) (Y : Finset (Lab n K))
    (hY : ∀ Ls ⊆ I, LDiv q pw Ls → stRes t I restF Ls ⊆ Y) :
    LDecomp (LDiv q pw) I (stR t I restF) Y (stW t I restF) := by
  intro Ls hLs hdiv
  obtain ⟨hsub, hpd, hdj, heq⟩ := stage_decomp (restF := restF) hI Ls hLs
  refine ⟨_, hsub, _, hY Ls hLs hdiv, ?_, hpd, hdj, heq⟩
  exact ldiv_of_partition (ldiv_union (disjoint_stR hI hLs) (ldiv_stR hd hN hpw hI hP0) hdiv)
    hpd (fun P hP => ldiv_stW hd hN hpw hP0 (hsub hP)) hdj heq

end RefinedAbsorption.OddGrid
