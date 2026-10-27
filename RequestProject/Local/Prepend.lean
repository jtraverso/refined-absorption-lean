module
public import RequestProject.LinkSpread.TRefOut

/-!
# A tagged stage followed by complete refiners using the whole reserve

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, §4).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`TStageOut.prepend'` is `TStageOut.prepend` where the second construction (complete tagged
refiners of the residue, which lies in the sub-reserve `Z₁`) may place its new copies anywhere in
the reserve `Zo`.  This is what the random embedding needs: the residues live in `Z₁` and the
new vertices of their local refiners are taken from `Zo \ Z₁`.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

set_option maxHeartbeats 4000000 in
/-- **A stage followed by complete refiners of its residue, using the whole reserve.**  As
`TStageOut.prepend`, but the complete tagged refiners of the residue (which lies inside `Z₁`) may
use all of `Zo`; the budgets add up. -/
theorem TStageOut.prepend' {q r i Cr M C : ℕ} (hC : Cr ≤ C) {n : ℕ} {E : Type}
    [DecidableEq E] {tg bd : E → Finset (Fin n)} {Zo Z₁ : Finset (Fin n)} {X : Finset E}
    {Bd₁ : ℕ} (htg : ∀ x, Disjoint (tg x) Zo) (htgc : ∀ x ∈ X, (tg x).card = i)
    (P : ℕ → Prop) (h : TStageOut q r i Cr M tg bd Zo Z₁ X Bd₁)
    (hnext : ∀ (E₁ : Type) [DecidableEq E₁] (tg₁ bd₁ : E₁ → Finset (Fin n)) (X₁ : Finset E₁),
      (∀ x, Disjoint (tg₁ x) Zo) → (∀ x, bd₁ x ⊆ Z₁) → (∀ x ∈ X₁, (tg₁ x).card = i) →
      (∀ x ∈ X₁, (bd₁ x).card = r - i) → X₁.image tg₁ ⊆ X.image tg →
      (∀ T e, mult bd₁ (fibre tg₁ X₁ T) e ≤ M) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg₁ bd₁) X₁ S ≤ Bd₁) →
      ∃ Bd₂, P Bd₂ ∧ TRefOut q r i C tg₁ bd₁ Zo X₁ (fun _ => Bd₂)) :
    ∃ Bd₂, P Bd₂ ∧ TRefOut q r i C tg bd Zo X (fun _ => Bd₁ + Bd₂) := by
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hT₁, hdeg₁, hpd₁⟩ := h
  set Ts := X.image tg with hTsdef
  have hTsZ : ∀ T ∈ Ts, Disjoint T Zo := by
    intro T hT; obtain ⟨x, -, rfl⟩ := mem_image.1 hT; exact htg x
  have hTsc : ∀ T ∈ Ts, T.card = i := by
    intro T hT; obtain ⟨x, hx, rfl⟩ := mem_image.1 hT; exact htgc x hx
  -- the residue as a tagged multigraph
  let Sb := {p : Finset (Fin n) × E₁ // p ∈ pairSet Ts Y₁}
  have hSb : ∀ p : Sb, p.1.1 ∈ Ts ∧ p.1.2 ∈ Y₁ p.1.1 := fun p => mem_pairSet.1 p.2
  let tg₁ : Sb → Finset (Fin n) := fun p => p.1.1
  let bd₁ : Sb → Finset (Fin n) := fun p => ends₁ p.1.1 p.1.2
  have h1 : ∀ p : Sb, Disjoint (tg₁ p) Zo := fun p => hTsZ _ (hSb p).1
  have h2 : ∀ p : Sb, bd₁ p ⊆ Z₁ := fun p => (hT₁ _ (hSb p).1).2.2.2.1 _ (hSb p).2
  have h3 : ∀ p ∈ (univ : Finset Sb), (tg₁ p).card = i := fun p _ => hTsc _ (hSb p).1
  have h4 : ∀ p ∈ (univ : Finset Sb), (bd₁ p).card = r - i := fun p _ =>
    (hT₁ _ (hSb p).1).2.1.rgraph _ (mem_union_right _ ((hT₁ _ (hSb p).1).2.2.1 (hSb p).2))
  have h5 : (univ : Finset Sb).image tg₁ ⊆ Ts := by
    intro T hT; obtain ⟨p, -, rfl⟩ := mem_image.1 hT; exact (hSb p).1
  have h6 : ∀ T e, mult bd₁ (fibre tg₁ univ T) e ≤ M := by
    intro T e
    by_cases hT : T ∈ Ts
    · refine le_trans ?_ ((hT₁ T hT).2.2.2.2.1 e)
      unfold mult fibre
      refine card_le_card_of_injOn (fun p => p.1.2) ?_ ?_
      · intro p hp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        obtain ⟨hpT, hpe⟩ := hp
        have hpT' : p.1.1 = T := hpT
        refine ⟨hpT' ▸ (hSb p).2, ?_⟩
        rw [← hpT']; exact hpe
      · intro p hp p' hp' hpp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp hp'
        have e1 : p.1.1 = p'.1.1 := hp.1.trans hp'.1.symm
        exact Subtype.ext (Prod.ext e1 hpp)
    · have : fibre tg₁ (univ : Finset Sb) T = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro p hp
        exact hT ((mem_fibre.1 hp).2 ▸ (hSb p).1)
      rw [this]; simp [mult]
  have h7 : ∀ S : Finset (Fin n), S.card = r - 1 →
      mdeg (liftEnds tg₁ bd₁) (univ : Finset Sb) S ≤ Bd₁ := by
    intro S hS
    refine le_trans ?_ ((sum_le_sum fun T hT => mdeg_mono _ ((hT₁ T hT).2.2.1) S).trans
      (hdeg₁ S hS))
    unfold mdeg
    rw [← card_sigma]
    refine card_le_card_of_injOn (fun p => ⟨p.1.1, p.1.2⟩) ?_ ?_
    · intro p hp
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hp
      simp only [mem_coe, mem_sigma, mem_filter]
      exact ⟨(hSb p).1, (hSb p).2, hp⟩
    · intro p _ p' _ hpp
      simp only [Sigma.mk.injEq] at hpp
      exact Subtype.ext (Prod.ext hpp.1 (eq_of_heq hpp.2))
  obtain ⟨Bd₂, hP, E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hT₂, hdeg₂, hpd₂⟩ :=
    hnext Sb tg₁ bd₁ univ h1 h2 h3 h4 h5 h6 h7
  set Ts₁ := (univ : Finset Sb).image tg₁ with hTs₁def
  -- relabelling of the copies of the stage
  let gT : Finset (Fin n) → E₁ → (Finset (Fin n) × E₁) ⊕ E₂ := fun T c =>
    if hc : T ∈ Ts ∧ c ∈ Y₁ T then Sum.inr (g₂ ⟨(T, c), mem_pairSet.2 hc⟩) else Sum.inl (T, c)
  let ends₃ : Finset (Fin n) → (Finset (Fin n) × E₁) ⊕ E₂ → Finset (Fin n) :=
    fun T => Sum.elim (fun p => ends₁ p.1 p.2) (ends₂ T)
  have hgT_ends : ∀ T c, ends₃ T (gT T c) = ends₁ T c := by
    intro T c
    by_cases hc : T ∈ Ts ∧ c ∈ Y₁ T
    · simp only [gT, ends₃, dif_pos hc, Sum.elim_inr]; exact hends₂ T _
    · simp only [gT, ends₃, dif_neg hc, Sum.elim_inl]
  have hgT_inj : ∀ T, Function.Injective (gT T) := by
    intro T c c' hcc
    by_cases hc : T ∈ Ts ∧ c ∈ Y₁ T <;> by_cases hc' : T ∈ Ts ∧ c' ∈ Y₁ T
    · dsimp only [gT] at hcc; rw [dif_pos hc, dif_pos hc'] at hcc
      exact congrArg (fun p : Sb => p.1.2) (hg₂ (Sum.inr_injective hcc))
    · dsimp only [gT] at hcc; rw [dif_pos hc, dif_neg hc'] at hcc
      exact absurd hcc Sum.inr_ne_inl
    · dsimp only [gT] at hcc; rw [dif_neg hc, dif_pos hc'] at hcc
      exact absurd hcc Sum.inl_ne_inr
    · dsimp only [gT] at hcc; rw [dif_neg hc, dif_neg hc'] at hcc
      exact (Prod.mk.inj (Sum.inl_injective hcc)).2
  have hgT_old : ∀ T x, tg x = T → gT T (g₁ x) = Sum.inl (tg x, g₁ x) := by
    intro T x hx
    have hc : ¬ (T ∈ Ts ∧ g₁ x ∈ Y₁ T) := by
      rintro ⟨hT, hY⟩
      exact (hT₁ T hT).1 _ ((hT₁ T hT).2.2.1 hY) x rfl
    simp only [gT, dif_neg hc, hx]
  refine ⟨Bd₂, hP, (Finset (Fin n) × E₁) ⊕ E₂, inferInstance, fun x => Sum.inl (tg x, g₁ x),
    ends₃, fun T => (R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅),
    fun T => (𝒲₁ T).image (image (gT T)) ∪
      (if T ∈ Ts₁ then (𝒲₂ T).image (image Sum.inr) else ∅),
    fun x y hxy => hg₁ (Prod.mk.inj (Sum.inl_injective hxy)).2,
    fun T c => by simp only [ends₃, Sum.elim_inl, hends₁], fun T hT => ?_, fun S hS => ?_,
    fun S hS => ?_⟩
  · obtain ⟨hR₁f, hres₁, hYR, hYZ, -, hR₁Zo⟩ := hT₁ T hT
    have hfib : ((fibre tg X T).image g₁).image (gT T) =
        (fibre tg X T).image fun x => Sum.inl (tg x, g₁ x) := by
      rw [image_image]
      exact image_congr fun x hx => hgT_old T x (mem_fibre.1 hx).2
    have hfresh : ∀ c ∈ (R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅),
        ∀ x, (Sum.inl (tg x, g₁ x) : (Finset (Fin n) × E₁) ⊕ E₂) ≠ c := by
      intro c hc x hx
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        by_cases hc' : T ∈ Ts ∧ c₁ ∈ Y₁ T
        · simp only [gT, dif_pos hc', reduceCtorEq] at hx
        · simp only [gT, dif_neg hc', Sum.inl.injEq, Prod.mk.injEq] at hx
          exact hR₁f c₁ hc₁ x hx.2
      · split_ifs at hc
        · obtain ⟨c₂, -, rfl⟩ := mem_image.1 hc
          exact Sum.inl_ne_inr hx
        · simp at hc
    have hZo : ∀ c ∈ (R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅),
        ends₃ T c ⊆ Zo := by
      intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rw [hgT_ends]; exact hR₁Zo c₁ hc₁
      · split_ifs at hc
        · obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 hc
          obtain ⟨-, -, hR₂Z⟩ := hT₂ T (by assumption)
          exact hR₂Z c₂ hc₂
        · simp at hc
    by_cases hT' : T ∈ Ts₁
    · obtain ⟨hR₂f, hch₂, hR₂Z⟩ := hT₂ T hT'
      have hrel := hch₂.relabel Sum.inr (ends₃ T) (fun c _ => rfl) Sum.inr_injective
      have hYimg : ((fibre tg₁ univ T).image g₂).image Sum.inr = (Y₁ T).image (gT T) := by
        ext c
        simp only [mem_image, fibre, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨c₂, ⟨p, hp, rfl⟩, rfl⟩
          have hpT : p.1.1 = T := hp
          refine ⟨p.1.2, hpT ▸ (hSb p).2, ?_⟩
          have hc : T ∈ Ts ∧ p.1.2 ∈ Y₁ T := hpT ▸ hSb p
          simp only [gT, dif_pos hc]
          congr 2
          exact Subtype.ext (Prod.ext hpT.symm rfl)
        · rintro ⟨c₁, hc₁, rfl⟩
          have hc : T ∈ Ts ∧ c₁ ∈ Y₁ T := ⟨hT, hc₁⟩
          refine ⟨g₂ ⟨(T, c₁), mem_pairSet.2 hc⟩, ⟨⟨(T, c₁), mem_pairSet.2 hc⟩, rfl, rfl⟩, ?_⟩
          simp only [gT, dif_pos hc]
      rw [hYimg, image_empty] at hrel
      have hpre := IsChainRefiner.prepend_relabel hres₁ hYR hC (gT T) (hgT_inj T)
        (hgT_ends T) hrel (fun c hc x hx => by
          obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 hc
          by_cases hx' : T ∈ Ts ∧ x ∈ Y₁ T
          · simp only [gT, dif_pos hx', Sum.inr.injEq] at hx
            exact hR₂f c₂ hc₂ _ hx
          · simp only [gT, dif_neg hx', reduceCtorEq] at hx)
      rw [hfib] at hpre
      simp only [if_pos hT']
      simp only [if_pos hT'] at hfresh hZo
      exact ⟨hfresh, hpre, hZo⟩
    · have hY0 : Y₁ T = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro c hc
        exact hT' (mem_image.2 ⟨⟨(T, c), mem_pairSet.2 ⟨hT, hc⟩⟩, mem_univ _, rfl⟩)
      have hch := (IsChainRefiner.ofResidual hres₁ hYR).mono' hC hC hC
      rw [hY0] at hch
      have hrel := hch.relabel (gT T) (ends₃ T) (fun c _ => hgT_ends T c) (hgT_inj T)
      rw [hfib, image_empty] at hrel
      simp only [if_neg hT', union_empty]
      simp only [if_neg hT', union_empty] at hfresh hZo
      exact ⟨hfresh, hrel, hZo⟩
  · -- lifted degrees
    have hsplit : ∀ T ∈ Ts, mdeg (fun c => T ∪ ends₃ T c)
        ((R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅)) S ≤
        mdeg (fun c => T ∪ ends₁ T c) (R₁ T) S +
          (if T ∈ Ts₁ then mdeg (fun c => T ∪ ends₂ T c) (R₂ T) S else 0) := by
      intro T _
      refine (RefinedAbsorption.Dense.mdeg_union_le _ _ _ S).trans
        (Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_))
      · exact mdeg_image_eq (A := R₁ T) (ends := fun c => T ∪ ends₁ T c)
          (ends' := fun c => T ∪ ends₃ T c) (g := gT T)
          (fun c _ => by simp only [hgT_ends]) (hgT_inj T).injOn subset_rfl S
      · split_ifs
        · exact mdeg_image_eq (A := R₂ T) (ends := fun c => T ∪ ends₂ T c)
            (ends' := fun c => T ∪ ends₃ T c) (g := Sum.inr) (fun c _ => rfl)
            Sum.inr_injective.injOn subset_rfl S
        · simp [mdeg]
    refine (sum_le_sum hsplit).trans ?_
    rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 h5]
    exact Nat.add_le_add (hdeg₁ S hS) (hdeg₂ S hS)
  · -- lifted piece degrees
    have hsplit : ∀ T ∈ Ts, pdeg (fun c => T ∪ ends₃ T c)
        ((𝒲₁ T).image (image (gT T)) ∪
          (if T ∈ Ts₁ then (𝒲₂ T).image (image Sum.inr) else ∅)) S ≤
        pdeg (fun c => T ∪ ends₁ T c) (𝒲₁ T) S +
          (if T ∈ Ts₁ then pdeg (fun c => T ∪ ends₂ T c) (𝒲₂ T) S else 0) := by
      intro T _
      refine (pdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ ?_)
      · exact pdeg_image_le (gT T) (fun c => by simp only [hgT_ends]) _ S
      · split_ifs
        · exact pdeg_image_le Sum.inr (fun c => rfl) _ S
        · simp [pdeg]
    refine (sum_le_sum hsplit).trans ?_
    rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 h5]
    exact Nat.add_le_add (hpd₁ S hS) (hpd₂ S hS)

end RefinedAbsorption.LinkSpread
