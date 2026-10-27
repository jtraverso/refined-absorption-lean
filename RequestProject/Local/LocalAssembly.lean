module
public import RequestProject.Local.Prepend

/-!
# Complete tagged refiners from independent local refiners

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1 (the union of the
local refiners of all outside parts `S`).  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

**`trefOut_of_local`**: if every tag `T` of a tagged multigraph has its own complete multi-refiner
of its fibre (over its own type of labels `E' T`), with new copies in `Z`, and the lifted degrees
and lifted piece degrees of these local refiners add up to at most `Bd`, then they form complete
tagged refiners in the sense of `TRefOut` (all labels are collected in `E₁ ⊕ Σ T, E' T`).
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

section Local

variable {n : ℕ} {E₁ : Type} [DecidableEq E₁] {tg bd : E₁ → Finset (Fin n)} {X : Finset E₁}

open Classical in
/-- Relabelling of the local labels of the tag `T`: old copies go back to `E₁`. -/
noncomputable def locLab (E' : X.image tg → Type) (g : ∀ T, E₁ → E' T) (T : X.image tg)
    (y : E' T) : E₁ ⊕ (Σ T, E' T) :=
  if h : ∃ c, g T c = y then Sum.inl h.choose else Sum.inr ⟨T, y⟩

omit [DecidableEq E₁] in
theorem locLab_g (E' : X.image tg → Type) (g : ∀ T, E₁ → E' T) (T : X.image tg)
    (hg : Function.Injective (g T)) (c : E₁) : locLab E' g T (g T c) = Sum.inl c := by
  have h : ∃ c', g T c' = g T c := ⟨c, rfl⟩
  unfold locLab
  rw [dif_pos h]
  exact congrArg Sum.inl (hg h.choose_spec)

omit [DecidableEq E₁] in
theorem locLab_new (E' : X.image tg → Type) (g : ∀ T, E₁ → E' T) (T : X.image tg) {y : E' T}
    (hy : ∀ c, g T c ≠ y) : locLab E' g T y = Sum.inr ⟨T, y⟩ := by
  unfold locLab
  rw [dif_neg (fun ⟨c, hc⟩ => hy c hc)]

omit [DecidableEq E₁] in
theorem locLab_injective (E' : X.image tg → Type) (g : ∀ T, E₁ → E' T) (T : X.image tg) :
    Function.Injective (locLab E' g T) := by
  intro y y' h
  unfold locLab at h
  by_cases h1 : ∃ c, g T c = y <;> by_cases h2 : ∃ c, g T c = y'
  · rw [dif_pos h1, dif_pos h2] at h
    rw [← h1.choose_spec, ← h2.choose_spec, Sum.inl_injective h]
  · rw [dif_pos h1, dif_neg h2] at h; exact absurd h Sum.inl_ne_inr
  · rw [dif_neg h1, dif_pos h2] at h; exact absurd h Sum.inr_ne_inl
  · rw [dif_neg h1, dif_neg h2] at h
    have := Sum.inr_injective h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    exact this

/-- **Complete tagged refiners from local refiners.** -/
theorem trefOut_of_local {q r i C Bd : ℕ} {Z : Finset (Fin n)}
    (E' : X.image tg → Type) [∀ T, DecidableEq (E' T)] (g : ∀ T, E₁ → E' T)
    (ends' : ∀ T, E' T → Finset (Fin n)) (R : ∀ T, Finset (E' T))
    (𝒲 : ∀ T, Finset (Finset (E' T)))
    (hg : ∀ T, Function.Injective (g T))
    (hends : ∀ T, ∀ c ∈ fibre tg X T.1, ends' T (g T c) = bd c)
    (hfresh : ∀ T, ∀ y ∈ R T, ∀ c, g T c ≠ y)
    (href : ∀ T, IsMultiRefiner (q - i) (r - i) C (ends' T) ((fibre tg X T.1).image (g T)) (R T)
      (𝒲 T))
    (hZ : ∀ T, ∀ y ∈ R T, ends' T y ⊆ Z)
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T, mdeg (fun y => T.1 ∪ ends' T y) (R T) S ≤ Bd)
    (hpdeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T, pdeg (fun y => T.1 ∪ ends' T y) (𝒲 T) S ≤ Bd) :
    TRefOut q r i C tg bd Z X (fun _ => Bd) := by
  classical
  let Es := E₁ ⊕ (Σ T, E' T)
  let endsS : Finset (Fin n) → Es → Finset (Fin n) := fun _ => Sum.elim bd fun p => ends' p.1 p.2
  let RS : Finset (Fin n) → Finset Es := fun T' =>
    if h : T' ∈ X.image tg then (R ⟨T', h⟩).image (locLab E' g ⟨T', h⟩) else ∅
  let 𝒲S : Finset (Fin n) → Finset (Finset Es) := fun T' =>
    if h : T' ∈ X.image tg then (𝒲 ⟨T', h⟩).image (image (locLab E' g ⟨T', h⟩)) else ∅
  -- the ends are compatible with the relabelling
  have hcompat : ∀ T : X.image tg, ∀ y ∈ (fibre tg X T.1).image (g T) ∪ R T,
      endsS T.1 (locLab E' g T y) = ends' T y := by
    intro T y hy
    rcases mem_union.1 hy with hy | hy
    · obtain ⟨c, hc, rfl⟩ := mem_image.1 hy
      rw [locLab_g E' g T (hg T)]
      exact (hends T c hc).symm
    · rw [locLab_new E' g T (fun c hc => hfresh T y hy c hc)]
      rfl
  have hRimg : ∀ T : X.image tg, (R T).image (locLab E' g T) = (R T).image fun y => Sum.inr ⟨T, y⟩ :=
    fun T => image_congr fun y hy => locLab_new E' g T (fun c hc => hfresh T y hy c hc)
  have hXimg : ∀ T : X.image tg, ((fibre tg X T.1).image (g T)).image (locLab E' g T) =
      (fibre tg X T.1).image Sum.inl := by
    intro T
    rw [image_image]
    exact image_congr fun c _ => locLab_g E' g T (hg T) c
  have hRS : ∀ T : X.image tg, RS T.1 = (R T).image (locLab E' g T) := fun T => by
    simp only [RS, dif_pos T.2]
  have h𝒲S : ∀ T : X.image tg, 𝒲S T.1 = (𝒲 T).image (image (locLab E' g T)) := fun T => by
    simp only [𝒲S, dif_pos T.2]
  refine ⟨Es, inferInstance, Sum.inl, endsS, RS, 𝒲S, Sum.inl_injective, fun T c => rfl,
    fun T' hT' => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · set T : X.image tg := ⟨T', hT'⟩
    have hrel := residual_relabel (href T) (locLab E' g T) (endsS T') (hcompat T)
      (locLab_injective E' g T).injOn (empty_subset _)
    rw [image_empty, hXimg T] at hrel
    rw [show RS T' = (R T).image (locLab E' g T) from hRS T,
      show 𝒲S T' = (𝒲 T).image (image (locLab E' g T)) from h𝒲S T]
    refine ⟨fun c hc x hx => ?_, IsChainRefiner.ofResidual hrel (empty_subset _), fun c hc => ?_⟩
    · rw [hRimg T] at hc
      obtain ⟨y, -, rfl⟩ := mem_image.1 hc
      exact Sum.inl_ne_inr hx
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
      rw [hcompat T y (mem_union_right _ hy)]
      exact hZ T y hy
  · rw [← sum_coe_sort (X.image tg)]
    refine le_trans (le_of_eq (sum_congr rfl fun T _ => ?_)) (hdeg S hS)
    rw [hRS T]
    exact mdeg_image_eq (A := R T) (ends := fun y => T.1 ∪ ends' T y)
      (fun y hy => by rw [hcompat T y (mem_union_right _ hy)])
      (locLab_injective E' g T).injOn subset_rfl S
  · rw [← sum_coe_sort (X.image tg)]
    refine le_trans (sum_le_sum fun T _ => ?_) (hpdeg S hS)
    rw [h𝒲S T]
    refine pdeg_image_le_of_mem (locLab E' g T) (𝒲 T) (fun W hW y hy => ?_) S
    rw [hcompat T y ((href T).subset W hW hy)]

end Local

end RefinedAbsorption.LinkSpread
