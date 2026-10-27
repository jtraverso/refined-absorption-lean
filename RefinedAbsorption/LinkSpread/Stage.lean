module
public import RefinedAbsorption.LinkSpread.RoundOut
public import RefinedAbsorption.FlatDown.MultDegree
public import RefinedAbsorption.Dense.Stage

/-!
# One stage for all link graphs at once

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

The analogue of `multiStageE` for tagged multigraphs: the tagged anti-edge round into a reserve
`Z ⊆ Zo` (`taggedRoundOut`), the tagged chain of flat steps (`taggedChainE`) and multiplicity
reduction in every fibre.  The output (`TStageOut`) consists, for every tag `T`, of a residual
refiner of the fibre of `T` whose residue consists of new copies inside `Z` with multiplicity
`≤ M` in that fibre; the lifted new copies and pieces have `(r-1)`-degrees `≤ Bd`, summed over the
tags, with `2^s · Bd ≤ 2^s · Cst · D + B · |Z|` (**`taggedStage`**).
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- Multiplicity reduction with explicit labels (`MLab V`) and explicit new copies. -/
theorem multRed_explicit (q r : ℕ) (hrq : r ≤ q) :
    ∃ M Cm : ℕ, 1 ≤ M ∧ ∀ {V E : Type} [DecidableEq V] [DecidableEq E]
      (ends : E → Finset V) (X : Finset E), MIsRGraph r ends X →
      (∀ y ∈ mR ends X M, y.1 ∈ X.image ends) ∧ mY ends X M ⊆ (mR ends X M).image Sum.inr ∧
      IsResidualMultiRefiner q r Cm (Sum.elim ends Prod.fst) (X.image Sum.inl)
        ((mR ends X M).image Sum.inr) (mY ends X M) (mW ends X M) ∧
      (∀ e, mult (Sum.elim ends Prod.fst) (mY ends X M) e ≤ M) ∧
      (∀ S, mdeg (Sum.elim ends Prod.fst) ((mR ends X M).image Sum.inr) S ≤
        (M + 2) ^ 2 * mdeg ends X S) ∧
      (∀ W ∈ mW ends X M, ∀ c ∈ W, W.biUnion (Sum.elim ends Prod.fst) ⊆
        Sum.elim ends Prod.fst c) := by
  set M := fakeModulus q r with hMdef
  have hM : 1 ≤ M := fakeModulus_pos hrq
  have hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M := fun s hs => dvd_fakeModulus hs
  refine ⟨M, 5 * M + 1, hM, ?_⟩
  intro V E _ _ ends X hX
  exact ⟨fun y hy => mR_ends hy, mY_subset_mR, multReduction hM hdvd hX, fun e => mult_mY_le e,
    fun S => mdeg_mR_le S, fun W hW => mW_parallel hW⟩

/-- Output of one tagged stage (see the module docstring). -/
def TStageOut (q r i C M : ℕ) {n : ℕ} {E : Type} (tg bd : E → Finset (Fin n))
    (Zo Z : Finset (Fin n)) (X : Finset E) (Bd : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : Finset (Fin n) → E' → Finset (Fin n))
    (R Y : Finset (Fin n) → Finset E') (𝒲 : Finset (Fin n) → Finset (Finset E')),
    Function.Injective g ∧ (∀ T c, ends' T (g c) = bd c) ∧
    (∀ T ∈ X.image tg, (∀ c ∈ R T, ∀ x, g x ≠ c) ∧
      IsResidualMultiRefiner (q - i) (r - i) C (ends' T) ((fibre tg X T).image g) (R T) (Y T)
        (𝒲 T) ∧
      Y T ⊆ R T ∧ (∀ c ∈ Y T, ends' T c ⊆ Z) ∧ (∀ e, mult (ends' T) (Y T) e ≤ M) ∧
      ∀ c ∈ R T, ends' T c ⊆ Zo) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, mdeg (fun c => T ∪ ends' T c) (R T) S ≤ Bd) ∧
    ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, pdeg (fun c => T ∪ ends' T c) (𝒲 T) S ≤ Bd

set_option maxHeartbeats 4000000 in
/-- **One stage for all link graphs at once.** -/
theorem taggedStage {q r i : ℕ} (hir : i + 1 < r) (hrq : r < q)
    (hL : ∀ j, 1 ≤ j → i + j < r → PlacedLinkLevelE q r (i + j)) (K : ℕ) :
    ∃ Cr B M : ℕ, 1 ≤ M ∧ ∀ s : ℕ, ∃ Cs Cst : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (tg bd : E → Finset (Fin n)) (Zo Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) →
      Zo ⊆ U → (∀ x ∈ X, liftEnds tg bd x ⊆ U) → U.card ≤ K * Z.card → q + r ≤ Z.card →
      1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      ∃ Bd : ℕ, 2 ^ s * Bd ≤ 2 ^ s * Cst * D + B * Z.card ∧
        TStageOut q r i Cr M tg bd Zo Z X Bd := by
  obtain ⟨C₀, hC₀, hround⟩ := taggedRoundOut q r i hir hrq
  obtain ⟨Cr₂, B₂, hchain⟩ := taggedChainE hrq hL (r - i - 1) (by omega) K
  obtain ⟨M, Cm, hM, hmr⟩ := multRed_explicit (q - i) (r - i) (by omega)
  set A' := (M + 2) ^ 2 + Cm * (1 + (M + 2) ^ 2) with hA'
  refine ⟨C₀ + Cr₂ + Cm, (1 + A') * B₂, M, hM, fun s => ?_⟩
  obtain ⟨Cs₂, C₂, hchain'⟩ := hchain s
  set κ := (K + 1) ^ (r - 1) with hκ
  refine ⟨C₀ + Cs₂, (1 + A') * (C₀ * κ + C₂ * (1 + C₀ * κ)) + A', ?_⟩
  intro n E _ tg bd Zo Z U X D hZ htg hbd htgc hbdc hZoU hXU hUK hZq hD1 hCs hdeg
  -- root density
  have hXr : MIsRGraph r (liftEnds tg bd) X := liftEnds_rgraph (by omega) htg hbd htgc hbdc
  have hXJ : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      mdeg (liftEnds tg bd) X J ≤ (κ * D) * Z.card ^ (r - 1 - J.card) := by
    intro J hJ
    refine (mdeg_le_pow hXr hXU hdeg hJ).trans ?_
    calc D * U.card ^ (r - 1 - J.card) ≤ D * ((K + 1) * Z.card) ^ (r - 1 - J.card) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) _)
      _ = D * ((K + 1) ^ (r - 1 - J.card) * Z.card ^ (r - 1 - J.card)) := by rw [mul_pow]
      _ ≤ D * (κ * Z.card ^ (r - 1 - J.card)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by omega) (by omega)))
      _ = κ * D * Z.card ^ (r - 1 - J.card) := by ring
  have hround' := hround n tg bd Zo Z X (κ * D) hZ htg hbd htgc hbdc (by omega) hXJ
  obtain ⟨Bd₂, hBd₂, hout⟩ := hround'.comp
    (fun Bd₂ => 2 ^ s * Bd₂ ≤ 2 ^ s * C₂ * (D + C₀ * (κ * D)) + B₂ * Z.card)
    (fun E₁ _ tg₁ bd₁ X₁ h1 h2 h3 h4 h5 h6 h7 => hchain' n tg₁ bd₁ Zo Z U X₁
      (D + C₀ * (κ * D)) hZ h1 h2 h3 h4 h5 hZoU h6 hUK hZq (by omega) (le_trans (by omega) hCs)
      h7)
    htg hbd htgc hZoU hXU hdeg
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hT₁, hdeg₁, hpd₁⟩ := hout
  set Bdc := C₀ * (κ * D) + Bd₂ with hBdc
  set Ts := X.image tg with hTs
  have hY₁sub : ∀ T ∈ Ts, Y₁ T ⊆ (fibre tg X T).image g₁ ∪ R₁ T :=
    fun T hT => (hT₁ T hT).2.2.2.1
  have hY₁r : ∀ T ∈ Ts, MIsRGraph (r - i) (ends₁ T) (Y₁ T) :=
    fun T hT c hc => (hT₁ T hT).2.1.rgraph c (hY₁sub T hT hc)
  have hTcard : ∀ T ∈ Ts, T.card = i := by
    intro T hT; obtain ⟨x, hx, rfl⟩ := mem_image.1 hT; exact htgc x hx
  -- lifted degrees of the residues of the chain
  have hYdeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ Ts, mdeg (fun c => T ∪ ends₁ T c) (Y₁ T) S ≤ D + Bdc := by
    intro S hS
    calc ∑ T ∈ Ts, mdeg (fun c => T ∪ ends₁ T c) (Y₁ T) S
        ≤ ∑ T ∈ Ts, (mdeg (fun c => T ∪ bd c) (fibre tg X T) S +
            mdeg (fun c => T ∪ ends₁ T c) (R₁ T) S) := by
          refine sum_le_sum fun T hT => ?_
          refine (mdeg_mono _ (hY₁sub T hT) S).trans ((RefinedAbsorption.Dense.mdeg_union_le _ _ _ S).trans
            (Nat.add_le_add_right (le_of_eq ?_) _))
          exact mdeg_image_eq (A := fibre tg X T) (ends := fun c => T ∪ bd c)
            (fun c _ => by simp only [hends₁]) hg₁.injOn subset_rfl S
      _ ≤ D + Bdc := by
          rw [sum_add_distrib, ← mdeg_liftEnds_eq_sum]
          exact Nat.add_le_add (hdeg S hS) (hdeg₁ S hS)
  refine ⟨Bdc + A' * (D + Bdc), ?_, E₁ ⊕ MLab (Fin n), inferInstance,
    fun x => Sum.inl (g₁ x), fun T => Sum.elim (ends₁ T) Prod.fst,
    fun T => (R₁ T).image Sum.inl ∪ (mR (ends₁ T) (Y₁ T) M).image Sum.inr,
    fun T => mY (ends₁ T) (Y₁ T) M,
    fun T => (𝒲₁ T).image (image Sum.inl) ∪ mW (ends₁ T) (Y₁ T) M,
    fun x y hxy => hg₁ (Sum.inl_injective hxy), fun T c => by simp [hends₁], fun T hT => ?_,
    fun S hS => ?_, fun S hS => ?_⟩
  · -- the budget
    have e1 : 2 ^ s * (Bdc + A' * (D + Bdc)) = (1 + A') * (2 ^ s * Bdc) + A' * (2 ^ s * D) := by
      ring
    have e2 : 2 ^ s * Bdc = 2 ^ s * (C₀ * κ) * D + 2 ^ s * Bd₂ := by rw [hBdc]; ring
    have e3 : 2 ^ s * C₂ * (D + C₀ * (κ * D)) = 2 ^ s * (C₂ * (1 + C₀ * κ)) * D := by ring
    rw [e3] at hBd₂
    have h4 : 2 ^ s * Bdc ≤ 2 ^ s * (C₀ * κ + C₂ * (1 + C₀ * κ)) * D + B₂ * Z.card := by
      rw [e2]
      have : 2 ^ s * (C₀ * κ + C₂ * (1 + C₀ * κ)) * D =
          2 ^ s * (C₀ * κ) * D + 2 ^ s * (C₂ * (1 + C₀ * κ)) * D := by ring
      omega
    rw [e1]
    have h5 := Nat.mul_le_mul_left (1 + A') h4
    have e4 : 2 ^ s * ((1 + A') * (C₀ * κ + C₂ * (1 + C₀ * κ)) + A') * D + (1 + A') * B₂ * Z.card
        = (1 + A') * (2 ^ s * (C₀ * κ + C₂ * (1 + C₀ * κ)) * D + B₂ * Z.card) +
          A' * (2 ^ s * D) := by ring
    rw [e4]
    omega
  · obtain ⟨hR₁g, hres₁, hflat₁, hY₁, hR₁Zo⟩ := hT₁ T hT
    obtain ⟨hmends, hmYR, hmres, hmmult, -, -⟩ := hmr (ends₁ T) (Y₁ T) (hY₁r T hT)
    have hcomp := RefinedAbsorption.Dense.IsResidualMultiRefiner.compose (g := Sum.inl) Sum.inl_injective
      (ends₂ := Sum.elim (ends₁ T) Prod.fst) (fun c => rfl) hres₁ hY₁ hmres
      (fun c hc x hx => by obtain ⟨y, -, rfl⟩ := mem_image.1 hc; exact Sum.inl_ne_inr hx)
    rw [image_image] at hcomp
    have hYZ : ∀ c ∈ Y₁ T, ends₁ T c ⊆ Z := by
      intro c hc
      have := hflat₁ c hc
      rw [Nat.le_zero, card_eq_zero, sdiff_eq_empty_iff_subset] at this
      exact this
    have hXRZo : ∀ c ∈ (fibre tg X T).image g₁ ∪ R₁ T, ends₁ T c ⊆ Zo := by
      intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨x, -, rfl⟩ := mem_image.1 hc; rw [hends₁]; exact hbd x
      · exact hR₁Zo c hc
    refine ⟨?_, hcomp, hmYR.trans subset_union_right, ?_, hmmult, ?_⟩
    · intro c hc x hx
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hR₁g c₁ hc₁ x (Sum.inl_injective hx)
      · obtain ⟨y, -, rfl⟩ := mem_image.1 hc
        exact Sum.inl_ne_inr hx
    · intro c hc
      obtain ⟨y, hy, rfl⟩ := mem_image.1 (hmYR hc)
      obtain ⟨c', hc', he⟩ := mem_image.1 (hmends y hy)
      show y.1 ⊆ Z
      rw [← he]; exact hYZ c' hc'
    · intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hR₁Zo c₁ hc₁
      · obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
        obtain ⟨c', hc', he⟩ := mem_image.1 (hmends y hy)
        show y.1 ⊆ Zo
        rw [← he]; exact hXRZo c' (hY₁ hc')
  · -- lifted degrees of the new copies
    have hle : ∀ T ∈ Ts, mdeg (fun c => T ∪ Sum.elim (ends₁ T) Prod.fst c)
        ((R₁ T).image Sum.inl ∪ (mR (ends₁ T) (Y₁ T) M).image Sum.inr) S ≤
        mdeg (fun c => T ∪ ends₁ T c) (R₁ T) S +
          (M + 2) ^ 2 * mdeg (fun c => T ∪ ends₁ T c) (Y₁ T) S := by
      intro T hT
      refine (RefinedAbsorption.Dense.mdeg_union_le _ _ _ S).trans (Nat.add_le_add (le_of_eq ?_) ?_)
      · exact mdeg_image_eq (A := R₁ T) (ends := fun c => T ∪ ends₁ T c)
          (ends' := fun c => T ∪ Sum.elim (ends₁ T) Prod.fst c) (g := Sum.inl) (fun c _ => rfl)
          Sum.inl_injective.injOn subset_rfl S
      · rw [mdeg_lift, mdeg_lift]
        exact (hmr (ends₁ T) (Y₁ T) (hY₁r T hT)).2.2.2.2.1 _
    refine (sum_le_sum hle).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    have h1 := hdeg₁ S hS
    have h2 := Nat.mul_le_mul_left ((M + 2) ^ 2) (hYdeg S hS)
    have h3 : (M + 2) ^ 2 * (D + Bdc) ≤ A' * (D + Bdc) :=
      Nat.mul_le_mul_right _ (by rw [hA']; omega)
    omega
  · -- lifted piece degrees
    have hle : ∀ T ∈ Ts, pdeg (fun c => T ∪ Sum.elim (ends₁ T) Prod.fst c)
        ((𝒲₁ T).image (image Sum.inl) ∪ mW (ends₁ T) (Y₁ T) M) S ≤
        pdeg (fun c => T ∪ ends₁ T c) (𝒲₁ T) S +
          (Cm * (1 + (M + 2) ^ 2)) * mdeg (fun c => T ∪ ends₁ T c) (Y₁ T) S := by
      intro T hT
      obtain ⟨-, -, hmres, -, hmdeg, hmpar⟩ := hmr (ends₁ T) (Y₁ T) (hY₁r T hT)
      refine (pdeg_union_le _ _ _ S).trans (Nat.add_le_add
        (pdeg_image_le Sum.inl (fun c => rfl) _ S) ?_)
      have hne : (S \ T).Nonempty := by
        rw [← card_pos]
        have := card_le_card_sdiff_add_card (s := S) (t := T)
        rw [hTcard T hT] at this
        omega
      refine (pdeg_lift_le _ _ _ S).trans ((pdeg_le_of_parallel hmres hmpar hne).trans ?_)
      rw [mdeg_lift]
      have hu := RefinedAbsorption.Dense.mdeg_union_le (Sum.elim (ends₁ T) Prod.fst)
        ((Y₁ T).image Sum.inl) ((mR (ends₁ T) (Y₁ T) M).image Sum.inr) (S \ T)
      rw [mdeg_image_eq (A := Y₁ T) (ends := ends₁ T) (ends' := Sum.elim (ends₁ T) Prod.fst)
        (g := Sum.inl) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl] at hu
      have := hmdeg (S \ T)
      calc Cm * mdeg (Sum.elim (ends₁ T) Prod.fst)
            ((Y₁ T).image Sum.inl ∪ (mR (ends₁ T) (Y₁ T) M).image Sum.inr) (S \ T)
          ≤ Cm * ((1 + (M + 2) ^ 2) * mdeg (ends₁ T) (Y₁ T) (S \ T)) :=
            Nat.mul_le_mul_left _ (by nlinarith)
        _ = _ := by ring
    refine (sum_le_sum hle).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    have h1 := hpd₁ S hS
    have h2 := Nat.mul_le_mul_left (Cm * (1 + (M + 2) ^ 2)) (hYdeg S hS)
    have h3 : Cm * (1 + (M + 2) ^ 2) * (D + Bdc) ≤ A' * (D + Bdc) :=
      Nat.mul_le_mul_right _ (by rw [hA']; omega)
    omega

end RefinedAbsorption.LinkSpread
