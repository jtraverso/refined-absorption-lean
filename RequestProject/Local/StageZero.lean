module
public import RequestProject.LinkSpread.Stage

/-!
# Tagged stages without additive term

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, §4).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

The tagged constructions of `LinkSpread/` (`taggedStep_of_levelE`, `taggedChainE`,
`taggedStage`) are stated for link levels in `ε`-form and produce budgets
`C_s · D + B · |Z| / 2^s`.  When the higher link levels hold *without* additive term
(`PlacedLinkLevel`, e.g. the last level `placedLinkLevel_last`), the same constructions give
budgets `C · D` with no additive term at all:

* `taggedStep_of_level`, `taggedChain0`: the flat steps and their chaining;
* **`taggedStage0`**: one tagged stage (round, flat steps, multiplicity reduction) into a
  sub-reserve `Z`, with lifted degrees `≤ Cst · D`.

For `r = 3` and `i = 1` the only higher level is the last one, so `taggedStage0` is unconditional
there.  This is the first half of the link refiners at level `1` with a sublinear additive term:
it moves all link graphs at once into a common half of the reserve, at cost `O(D)`.
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread

/-- **One flat step for all fibres at once, from a link level without additive term.** -/
theorem taggedStep_of_level {q r i j : ℕ} (hj : 1 ≤ j) (hijr : i + j < r) (hrq : r < q)
    (hL : PlacedLinkLevel q r (i + j)) (K : ℕ) :
    ∃ Cr Cs C : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (tg bd : E → Finset (Fin n)) (Zo Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) → IsFlat j Z bd X →
      (∀ x ∈ X, liftEnds tg bd x ⊆ U) → U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D →
      Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      ∃ Bd : ℕ, Bd ≤ C * D ∧ TaggedOutE q r i (j - 1) Cr tg bd Zo Z X Bd := by
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := hL K
  obtain ⟨Cs₀, Cs', -, hflat⟩ := taggedFlatStep q r i j Cl hj hijr hrq
  refine ⟨flatConst (q - i) (r - i) Cl, Ch + Cs₀, Cg + Cs' * Cd, ?_⟩
  intro n E _ tg bd Zo Z U X D hZ htg hbd htgc hbdc hX hU hUK hZq hD1 hCD hdeg
  obtain ⟨N, _, endsN, RN, 𝒲, hLR, hdens, hdegL⟩ :=
    hlev n (liftEnds tg bd) Z U X D (liftEnds_rgraph (by omega) htg hbd htgc hbdc)
      (liftEnds_flat hZ htg htgc hX) hU hUK hZq hD1 (le_trans (by omega) hCD) hdeg
  obtain ⟨R, Y, 𝒲', hfib, hdegR, hpdR⟩ := hflat n tg bd Zo Z endsN X RN 𝒲 (Cd * D) hZ htg hbd
    htgc hbdc hX hLR hZq (le_trans (by omega) hCD) hdens
  refine ⟨Cg * D + Cs' * (Cd * D), by nlinarith, E ⊕ FLab (Fin n) E N, inferInstance,
    Sum.inl, fun T => fEnds bd (fun T₂ => endsN (T ∪ T₂)), R, Y, 𝒲', Sum.inl_injective,
    fun T c => rfl, fun T hT => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · obtain ⟨h1, h2, -, h4, h5, h6⟩ := hfib T hT
    exact ⟨fun c hc x hx => h5 c hc x hx.symm, h1, h2, h4, h6⟩
  · exact (hdegR S hS).trans (Nat.add_le_add_right (hdegL S hS) _)
  · exact (hpdR S hS).trans (Nat.le_add_left _ _)

/-- **Chaining the flat steps of all link graphs at once, without additive term.** -/
theorem taggedChain0 {q r i : ℕ} (hrq : r < q)
    (hL : ∀ j, 1 ≤ j → i + j < r → PlacedLinkLevel q r (i + j)) :
    ∀ j, i + j < r → ∀ K : ℕ, ∃ Cr Cs C : ℕ, ∀ (n : ℕ) {E : Type}
      [DecidableEq E] (tg bd : E → Finset (Fin n)) (Zo Z U : Finset (Fin n)) (X : Finset E)
      (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) → IsFlat j Z bd X →
      Zo ⊆ U → (∀ x ∈ X, liftEnds tg bd x ⊆ U) → U.card ≤ K * Z.card → q + r ≤ Z.card →
      1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      ∃ Bd : ℕ, Bd ≤ C * D ∧ TaggedOutE q r i 0 Cr tg bd Zo Z X Bd := by
  intro j
  induction j with
  | zero =>
    intro _ K
    refine ⟨1, 0, 0, ?_⟩
    intro n E _ tg bd Zo Z U X D _ _ _ _ hbdc hX _ _ _ _ _ _ _
    refine ⟨0, by simp, E, inferInstance, id, fun _ => bd, fun _ => ∅, fun T => fibre tg X T,
      fun _ => ∅, Function.injective_id, fun T c => rfl, fun T _ => ?_, fun S _ => by simp [mdeg],
      fun S _ => by simp [pdeg]⟩
    rw [image_id]
    refine ⟨by simp, isResidualMultiRefiner_self 1 fun x hx => hbdc x (fibre_subset _ _ _ hx),
      fun x hx => hX x (fibre_subset _ _ _ hx), by simp, by simp⟩
  | succ j ih =>
    intro hj K
    obtain ⟨Cr₁, Cs₁, C₁, hstep⟩ := taggedStep_of_level (j := j + 1) (by omega) hj hrq
      (hL (j + 1) (by omega) hj) K
    obtain ⟨Cr₂, Cs₂, C₂, hrest⟩ := ih (by omega) K
    refine ⟨Cr₁ + Cr₂, Cs₁ + Cs₂, C₁ + C₂ * (1 + C₁), ?_⟩
    intro n E _ tg bd Zo Z U X D hZ htg hbd htgc hbdc hX hZoU hU hUK hZq hD1 hCD hdeg
    obtain ⟨Bd₁, hBd₁, hout₁⟩ :=
      hstep n tg bd Zo Z U X D hZ htg hbd htgc hbdc hX hU hUK hZq hD1 (le_trans (by omega) hCD)
        hdeg
    rw [Nat.add_sub_cancel] at hout₁
    obtain ⟨Bd₂, hBd₂, hout⟩ := hout₁.comp (fun Bd₂ => Bd₂ ≤ C₂ * (D + Bd₁))
      (fun E₁ _ tg₁ bd₁ X₁ h1 h2 h3 h4 h5 h6 h7 => hrest n tg₁ bd₁ Zo Z U X₁ (D + Bd₁) hZ h1 h2
        h3 h4 h5 hZoU h6 hUK hZq (by omega) (le_trans (by omega) hCD) h7)
      htg hbd htgc hZoU hU hdeg
    refine ⟨Bd₁ + Bd₂, ?_, hout⟩
    have : C₂ * (D + Bd₁) ≤ C₂ * (D + C₁ * D) := Nat.mul_le_mul_left _ (by omega)
    nlinarith

set_option maxHeartbeats 4000000 in
/-- **One stage for all link graphs at once, without additive term**, from link levels without
additive term (`PlacedLinkLevel`) at the higher levels. -/
theorem taggedStage0 {q r i : ℕ} (hir : i + 1 < r) (hrq : r < q)
    (hL : ∀ j, 1 ≤ j → i + j < r → PlacedLinkLevel q r (i + j)) (K : ℕ) :
    ∃ Cr M Cs Cst : ℕ, 1 ≤ M ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (tg bd : E → Finset (Fin n)) (Zo Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) →
      Zo ⊆ U → (∀ x ∈ X, liftEnds tg bd x ⊆ U) → U.card ≤ K * Z.card → q + r ≤ Z.card →
      1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      ∃ Bd : ℕ, Bd ≤ Cst * D ∧ TStageOut q r i Cr M tg bd Zo Z X Bd := by
  obtain ⟨C₀, hC₀, hround⟩ := taggedRoundOut q r i hir hrq
  obtain ⟨Cr₂, Cs₂, C₂, hchain'⟩ := taggedChain0 hrq hL (r - i - 1) (by omega) K
  obtain ⟨M, Cm, hM, hmr⟩ := multRed_explicit (q - i) (r - i) (by omega)
  set A' := (M + 2) ^ 2 + Cm * (1 + (M + 2) ^ 2) with hA'
  set κ := (K + 1) ^ (r - 1) with hκ
  refine ⟨C₀ + Cr₂ + Cm, M, C₀ + Cs₂, (1 + A') * (C₀ * κ + C₂ * (1 + C₀ * κ)) + A', hM, ?_⟩
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
    (fun Bd₂ => Bd₂ ≤ C₂ * (D + C₀ * (κ * D)))
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
    have e3 : C₂ * (D + C₀ * (κ * D)) = (C₂ * (1 + C₀ * κ)) * D := by ring
    rw [e3] at hBd₂
    have h4 : Bdc ≤ (C₀ * κ + C₂ * (1 + C₀ * κ)) * D := by
      rw [hBdc]
      have : (C₀ * κ + C₂ * (1 + C₀ * κ)) * D = C₀ * (κ * D) + (C₂ * (1 + C₀ * κ)) * D := by ring
      omega
    have h5 := Nat.mul_le_mul_left (1 + A') h4
    have e1 : Bdc + A' * (D + Bdc) = (1 + A') * Bdc + A' * D := by ring
    have e4 : ((1 + A') * (C₀ * κ + C₂ * (1 + C₀ * κ)) + A') * D =
        (1 + A') * ((C₀ * κ + C₂ * (1 + C₀ * κ)) * D) + A' * D := by ring
    rw [e1, e4]
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


end RefinedAbsorption.Local
