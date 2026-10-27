module
public import RefinedAbsorption.SparseChain.StageS

/-!
# The refine-down stage with new copies meeting the reserve

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, flatness output of
Theorem 3.8).

The sparse refine-down stage (`Dense.multiStageS`) and its chain of flat levels
(`Placement.placedChainS`) are restated here with one more output: **every new copy meets the
reserve `Z`**.  The proofs are those of the original statements; the extra output comes from the
anti-edge round (`Gen.multiRound`: every new copy meets `Z`), from the flat steps (every new copy
lies in `T ∪ Z` for an outside part `T` of size `i < r`) and from the multiplicity reduction (new
copies are parallel to residue copies, which lie inside `Z`).

* `PlacedOutM`: `PlacedOut` together with "every new copy meets `Z`".
* `placedStep_of_levelS_M`, `placedChainS_M`, `multiStageS_M`.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense

/-- `PlacedOut` together with: every new copy meets the reserve `Z`. -/
def PlacedOutM (q r j C : ℕ) {n : ℕ} {E : Type} (ends : E → Finset (Fin n))
    (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
    (R Y : Finset E') (𝒲 : Finset (Finset E')),
    Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
    IsResidualMultiRefiner q r C ends' (X.image g) R Y 𝒲 ∧ IsFlat j Z ends' Y ∧
    Y ⊆ X.image g ∪ R ∧ (∀ c ∈ R, ends' c ⊆ U ∪ Z) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ C * D) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ C * D) ∧
    ∀ c ∈ R, (ends' c ∩ Z).Nonempty

/-- A set contained in `T ∪ Z` with more elements than `T` meets `Z`. -/
theorem inter_nonempty_of_subset_union {α : Type*} [DecidableEq α] {s T Z : Finset α}
    (h : s ⊆ T ∪ Z) (hc : T.card < s.card) : (s ∩ Z).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsT : s ⊆ T := by
    intro x hx
    rcases mem_union.1 (h hx) with h1 | h1
    · exact h1
    · have : x ∈ s ∩ Z := mem_inter.2 ⟨hx, h1⟩
      rw [hne] at this
      exact absurd this (notMem_empty x)
  exact absurd (card_le_card hsT) (by omega)

/-- **A degree-controlled flat step from a placed level.** -/
theorem placedStep_of_levelS_M {q r i : ℕ} {a : ℕ → ℕ} (hir : i < r) (hrq : r < q)
    (hL : PlacedLinkLevelS q r i a) (K : ℕ) :
    ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Cs * D ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      PlacedOutM q r (i - 1) C ends Z U X D := by
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := hL K
  obtain ⟨Cs₀, Cs', -, hflat⟩ := placedFlatStep_link q r i Cl hir hrq
  refine ⟨Ch + Cs₀ + 1, flatConst q r Cl + Cg + Cs' * Cd, by omega, ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCD hdeg
  have hCh : Ch * D ≤ Z.card := le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
  have hCs : Cs₀ ≤ Z.card :=
    le_trans (by omega) (le_trans (Nat.le_mul_of_pos_right _ hD1) hCD)
  obtain ⟨N, _, endsN, RN, 𝒲, hLR, hdens, hdegL⟩ :=
    hlev n ends Z U X D hXr hX hU hUK hZq hD1 haD hCh hdeg
  obtain ⟨R, Y, 𝒲', h1, h2, -, h4, h5, h6, h7, h8⟩ :=
    hflat n ends Z endsN X RN 𝒲 (Cd * D) hXr hX hLR hZq hCs hdens
  refine ⟨E ⊕ FLab (Fin n) E N, inferInstance, Sum.inl, fEnds ends endsN, R, Y, 𝒲',
    Sum.inl_injective, fun c => rfl, fun c hc x hx => h5 c hc x hx.symm,
    h1.mono (by omega), h2, h4, fun c hc => ?_, fun S hS => ?_, fun S hS => ?_, fun c hc => ?_⟩
  · obtain ⟨T, hT, hcT⟩ := h6 c hc
    exact hcT.trans (union_subset_union (outParts_subset hU hT) subset_rfl)
  · refine (h7 S hS).trans ?_
    have := hdegL S hS
    calc _ ≤ Cg * D + Cs' * (Cd * D) := Nat.add_le_add_right this _
      _ ≤ (flatConst q r Cl + Cg + Cs' * Cd) * D := by nlinarith
  · refine (h8 S hS).trans ?_
    calc Cs' * (Cd * D) = (Cs' * Cd) * D := by ring
      _ ≤ (flatConst q r Cl + Cg + Cs' * Cd) * D := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  · obtain ⟨T, hT, hcT⟩ := h6 c hc
    have hTc := (outParts_card hT).1
    have hcr : (fEnds ends endsN c).card = r := h1.rgraph c (mem_union_right _ hc)
    exact inter_nonempty_of_subset_union hcT (by omega)

/-- **Chaining the levels** `j, j - 1, …, 1`, given placed link refiners at each of them. -/
theorem placedChainS_M {q r : ℕ} {a : ℕ → ℕ} (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelS q r i a) :
    ∀ j, j < r → ∀ K : ℕ, ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat j Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Cs * D ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      PlacedOutM q r 0 C ends Z U X D := by
  intro j
  induction j with
  | zero =>
    intro _ K
    refine ⟨1, 1, one_pos, ?_⟩
    intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 _ hCD hdeg
    refine ⟨E, inferInstance, id, ends, ∅, X, ∅, Function.injective_id, fun c => rfl,
      by simp, ?_, hX, by simp, by simp, fun S _ => by simp [mdeg], fun S _ => by simp [pdeg],
      by simp⟩
    rw [image_id]
    exact isResidualMultiRefiner_self 1 hXr
  | succ j ih =>
    intro hj K
    obtain ⟨Cs₁, C₁, hCs₁, hstep⟩ :=
      placedStep_of_levelS_M hj hrq (hL (j + 1) (by omega) hj) K
    obtain ⟨Cs₂, C₂, -, hrest⟩ := ih (by omega) (K + 1)
    refine ⟨Cs₁ + Cs₂ * (1 + C₁), C₁ + C₂ + C₂ * (1 + C₁), by omega, ?_⟩
    intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCD hdeg
    have hCD₁ : Cs₁ * D ≤ Z.card := le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
    obtain ⟨E₁, _, g, ends₁, R₁, Y₁, 𝒲₁, hg, hends, hR₁, h₁, hflat₁, hY₁, hR₁U, hdeg₁, hpd₁,
      hmeet₁⟩ :=
      hstep n ends Z U X D hXr hX hU hUK hZq hD1 haD hCD₁ hdeg
    rw [Nat.add_sub_cancel] at hflat₁
    have hYr : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (hY₁ hc)
    have hYU : ∀ c ∈ Y₁, ends₁ c ⊆ U ∪ Z := by
      intro c hc
      rcases mem_union.1 (hY₁ hc) with hc | hc
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
        rw [hends]; exact (hU x hx).trans subset_union_left
      · exact hR₁U c hc
    have hUK' : (U ∪ Z).card ≤ (K + 1) * Z.card := by
      have := card_union_le U Z
      nlinarith
    have hD₁ : 1 ≤ (1 + C₁) * D := by nlinarith
    have hCD₂ : Cs₂ * ((1 + C₁) * D) ≤ Z.card := by
      rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
    have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ (1 + C₁) * D := by
      intro S hS
      calc mdeg ends₁ Y₁ S ≤ mdeg ends₁ (X.image g ∪ R₁) S := mdeg_mono _ hY₁ S
        _ ≤ mdeg ends₁ (X.image g) S + mdeg ends₁ R₁ S := by
          unfold mdeg; rw [filter_union]; exact card_union_le _ _
        _ ≤ D + C₁ * D := by
          rw [mdeg_image_eq (A := X) (fun c _ => hends c) hg.injOn subset_rfl]
          exact Nat.add_le_add (hdeg S hS) (hdeg₁ S hS)
        _ = (1 + C₁) * D := by ring
    obtain ⟨E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂, h₂, hflat₂, hY₂, hR₂U,
      hdeg₂, hpd₂, hmeet₂⟩ := hrest n ends₁ Z (U ∪ Z) Y₁ ((1 + C₁) * D) hYr hflat₁ hYU hUK' hZq hD₁
        (haD.trans (by nlinarith)) hCD₂ hdegY
    have h₁' := residual_relabel h₁ g₂ ends₂ (fun c _ => hends₂ c) hg₂.injOn hY₁
    have hcomp := h₁'.trans h₂ (by rw [← image_union]; exact image_subset_image hY₁) (by
      rw [disjoint_left]
      intro c hc hc'
      rw [← image_union] at hc'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hc'
      exact hR₂ _ hc x rfl)
    refine ⟨E₂, inferInstance, g₂ ∘ g, ends₂, R₁.image g₂ ∪ R₂, Y₂, 𝒲₁.image (image g₂) ∪ 𝒲₂,
      hg₂.comp hg, fun c => by simp [hends₂, hends], ?_, ?_, hflat₂, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc x hx
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hR₁ c₁ hc₁ x (hg₂ hx)
      · exact hR₂ c hc _ hx
    · rw [← image_image]
      exact hcomp.mono (by nlinarith)
    · intro c hc
      rcases mem_union.1 (hY₂ hc) with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rcases mem_union.1 (hY₁ hc₁) with h | h
        · obtain ⟨x, hx, rfl⟩ := mem_image.1 h
          exact mem_union_left _ (mem_image.2 ⟨x, hx, rfl⟩)
        · exact mem_union_right _ (mem_union_left _ (mem_image_of_mem _ h))
      · exact mem_union_right _ (mem_union_right _ hc)
    · intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rw [hends₂]; exact hR₁U c₁ hc₁
      · refine (hR₂U c hc).trans ?_
        rw [union_assoc, union_self]
    · intro S hS
      calc mdeg ends₂ (R₁.image g₂ ∪ R₂) S ≤ mdeg ends₂ (R₁.image g₂) S + mdeg ends₂ R₂ S := by
            unfold mdeg; rw [filter_union]; exact card_union_le _ _
        _ ≤ C₁ * D + C₂ * ((1 + C₁) * D) := by
          rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
          exact Nat.add_le_add (hdeg₁ S hS) (hdeg₂ S hS)
        _ ≤ (C₁ + C₂ + C₂ * (1 + C₁)) * D := by nlinarith
    · intro S hS
      calc pdeg ends₂ (𝒲₁.image (image g₂) ∪ 𝒲₂) S
          ≤ pdeg ends₂ (𝒲₁.image (image g₂)) S + pdeg ends₂ 𝒲₂ S := pdeg_union_le _ _ _ _
        _ ≤ C₁ * D + C₂ * ((1 + C₁) * D) :=
          Nat.add_le_add ((pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)) (hpd₂ S hS)
        _ ≤ (C₁ + C₂ + C₂ * (1 + C₁)) * D := by nlinarith
    · intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rw [hends₂]; exact hmeet₁ c₁ hc₁
      · exact hmeet₂ c hc


set_option maxHeartbeats 2000000 in
/-- **One stage of the multigraph refine-down construction, sparse form**: `multiStage` from
sparse link levels, under the hypothesis `Cs · D ≤ |Z|`. -/
theorem multiStageS_M {q r : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelS q r i a) :
    ∃ Cs C M : ℕ, 1 ≤ M ∧ q + r ≤ Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → U.card ≤ 8 * Z.card → Cs * D ≤ Z.card →
      1 ≤ D → a Z.card ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
        (R Y : Finset E') (𝒲 : Finset (Finset E')),
        Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
        IsResidualMultiRefiner q r C ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
        (∀ c ∈ Y, ends' c ⊆ Z) ∧ (∀ e, mult ends' Y e ≤ M) ∧ (∀ c ∈ R, ends' c ⊆ U ∪ Z) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ C * D) ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ C * D) ∧
        (∀ c ∈ R, (ends' c ∩ Z).Nonempty) := by
  obtain ⟨C₀, hC₀, hround⟩ := Gen.multiRound (q := q) (r := r) (by omega) hrq
  obtain ⟨Cs₂, C₂, hCs₂, hchain⟩ := placedChainS_M hrq hL (r - 1) (by omega) 9
  obtain ⟨M, Cm, hM, hmr⟩ := multiplicityReduction_quant q r hrq.le
  set Kp := 9 ^ (r - 1) with hKp
  have hKp1 : 1 ≤ Kp := Nat.one_le_pow _ _ (by omega)
  set D₀ := C₀ * Kp with hD₀
  set A := D₀ + C₂ * D₀ + (M + 2) ^ 2 * (D₀ + C₂ * D₀) with hA
  set P := C₀ * Kp + C₂ * D₀ + Cm * (1 + (M + 2) ^ 2) * (D₀ + C₂ * D₀) with hP
  set C := (C₀ + C₂ + Cm) + A + P with hC
  refine ⟨C₀ + Cs₂ * D₀ + q + r, C, M, hM, by omega, ?_⟩
  intro n E _ ends Z U X D hXr hXU hUZ hZD hD1 haD hdeg
  have hZ : C₀ + Cs₂ * D₀ + q + r ≤ Z.card := le_trans (Nat.le_mul_of_pos_right _ hD1) hZD
  -- density of the roots
  have hXJ : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      mdeg ends X J ≤ (Kp * D) * Z.card ^ (r - 1 - J.card) := by
    intro J hJ
    refine (mdeg_le_pow hXr hXU hdeg hJ).trans ?_
    calc D * U.card ^ (r - 1 - J.card) ≤ D * (9 * Z.card) ^ (r - 1 - J.card) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = D * (9 ^ (r - 1 - J.card) * Z.card ^ (r - 1 - J.card)) := by rw [mul_pow]
      _ ≤ D * (Kp * Z.card ^ (r - 1 - J.card)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by omega) (by omega)))
      _ = Kp * D * Z.card ^ (r - 1 - J.card) := by ring
  -- 1. the round
  obtain ⟨ends₀, R₀, Y₀, 𝒲₀, hends₀, h₀, hY₀R, hR₀fresh, hR₀Z, hR₀loc, hone₀, hdeg₀, hpd₀⟩ :=
    hround n ends X Z (Kp * D) hXr (by omega) hXJ
  have hY₀r : MIsRGraph r ends₀ Y₀ := fun c hc => h₀.rgraph c (mem_union_right _ (hY₀R hc))
  have hY₀flat : IsFlat (r - 1) Z ends₀ Y₀ := by
    intro c hc
    have hcard := hY₀r c hc
    have h1 : 0 < (ends₀ c ∩ Z).card := (hR₀Z c (hY₀R hc)).card_pos
    have := card_sdiff_add_card_inter (ends₀ c) Z
    omega
  have hR₀U : ∀ c ∈ R₀, ends₀ c ⊆ U ∪ Z := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := hR₀loc c hc
    exact hcx.trans (union_subset_union (hXU x hx) subset_rfl)
  have hY₀U : ∀ c ∈ Y₀, ends₀ c ⊆ U ∪ Z := fun c hc => hR₀U c (hY₀R hc)
  have hdegR₀ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₀ R₀ S ≤ D₀ * D := by
    intro S hS; rw [hD₀, mul_assoc]; exact hdeg₀ S hS
  have hdegY₀ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₀ Y₀ S ≤ D₀ * D :=
    fun S hS => (mdeg_mono _ hY₀R S).trans (hdegR₀ S hS)
  have hUZ9 : (U ∪ Z).card ≤ 9 * Z.card := (card_union_le U Z).trans (by omega)
  have hD₀D : 1 ≤ D₀ * D := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- 2. the flat levels
  obtain ⟨E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂fresh, h₂, hY₂flat, hY₂sub, hR₂U,
    hdegR₂, hpdR₂, hmeetR₂⟩ := hchain n ends₀ Z (U ∪ Z) Y₀ (D₀ * D) hY₀r hY₀flat hY₀U hUZ9
      (by omega) hD₀D (haD.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hKp1)))
      (by rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hZD) hdegY₀
  have hY₂Z : ∀ c ∈ Y₂, ends₂ c ⊆ Z := by
    intro c hc
    have := hY₂flat c hc
    rw [Nat.le_zero, card_eq_zero, sdiff_eq_empty_iff_subset] at this
    exact this
  have hY₂r : MIsRGraph r ends₂ Y₂ := fun c hc => h₂.rgraph c (hY₂sub hc)
  have h02 := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₀
    (hY₀R.trans subset_union_right) h₂ hR₂fresh
  have hone02 := oneX_compose g₂ hg₂ h₀.disjoint hY₀R hone₀ h₂ hR₂fresh
  -- 3. multiplicity reduction
  obtain ⟨N, _, endsN, Rm, Ym, 𝒲m, hRm, hYmR, hm, hmult, hdegm, hparm⟩ := hmr ends₂ Y₂ hY₂r
  set R₀₂ := R₀.image g₂ ∪ R₂ with hR₀₂
  have hY₂R : Y₂ ⊆ R₀₂ := by
    intro c hc
    rcases mem_union.1 (hY₂sub hc) with h | h
    · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 h
      exact mem_union_left _ (mem_image_of_mem _ (hY₀R hc₀))
    · exact mem_union_right _ h
  have hR₀₂fresh : ∀ c ∈ R₀₂, ∀ x : E, g₂ (Sum.inl x) ≠ c := by
    intro c hc x
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 h
      intro hxc
      exact hR₀fresh c₀ hc₀ x (hg₂ hxc).symm
    · exact hR₂fresh c h _
  have hmR : IsResidualMultiRefiner q r Cm (Sum.elim ends₂ endsN) (Y₂.image Sum.inl)
      (Rm.image Sum.inr) Ym 𝒲m := hm
  have hinrfresh : ∀ c ∈ Rm.image (Sum.inr : N → E₂ ⊕ N), ∀ x : E₂, Sum.inl x ≠ c := by
    intro c hc x hx
    obtain ⟨y, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr hx
  have h02m := IsResidualMultiRefiner.compose (Sum.inl : E₂ → E₂ ⊕ N) Sum.inl_injective
    (fun c => rfl) h02 (hY₂R.trans subset_union_right) hmR hinrfresh
  have hone := oneX_compose (Sum.inl : E₂ → E₂ ⊕ N) Sum.inl_injective h02.disjoint hY₂R
    hone02 hmR hinrfresh
  -- assembling
  set g : E → E₂ ⊕ N := fun x => Sum.inl (g₂ (Sum.inl x)) with hgdef
  have hg : Function.Injective g := fun x y hxy =>
    Sum.inl_injective (hg₂ (Sum.inl_injective hxy))
  have hXimg : ((X.map Function.Embedding.inl).image g₂).image (Sum.inl : E₂ → E₂ ⊕ N) =
      X.image g := by
    ext c
    simp only [mem_image, mem_map, Function.Embedding.inl_apply, hgdef]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  rw [hXimg] at h02m hone
  set ends' : E₂ ⊕ N → Finset (Fin n) := Sum.elim ends₂ endsN with hends'
  have hYmRt : Ym ⊆ R₀₂.image (Sum.inl : E₂ → E₂ ⊕ N) ∪ Rm.image Sum.inr :=
    hYmR.trans subset_union_right
  -- degrees
  have hdeg₀₂ : ∀ S : Finset (Fin n), S.card = r - 1 →
      mdeg ends₂ R₀₂ S ≤ D₀ * D + C₂ * (D₀ * D) := by
    intro S hS
    refine (Dense.mdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ (hdegR₂ S hS))
    rw [mdeg_image_eq (A := R₀) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    exact hdegR₀ S hS
  refine ⟨E₂ ⊕ N, inferInstance, g, ends', R₀₂.image Sum.inl ∪ Rm.image Sum.inr, Ym,
    (𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl) ∪ 𝒲m, hg,
    fun c => by simp [hends', hgdef, hends₂, hends₀], ?_, h02m.mono (by omega), hYmRt, ?_,
    hmult, ?_, ?_, hone, ?_, ?_⟩
  · intro c hc x hx
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 h
      exact hR₀₂fresh c₂ hc₂ x (Sum.inl_injective hx)
    · obtain ⟨y, -, rfl⟩ := mem_image.1 h
      exact Sum.inl_ne_inr hx
  · intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 (hYmR hc)
    obtain ⟨c₂, hc₂, he⟩ := mem_image.1 (hRm y hy)
    show endsN y ⊆ Z
    rw [← he]; exact hY₂Z c₂ hc₂
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 h
      show ends₂ c₂ ⊆ U ∪ Z
      rcases mem_union.1 hc₂ with h' | h'
      · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 h'
        rw [hends₂]; exact hR₀U c₀ hc₀
      · refine (hR₂U c₂ h').trans ?_
        rw [union_assoc, union_self]
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 h
      obtain ⟨c₂, hc₂, he⟩ := mem_image.1 (hRm y hy)
      show endsN y ⊆ U ∪ Z
      rw [← he]; exact (hY₂Z c₂ hc₂).trans subset_union_right
  · intro S hS
    refine (Dense.mdeg_union_le _ _ _ S).trans ?_
    have e1 : mdeg ends' (R₀₂.image Sum.inl) S = mdeg ends₂ R₀₂ S :=
      mdeg_image_eq (A := R₀₂) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
    have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends₂ Y₂ S := hdegm S
    rw [e1]
    have h4 := hdeg₀₂ S hS
    calc mdeg ends₂ R₀₂ S + mdeg ends' (Rm.image Sum.inr) S
        ≤ (D₀ * D + C₂ * (D₀ * D)) + (M + 2) ^ 2 * (D₀ * D + C₂ * (D₀ * D)) := by
          refine Nat.add_le_add h4 (e2.trans (Nat.mul_le_mul_left _ ?_))
          exact (mdeg_mono _ hY₂R S).trans h4
      _ ≤ C * D := by
          have : (D₀ * D + C₂ * (D₀ * D)) + (M + 2) ^ 2 * (D₀ * D + C₂ * (D₀ * D)) = A * D := by
            rw [hA]; ring
          rw [this]
          exact Nat.mul_le_mul_right _ (by omega)
  · intro S hS
    have hSne : S.Nonempty := by rw [← card_pos, hS]; omega
    have hY₂d : mdeg ends₂ Y₂ S ≤ D₀ * D + C₂ * (D₀ * D) := (mdeg_mono _ hY₂R S).trans (hdeg₀₂ S hS)
    have hm1 : pdeg ends' 𝒲m S ≤ Cm * mdeg ends' (Y₂.image Sum.inl ∪ Rm.image Sum.inr) S :=
      pdeg_le_of_parallel hmR hparm hSne
    have hm2 : mdeg ends' (Y₂.image Sum.inl ∪ Rm.image Sum.inr) S ≤
        (1 + (M + 2) ^ 2) * (D₀ * D + C₂ * (D₀ * D)) := by
      refine (Dense.mdeg_union_le _ _ _ S).trans ?_
      have e1 : mdeg ends' (Y₂.image Sum.inl) S = mdeg ends₂ Y₂ S :=
        mdeg_image_eq (A := Y₂) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
      have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends₂ Y₂ S := hdegm S
      rw [e1]
      calc mdeg ends₂ Y₂ S + mdeg ends' (Rm.image Sum.inr) S
          ≤ (D₀ * D + C₂ * (D₀ * D)) + (M + 2) ^ 2 * (D₀ * D + C₂ * (D₀ * D)) :=
            Nat.add_le_add hY₂d (e2.trans (Nat.mul_le_mul_left _ hY₂d))
        _ = (1 + (M + 2) ^ 2) * (D₀ * D + C₂ * (D₀ * D)) := by ring
    have h0 : pdeg ends₀ 𝒲₀ S ≤ C₀ * (Kp * D) := hpd₀ S hS
    have h2 : pdeg ends₂ 𝒲₂ S ≤ C₂ * (D₀ * D) := hpdR₂ S hS
    calc pdeg ends' ((𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl) ∪ 𝒲m) S
        ≤ pdeg ends' ((𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl)) S + pdeg ends' 𝒲m S :=
          pdeg_union_le _ _ _ _
      _ ≤ (pdeg ends₂ (𝒲₀.image (image g₂)) S + pdeg ends₂ 𝒲₂ S) + pdeg ends' 𝒲m S :=
          Nat.add_le_add_right ((pdeg_image_le Sum.inl (fun c => rfl) _ S).trans
            (pdeg_union_le _ _ _ S)) _
      _ ≤ (C₀ * (Kp * D) + C₂ * (D₀ * D)) +
            Cm * ((1 + (M + 2) ^ 2) * (D₀ * D + C₂ * (D₀ * D))) := by
          refine Nat.add_le_add (Nat.add_le_add ((pdeg_image_le g₂ hends₂ 𝒲₀ S).trans h0) h2) ?_
          exact hm1.trans (Nat.mul_le_mul_left _ hm2)
      _ = P * D := by rw [hP]; ring
      _ ≤ C * D := Nat.mul_le_mul_right _ (by omega)
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 h
      show (ends₂ c₂ ∩ Z).Nonempty
      rcases mem_union.1 hc₂ with h' | h'
      · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 h'
        rw [hends₂]; exact hR₀Z c₀ hc₀
      · exact hmeetR₂ c₂ h'
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 h
      obtain ⟨c₂, hc₂, he⟩ := mem_image.1 (hRm y hy)
      show (endsN y ∩ Z).Nonempty
      rw [← he, inter_eq_left.2 (hY₂Z c₂ hc₂), ← card_pos, hY₂r c₂ hc₂]
      omega


end RefinedAbsorption.Original2024
