module
public import RequestProject.Dense.StageE
public import RequestProject.Dense.Native

/-!
# `o(n)`-budget strong multi-refiners from link levels in `ε`-form

* `refinerOut_of_stageE`: a stage (refinedness and degree bound separated) followed by a refiner
  of its residue.
* **`stagedRefinerE`**: iterating `ε`-form stages through reserves of a quarter of the size.  At
  each stage the precision is chosen after the constant of the remaining stages, so that the
  additive terms are not amplified; the refinedness stays uniform.
* **`nativeWeakStrongMultiRefiners_of_levelsE`**: `NativeWeakStrongMultiRefiners q r` from
  `PlacedLinkLevelE q r i` at the intermediate levels `1 ≤ i < r - 1`.  This hypothesis is weaker
  than those of `nativeWeakStrongMultiRefiners_of_levels` and
  `nativeWeakStrongMultiRefiners_of_levelsA` (`PlacedLinkLevel.toE`, `PlacedLinkLevelA.toE`).
-/

@[expose] public section

namespace RefinedAbsorption.Dense

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement

/-- **A stage followed by a refiner of its residue** (refinedness `Cr ≤ C`, degree bound
`Bd₁`). -/
theorem refinerOut_of_stageE {q r Cr C : ℕ} (hC : Cr ≤ C) {n : ℕ} {E : Type} [DecidableEq E]
    {ends : E → Finset (Fin n)} {Z Z₁ : Finset (Fin n)} {X : Finset E} {Bd₁ Bd₂ : ℕ}
    (hZ₁ : Z₁ ⊆ Z) {E₁ : Type} [DecidableEq E₁] {g₁ : E → E₁} {ends₁ : E₁ → Finset (Fin n)}
    {R₁ Y₁ : Finset E₁} {𝒲₁ : Finset (Finset E₁)} (hg₁ : Function.Injective g₁)
    (hends₁ : ∀ c, ends₁ (g₁ c) = ends c) (hR₁f : ∀ c ∈ R₁, ∀ x, g₁ x ≠ c)
    (h₁ : IsResidualMultiRefiner q r Cr ends₁ (X.image g₁) R₁ Y₁ 𝒲₁) (hY₁R : Y₁ ⊆ R₁)
    (hR₁Z : ∀ c ∈ R₁, ends₁ c ⊆ Z ∪ Z₁)
    (hdeg₁ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ R₁ S ≤ Bd₁)
    (hpd₁ : ∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends₁ 𝒲₁ S ≤ Bd₁)
    (hrest : RefinerOut q r C ends₁ Z₁ Y₁ Bd₂) :
    RefinerOut q r C ends Z X (Bd₁ + Bd₂) := by
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hR₂Z, hdeg₂, hpd₂⟩ := hrest
  have hpre := IsChainRefiner.prepend_relabel h₁ hY₁R hC g₂ hg₂ hends₂ h₂ hR₂f
  rw [image_image] at hpre
  refine ⟨E₂, inferInstance, g₂ ∘ g₁, ends₂, R₁.image g₂ ∪ R₂, _, hg₂.comp hg₁,
    fun c => by simp [hends₂, hends₁], ?_, hpre, ?_, ?_, ?_⟩
  · intro c hc x hx
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      exact hR₁f c₁ hc₁ x (hg₂ hx)
    · exact hR₂f c h _ hx
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      rw [hends₂]
      exact (hR₁Z c₁ hc₁).trans (union_subset subset_rfl hZ₁)
    · exact (hR₂Z c h).trans hZ₁
  · intro S hS
    refine (mdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ (hdeg₂ S hS))
    rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    exact hdeg₁ S hS
  · intro S hS
    exact (pdeg_union_le _ _ _ S).trans (Nat.add_le_add
      ((pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)) (hpd₂ S hS))

/-- The stage at precision `0` is a `StageProp` with additive term `a = id`. -/
theorem stageProp_of_stagePropE {q r Cs Cst Cr B M : ℕ} (h : StagePropE q r Cs Cst Cr B M 0) :
    StageProp q r Cs (Cr + Cst + B) M id := by
  intro n E _ ends Z U X D hXr hXU hUZ hCs hD1 haD hdeg
  obtain ⟨E', _, g, ends', R, Y, 𝒲, Bd, hBd, hg, hends, hRf, h₁, hYR, hYZ, hmult, hRU, hdegR,
    hone, hpd⟩ := h n ends Z U X D hXr hXU hUZ hCs hD1 hdeg
  simp only [pow_zero, one_mul] at hBd
  have haD' : Z.card ≤ D := haD
  have hBdD : Bd ≤ (Cr + Cst + B) * D := by nlinarith
  exact ⟨E', inferInstance, g, ends', R, Y, 𝒲, hg, hends, hRf, h₁.mono (by omega), hYR, hYZ,
    hmult, hRU, fun S hS => (hdegR S hS).trans hBdD, hone, fun S hS => (hpd S hS).trans hBdD⟩

set_option maxHeartbeats 1000000 in
/-- **Staged refiners inside a reserve, `ε`-form.** -/
theorem stagedRefinerE {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelE q r i) :
    ∃ Cr B M C B' : ℕ, 1 ≤ M ∧ Cr ≤ C ∧ B ≤ B' ∧
      (∀ s : ℕ, ∃ Cs Cst : ℕ, q + r ≤ Cs ∧ StagePropE q r Cs Cst Cr B M s) ∧
      ∀ t : ℕ, ∃ Ct : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
        (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
        MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → 1 ≤ D →
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
        ∃ Bd : ℕ, 2 ^ t * Bd ≤ 2 ^ t * Ct * D + B' * Z.card ∧
          RefinerOut q r C ends Z X Bd := by
  obtain ⟨Cr, B, M, hM, hst⟩ := multiStageE hr hrq hL
  obtain ⟨Cs₀, Cst₀, hCs₀, h0⟩ := hst 0
  set Cst' := Cr + Cst₀ + B with hCst'
  have hstage0 := stageProp_of_stagePropE h0
  obtain ⟨Cb, Ab, hbase⟩ := baseRefiner q r hr hrq (4 * Cs₀ + 12)
  have hdense := denseRefiner_of hr hM (by omega) (fun m => le_rfl) hstage0 hbase
  set A := Cst' + Ab with hA
  set B' := A * M + B with hB'
  refine ⟨Cr, B, M, Cst' + Cb, B', hM, by omega, by omega, hst, fun t => ?_⟩
  induction t with
  | zero =>
    refine ⟨A, fun n E _ ends Z X D hXr hXZ hD1 hdeg => ⟨_, ?_,
      hdense n ends Z X D hXr hXZ hD1 hdeg⟩⟩
    simp only [pow_zero, one_mul]
    have : A * M * Z.card ≤ B' * Z.card := Nat.mul_le_mul_right _ (by omega)
    omega
  | succ t ih =>
    obtain ⟨Ct, hCt⟩ := ih
    set s := t + 2 + Ct with hs
    obtain ⟨Cs, Cst, hCs, hstage⟩ := hst s
    refine ⟨2 ^ s * Cst + Ct + A + B' * (4 * Cs + 12), ?_⟩
    intro n E _ ends Z X D hXr hXZ hD1 hdeg
    by_cases hsmall : Z.card ≤ 4 * Cs + 12
    · refine ⟨_, ?_, hdense n ends Z X D hXr hXZ hD1 hdeg⟩
      have h1 : A * M * Z.card ≤ B' * (4 * Cs + 12) :=
        Nat.mul_le_mul (by omega) hsmall
      have h2 : B' * (4 * Cs + 12) ≤ B' * (4 * Cs + 12) * D := Nat.le_mul_of_pos_right _ hD1
      have h3 : A * D + A * M * Z.card ≤ (2 ^ s * Cst + Ct + A + B' * (4 * Cs + 12)) * D := by
        have e : (2 ^ s * Cst + Ct + A + B' * (4 * Cs + 12)) * D =
            2 ^ s * Cst * D + Ct * D + A * D + B' * (4 * Cs + 12) * D := by ring
        rw [e]; omega
      calc 2 ^ (t + 1) * (A * D + A * M * Z.card)
          ≤ 2 ^ (t + 1) * ((2 ^ s * Cst + Ct + A + B' * (4 * Cs + 12)) * D) :=
            Nat.mul_le_mul_left _ h3
        _ = 2 ^ (t + 1) * (2 ^ s * Cst + Ct + A + B' * (4 * Cs + 12)) * D := by ring
        _ ≤ _ := Nat.le_add_right _ _
    · obtain ⟨Z₁, hZ₁Z, hZ₁c⟩ := exists_quarter Z
      have hZ8 : Z.card ≤ 8 * Z₁.card := by omega
      have hCsZ : Cs ≤ Z₁.card := by omega
      obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, Bd₁, hBd₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁Z, -,
        hR₁Z, hdeg₁, -, hpd₁⟩ := hstage n ends Z₁ Z X D hXr hXZ hZ8 hCsZ hD1 hdeg
      have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
      have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ D + Bd₁ :=
        fun S hS => (mdeg_mono _ hY₁R S).trans ((hdeg₁ S hS).trans (Nat.le_add_left _ _))
      obtain ⟨Bd₂, hBd₂, hrest⟩ := hCt n ends₁ Z₁ Y₁ (D + Bd₁) hY₁r hY₁Z (by omega) hdegY
      refine ⟨Bd₁ + Bd₂, ?_, refinerOut_of_stageE (by omega) hZ₁Z hg₁ hends₁ hR₁f h₁ hY₁R
        hR₁Z hdeg₁ hpd₁ hrest⟩
      have h4 : 4 * Z₁.card ≤ Z.card := by omega
      -- `2 · 2^(t+1) · (1 + Ct) ≤ 2^s`
      have hpow : 2 * 2 ^ (t + 1) * (1 + Ct) ≤ 2 ^ s := by
        have := Nat.lt_two_pow_self (n := Ct)
        have e : 2 ^ s = 2 * 2 ^ (t + 1) * 2 ^ Ct := by
          rw [hs, show t + 2 + Ct = 1 + (t + 1) + Ct by omega, pow_add, pow_add, pow_one]
        rw [e]
        exact Nat.mul_le_mul_left _ (by omega)
      have hB1 : 2 * 2 ^ (t + 1) * (1 + Ct) * Bd₁ ≤ 2 ^ s * Cst * D + B * Z₁.card :=
        (Nat.mul_le_mul_right _ hpow).trans hBd₁
      have e1 : 2 ^ t * Ct * (D + Bd₁) = 2 ^ t * Ct * D + 2 ^ t * Ct * Bd₁ := by ring
      rw [e1] at hBd₂
      have hBZ : B * Z₁.card ≤ B' * Z.card := Nat.mul_le_mul (by omega) (by omega)
      have hBZ' : 4 * (B' * Z₁.card) ≤ B' * Z.card := by nlinarith
      have hpos : 1 ≤ 2 ^ (t + 2) := Nat.one_le_two_pow
      have key : 2 * (2 ^ (t + 1) * (Bd₁ + Bd₂)) ≤
          2 * (2 ^ (t + 1) * (2 ^ s * Cst + Ct + A + B' * (4 * Cs + 12)) * D + B' * Z.card) := by
        have e2 : 2 * (2 ^ (t + 1) * (Bd₁ + Bd₂)) =
            2 * 2 ^ (t + 1) * Bd₁ + 4 * (2 ^ t * Bd₂) := by ring
        have e3 : 2 * 2 ^ (t + 1) * (1 + Ct) * Bd₁ =
            2 * 2 ^ (t + 1) * Bd₁ + 4 * (2 ^ t * Ct * Bd₁) := by ring
        have e4 : 2 * (2 ^ (t + 1) * (2 ^ s * Cst + Ct + A + B' * (4 * Cs + 12)) * D +
            B' * Z.card) = 2 ^ (t + 2) * (2 ^ s * Cst * D) + 4 * (2 ^ t * Ct * D) +
              2 ^ (t + 2) * ((A + B' * (4 * Cs + 12)) * D) + 2 * (B' * Z.card) := by ring
        rw [e2, e4]
        rw [e3] at hB1
        have h5 : 2 ^ s * Cst * D ≤ 2 ^ (t + 2) * (2 ^ s * Cst * D) := Nat.le_mul_of_pos_left _ hpos
        omega
      omega

set_option maxHeartbeats 1000000 in
/-- **`NativeWeakStrongMultiRefiners q r` from the intermediate link levels in `ε`-form.** -/
theorem nativeWeakStrongMultiRefiners_of_levelsE {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelE q r i) :
    NativeWeakStrongMultiRefiners q r := by
  have hL' : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelE q r i := fun i hi hir => by
    rcases Nat.lt_or_ge i (r - 1) with h | h
    · exact hL i hi h
    · obtain rfl : i = r - 1 := by omega
      exact (placedLinkLevel_last q r hr hrq).toE
  obtain ⟨Cr, B, M, C, B', hM, hCrC, hBB', hst, hstaged⟩ := stagedRefinerE hr hrq hL'
  refine ⟨3 * C + 1, B + B', by omega, fun t => ?_⟩
  obtain ⟨Ct, hCt⟩ := hstaged t
  set s := t + Ct + 1 with hs
  obtain ⟨Cs, Cst, hCs, hstage⟩ := hst s
  refine ⟨1 + 2 ^ s * Cst + Ct, 4 * Cs + 12, fun n hn X D hX hD1 hdeg => ?_⟩
  obtain ⟨Z₁, -, hZ₁c⟩ := exists_quarter (univ : Finset (Fin n))
  rw [card_univ, Fintype.card_fin] at hZ₁c
  have hXr : MIsRGraph r (id : Finset (Fin n) → Finset (Fin n)) X := hX
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, Bd₁, hBd₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁Z, -, -,
    hdeg₁, hone₁, hpd₁⟩ := hstage n id Z₁ univ X D hXr (fun _ _ => subset_univ _)
      (by rw [card_univ, Fintype.card_fin]; omega) (by omega) hD1 hdeg
  have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ D + Bd₁ :=
    fun S hS => (mdeg_mono _ hY₁R S).trans ((hdeg₁ S hS).trans (Nat.le_add_left _ _))
  obtain ⟨Bd₂, hBd₂, E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, -, hdeg₂, hpd₂⟩ :=
    hCt n ends₁ Z₁ Y₁ (D + Bd₁) hY₁r hY₁Z (by omega) hdegY
  have hpre := IsChainRefiner.prepend_relabel h₁ hY₁R hCrC g₂ hg₂ hends₂ h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂.base hR₂f
  rw [image_image] at hpre hone
  set Bd := D + (Bd₁ + Bd₂) with hBd
  have hendsX : ∀ e, ends₂ ((g₂ ∘ g₁) e) = e := fun e => by simp [hends₂, hends₁]
  refine ⟨E₂, inferInstance, ends₂, X.image (g₂ ∘ g₁), X.image (g₂ ∘ g₁),
    R₁.image g₂ ∪ R₂, 𝒲₁.image (image g₂) ∪ 𝒲₂, Bd, ?_, ?_, ?_⟩
  · rw [image_image]
    have : ends₂ ∘ (g₂ ∘ g₁) = id := funext hendsX
    rw [this, image_id]
  · -- the budget
    have hZ₁n : Z₁.card ≤ n := by omega
    have hpow : 2 ^ t * (1 + Ct) ≤ 2 ^ s := by
      have := Nat.lt_two_pow_self (n := Ct)
      have e : 2 ^ s = 2 ^ t * 2 ^ (Ct + 1) := by rw [hs, add_assoc, pow_add]
      rw [e]
      exact Nat.mul_le_mul_left (2 ^ t) (show 1 + Ct ≤ 2 ^ (Ct + 1) by rw [pow_succ]; omega)
    have hB1 : 2 ^ t * (1 + Ct) * Bd₁ ≤ 2 ^ s * Cst * D + B * Z₁.card :=
      (Nat.mul_le_mul_right _ hpow).trans hBd₁
    have e1 : 2 ^ t * Ct * (D + Bd₁) = 2 ^ t * Ct * D + 2 ^ t * Ct * Bd₁ := by ring
    rw [e1] at hBd₂
    have e2 : 2 ^ t * Bd = 2 ^ t * D + 2 ^ t * Bd₁ + 2 ^ t * Bd₂ := by rw [hBd]; ring
    have e3 : 2 ^ t * (1 + Ct) * Bd₁ = 2 ^ t * Bd₁ + 2 ^ t * Ct * Bd₁ := by ring
    have e4 : 2 ^ t * (1 + 2 ^ s * Cst + Ct) * D + (B + B') * n =
        2 ^ t * D + 2 ^ t * (2 ^ s * Cst * D) + 2 ^ t * Ct * D + B * n + B' * n := by ring
    rw [e2, e4]
    rw [e3] at hB1
    have h5 : 2 ^ s * Cst * D ≤ 2 ^ t * (2 ^ s * Cst * D) :=
      Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
    have h6 : B * Z₁.card ≤ B * n := Nat.mul_le_mul_left _ hZ₁n
    have h7 : B' * Z₁.card ≤ B' * n := Nat.mul_le_mul_left _ hZ₁n
    omega
  · have hinj : Set.InjOn ends₂ (X.image (g₂ ∘ g₁) : Set _) := by
      intro a ha b hb hab
      obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 ha)
      obtain ⟨y, -, rfl⟩ := mem_image.1 (mem_coe.1 hb)
      rw [hendsX, hendsX] at hab
      rw [hab]
    have hDBd : D ≤ Bd := Nat.le_add_right _ _
    exact
      { refiner := hpre.base.mono (by omega)
        keep := subset_rfl
        inj := hinj
        oneX := hone
        degX := fun S hS => by
          rw [mdeg_image_eq (A := X) (fun c _ => hendsX c) (hg₂.comp hg₁).injOn subset_rfl]
          exact (hdeg S hS).trans hDBd
        degR := fun S hS => by
          refine (mdeg_union_le _ _ _ S).trans ?_
          rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
          have := hdeg₁ S hS
          have := hdeg₂ S hS
          have : Bd ≤ (3 * C + 1) * Bd := Nat.le_mul_of_pos_left _ (by omega)
          omega
        pieceDeg := fun S hS => by
          refine (pdeg_union_le _ _ _ S).trans ?_
          have := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
          have := hpd₂ S hS
          have : Bd ≤ (3 * C + 1) * Bd := Nat.le_mul_of_pos_left _ (by omega)
          change pdeg _ _ S + pdeg _ _ S ≤ _
          omega }

end RefinedAbsorption.Dense
