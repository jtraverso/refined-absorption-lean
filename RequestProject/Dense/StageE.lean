module
public import RequestProject.Dense.Stage
public import RequestProject.Placement.ChainLevelsE

/-!
# One stage, with link levels in `ε`-form

As `multiStage` (anti-edge round into `Z`, flat levels `r - 1, …, 1`, multiplicity reduction),
but with the link levels in `ε`-form (`PlacedLinkLevelE`).  For every precision `s` the stage
costs `Cst_s · D + B · |Z| / 2^s`, where the refinedness `Cr`, the additive constant `B` and the
multiplicity bound `M` do not depend on `s` (`StagePropE`, **`multiStageE`**).
-/

@[expose] public section

namespace RefinedAbsorption.Dense

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement

/-- The conclusion of one stage at precision `s` (refinedness `Cr`, degree bound `Bd` with
`2^s · Bd ≤ 2^s · Cst · D + B · |Z|`). -/
def StagePropE (q r Cs Cst Cr B M s : ℕ) : Prop :=
  ∀ (n : ℕ) {E : Type} [DecidableEq E]
    (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → U.card ≤ 8 * Z.card → Cs ≤ Z.card →
    1 ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R Y : Finset E') (𝒲 : Finset (Finset E')) (Bd : ℕ),
      2 ^ s * Bd ≤ 2 ^ s * Cst * D + B * Z.card ∧
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsResidualMultiRefiner q r Cr ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
      (∀ c ∈ Y, ends' c ⊆ Z) ∧ (∀ e, mult ends' Y e ≤ M) ∧ (∀ c ∈ R, ends' c ⊆ U ∪ Z) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ Bd) ∧
      (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ Bd)

set_option maxHeartbeats 2000000 in
/-- **One stage of the multigraph refine-down construction, `ε`-form.** -/
theorem multiStageE {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelE q r i) :
    ∃ Cr B M : ℕ, 1 ≤ M ∧ ∀ s : ℕ, ∃ Cs Cst : ℕ, q + r ≤ Cs ∧ StagePropE q r Cs Cst Cr B M s := by
  obtain ⟨C₀, hC₀, hround⟩ := Gen.multiRound (q := q) (r := r) (by omega) hrq
  obtain ⟨Cr₂, B₂, hchain⟩ := placedChainE hrq hL (r - 1) (by omega) 9
  obtain ⟨M, Cm, hM, hmr⟩ := multiplicityReduction_quant q r hrq.le
  set A' := 1 + (M + 2) ^ 2 + Cm * (1 + (M + 2) ^ 2) with hA'
  refine ⟨C₀ + Cr₂ + Cm, A' * B₂, M, hM, fun s => ?_⟩
  obtain ⟨Cs₂, C₂, hchain'⟩ := hchain s
  set Kp := 9 ^ (r - 1) with hKp
  have hKp1 : 1 ≤ Kp := Nat.one_le_pow _ _ (by omega)
  set D₀ := C₀ * Kp with hD₀
  refine ⟨C₀ + Cs₂ + q + r, A' * D₀ * (1 + C₂), by omega, ?_⟩
  intro n E _ ends Z U X D hXr hXU hUZ hZ hD1 hdeg
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
  obtain ⟨Bd₂, hBd₂, E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂fresh, h₂, hY₂flat, hY₂sub,
    hR₂U, hdegR₂, hpdR₂⟩ := hchain' n ends₀ Z (U ∪ Z) Y₀ (D₀ * D) hY₀r hY₀flat hY₀U hUZ9
      (by omega) hD₀D (by omega) hdegY₀
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
  set T₀ := D₀ * D + Bd₂ with hT₀
  have hdeg₀₂ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₂ R₀₂ S ≤ T₀ := by
    intro S hS
    refine (mdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ (hdegR₂ S hS))
    rw [mdeg_image_eq (A := R₀) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    exact hdegR₀ S hS
  refine ⟨E₂ ⊕ N, inferInstance, g, ends', R₀₂.image Sum.inl ∪ Rm.image Sum.inr, Ym,
    (𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl) ∪ 𝒲m, A' * T₀, ?_, hg,
    fun c => by simp [hends', hgdef, hends₂, hends₀], ?_, h02m, hYmRt, ?_,
    hmult, ?_, ?_, hone, ?_⟩
  · -- the budget
    have e1 : 2 ^ s * (A' * T₀) = A' * (2 ^ s * D₀ * D + 2 ^ s * Bd₂) := by rw [hT₀]; ring
    have e2 : 2 ^ s * (A' * D₀ * (1 + C₂)) * D + A' * B₂ * Z.card =
        A' * (2 ^ s * D₀ * D + (2 ^ s * C₂ * (D₀ * D) + B₂ * Z.card)) := by ring
    rw [e1, e2]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hBd₂ _)
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
    refine (mdeg_union_le _ _ _ S).trans ?_
    have e1 : mdeg ends' (R₀₂.image Sum.inl) S = mdeg ends₂ R₀₂ S :=
      mdeg_image_eq (A := R₀₂) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
    have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends₂ Y₂ S := hdegm S
    rw [e1]
    have h4 := hdeg₀₂ S hS
    have h5 : mdeg ends' (Rm.image Sum.inr) S ≤ (M + 2) ^ 2 * T₀ :=
      e2.trans (Nat.mul_le_mul_left _ ((mdeg_mono _ hY₂R S).trans h4))
    calc mdeg ends₂ R₀₂ S + mdeg ends' (Rm.image Sum.inr) S ≤ T₀ + (M + 2) ^ 2 * T₀ :=
          Nat.add_le_add h4 h5
      _ ≤ A' * T₀ := by
          have : T₀ + (M + 2) ^ 2 * T₀ ≤ (1 + (M + 2) ^ 2) * T₀ := by ring_nf; omega
          exact this.trans (Nat.mul_le_mul_right _ (by omega))
  · intro S hS
    have hSne : S.Nonempty := by rw [← card_pos, hS]; omega
    have hY₂d : mdeg ends₂ Y₂ S ≤ T₀ := (mdeg_mono _ hY₂R S).trans (hdeg₀₂ S hS)
    have hm1 : pdeg ends' 𝒲m S ≤ Cm * mdeg ends' (Y₂.image Sum.inl ∪ Rm.image Sum.inr) S :=
      pdeg_le_of_parallel hmR hparm hSne
    have hm2 : mdeg ends' (Y₂.image Sum.inl ∪ Rm.image Sum.inr) S ≤
        (1 + (M + 2) ^ 2) * T₀ := by
      refine (mdeg_union_le _ _ _ S).trans ?_
      have e1 : mdeg ends' (Y₂.image Sum.inl) S = mdeg ends₂ Y₂ S :=
        mdeg_image_eq (A := Y₂) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
      have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends₂ Y₂ S := hdegm S
      rw [e1]
      calc mdeg ends₂ Y₂ S + mdeg ends' (Rm.image Sum.inr) S
          ≤ T₀ + (M + 2) ^ 2 * T₀ := Nat.add_le_add hY₂d (e2.trans (Nat.mul_le_mul_left _ hY₂d))
        _ = (1 + (M + 2) ^ 2) * T₀ := by ring
    have h0 : pdeg ends₀ 𝒲₀ S ≤ C₀ * (Kp * D) := hpd₀ S hS
    have h2 : pdeg ends₂ 𝒲₂ S ≤ Bd₂ := hpdR₂ S hS
    have h0' : C₀ * (Kp * D) = D₀ * D := by rw [hD₀]; ring
    calc pdeg ends' ((𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl) ∪ 𝒲m) S
        ≤ pdeg ends' ((𝒲₀.image (image g₂) ∪ 𝒲₂).image (image Sum.inl)) S + pdeg ends' 𝒲m S :=
          pdeg_union_le _ _ _ _
      _ ≤ (pdeg ends₂ (𝒲₀.image (image g₂)) S + pdeg ends₂ 𝒲₂ S) + pdeg ends' 𝒲m S :=
          Nat.add_le_add_right ((pdeg_image_le Sum.inl (fun c => rfl) _ S).trans
            (pdeg_union_le _ _ _ S)) _
      _ ≤ (D₀ * D + Bd₂) + Cm * ((1 + (M + 2) ^ 2) * T₀) := by
          refine Nat.add_le_add (Nat.add_le_add ((pdeg_image_le g₂ hends₂ 𝒲₀ S).trans
            (h0.trans h0'.le)) h2) ?_
          exact hm1.trans (Nat.mul_le_mul_left _ hm2)
      _ = (1 + Cm * (1 + (M + 2) ^ 2)) * T₀ := by rw [hT₀]; ring
      _ ≤ A' * T₀ := Nat.mul_le_mul_right _ (by omega)

end RefinedAbsorption.Dense
