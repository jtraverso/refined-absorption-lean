module
public import RequestProject.Dense.Refiner

/-!
# Iterating the stages

* `RefinerOut q r C ends Z X Bd`: after an injective relabelling, `X` has a complete chain
  refiner with constants `C, C, C`, fresh copies inside `Z`, and `(r-1)`-degrees `≤ Bd`.
* `baseRefiner`: if `|Z| ≤ m₀`, multiplicity reduction followed by the finite step.
* `refinerOut_of_stage`: a stage followed by a refiner of its residue.
* **`denseRefiner`**: `RefinerOut` with `Bd = A · D + B · |Z|`.
* **`stagedRefiner`**: for every `t`, `RefinerOut` with `2^t · Bd ≤ 2^t · C_t · D + B · |Z|`,
  where `C` and `B` do not depend on `t`.
-/

@[expose] public section

namespace RefinedAbsorption.Dense

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement

/-- Output of the refiner construction (see the module docstring). -/
def RefinerOut (q r C : ℕ) {n : ℕ} {E : Type} (ends : E → Finset (Fin n)) (Z : Finset (Fin n))
    (X : Finset E) (Bd : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
    (R : Finset E') (𝒲 : Finset (Finset E')),
    Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
    IsChainRefiner q r C C C ends' (X.image g) R ∅ 𝒲 ∧ (∀ c ∈ R, ends' c ⊆ Z) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ Bd) ∧
    ∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ Bd

theorem RefinerOut.mono {q r C C' : ℕ} {n : ℕ} {E : Type} {ends : E → Finset (Fin n)}
    {Z : Finset (Fin n)} {X : Finset E} {Bd Bd' : ℕ} (h : RefinerOut q r C ends Z X Bd)
    (hC : C ≤ C') (hB : Bd ≤ Bd') : RefinerOut q r C' ends Z X Bd' := by
  obtain ⟨E', _, g, ends', R, 𝒲, hg, he, hf, hch, hZ, hd, hp⟩ := h
  exact ⟨E', inferInstance, g, ends', R, 𝒲, hg, he, hf, hch.mono' hC hC hC, hZ,
    fun S hS => (hd S hS).trans hB, fun S hS => (hp S hS).trans hB⟩

/-- **Small reserves**: multiplicity reduction followed by the finite step. -/
theorem baseRefiner (q r : ℕ) (hr : 2 ≤ r) (hrq : r < q) (m₀ : ℕ) :
    ∃ Cb Ab : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → Z.card ≤ m₀ → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r Cb ends Z X (Ab * D) := by
  obtain ⟨M, Cm, hM, hmr⟩ := multiplicityReduction_quant q r hrq.le
  set Kf := M * 2 ^ m₀ with hKf
  refine ⟨Cm + (Kf + 2 ^ Kf), (M + 2) ^ 2 + Cm * (1 + (M + 2) ^ 2) + 2 ^ Kf, ?_⟩
  intro n E _ ends Z X D hXr hXZ hZm hD1 hdeg
  obtain ⟨N, _, endsN, Rm, Ym, 𝒲m, hRm, hYmR, hm, hmult, hdegm, hparm⟩ := hmr ends X hXr
  set ends' : E ⊕ N → Finset (Fin n) := Sum.elim ends endsN with hends'
  have hRmZ : ∀ c ∈ Rm.image (Sum.inr : N → E ⊕ N), ends' c ⊆ Z := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    obtain ⟨x, hx, he⟩ := mem_image.1 (hRm y hy)
    show endsN y ⊆ Z
    rw [← he]; exact hXZ x hx
  have hYmr : MIsRGraph r ends' Ym := fun c hc => hm.rgraph c (mem_union_right _ (hYmR hc))
  have hYmcard : Ym.card ≤ Kf :=
    (card_le_of_mult (fun c hc => hRmZ c (hYmR hc)) hmult).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hZm))
  have hf := finiteStep (q := q) hYmr hYmcard
  have hle : Kf + 2 ^ Kf ≤ Cm + (Kf + 2 ^ Kf) := Nat.le_add_left _ _
  have hch := (IsChainRefiner.ofResidual hf (empty_subset _)).mono' hle hle hle
  have hpre := IsChainRefiner.prepend hm hYmR (Nat.le_add_right _ _) hch (disjoint_empty_left _)
  rw [union_empty] at hpre
  refine ⟨E ⊕ N, inferInstance, Sum.inl, ends', Rm.image Sum.inr, _, Sum.inl_injective,
    fun c => rfl, ?_, hpre, hRmZ, fun S hS => (hdegm S).trans ?_, fun S hS => ?_⟩
  · intro c hc x hx
    obtain ⟨y, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr hx
  · exact (Nat.mul_le_mul_left _ (hdeg S hS)).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_right_of_le (Nat.le_add_right _ _)))
  · have hSne : S.Nonempty := by rw [← card_pos, hS]; omega
    have hmR : IsResidualMultiRefiner q r Cm ends' (X.image Sum.inl) (Rm.image Sum.inr) Ym 𝒲m :=
      hm
    have h1 : pdeg ends' 𝒲m S ≤ Cm * mdeg ends' (X.image Sum.inl ∪ Rm.image Sum.inr) S :=
      pdeg_le_of_parallel hmR hparm hSne
    have h2 : mdeg ends' (X.image Sum.inl ∪ Rm.image Sum.inr) S ≤ (1 + (M + 2) ^ 2) * D := by
      refine (mdeg_union_le _ _ _ S).trans ?_
      have e1 : mdeg ends' (X.image Sum.inl) S = mdeg ends X S :=
        mdeg_image_eq (A := X) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
      rw [e1]
      calc mdeg ends X S + mdeg ends' (Rm.image Sum.inr) S ≤ D + (M + 2) ^ 2 * D :=
            Nat.add_le_add (hdeg S hS) ((hdegm S).trans (Nat.mul_le_mul_left _ (hdeg S hS)))
        _ = (1 + (M + 2) ^ 2) * D := by ring
    have h3 : ∀ 𝒲' : Finset (Finset (E ⊕ N)), (∀ W ∈ 𝒲', W ⊆ Ym ∪ ∅) →
        pdeg ends' 𝒲' S ≤ 2 ^ Kf * D := by
      intro 𝒲' h𝒲'
      refine (pdeg_le_card _ _ _).trans ((card_le_card fun W hW =>
        mem_powerset.2 (by simpa using h𝒲' W hW)).trans ?_)
      rw [card_powerset]
      exact (Nat.pow_le_pow_right (by norm_num) hYmcard).trans (Nat.le_mul_of_pos_right _ hD1)
    refine (pdeg_union_le _ _ _ S).trans ((Nat.add_le_add (h1.trans (Nat.mul_le_mul_left _ h2))
      (h3 _ hf.subset)).trans ?_)
    · have e : ((M + 2) ^ 2 + Cm * (1 + (M + 2) ^ 2) + 2 ^ Kf) * D =
          (M + 2) ^ 2 * D + (Cm * ((1 + (M + 2) ^ 2) * D) + 2 ^ Kf * D) := by ring
      rw [e]
      exact Nat.le_add_left _ _

/-- **A stage followed by a refiner of its residue.** -/
theorem refinerOut_of_stage {q r Cst C : ℕ} (hC : Cst ≤ C) {n : ℕ} {E : Type} [DecidableEq E]
    {ends : E → Finset (Fin n)} {Z Z₁ : Finset (Fin n)} {X : Finset E} {D Bd₂ : ℕ}
    (hZ₁ : Z₁ ⊆ Z) {E₁ : Type} [DecidableEq E₁] {g₁ : E → E₁} {ends₁ : E₁ → Finset (Fin n)}
    {R₁ Y₁ : Finset E₁} {𝒲₁ : Finset (Finset E₁)} (hg₁ : Function.Injective g₁)
    (hends₁ : ∀ c, ends₁ (g₁ c) = ends c) (hR₁f : ∀ c ∈ R₁, ∀ x, g₁ x ≠ c)
    (h₁ : IsResidualMultiRefiner q r Cst ends₁ (X.image g₁) R₁ Y₁ 𝒲₁) (hY₁R : Y₁ ⊆ R₁)
    (hR₁Z : ∀ c ∈ R₁, ends₁ c ⊆ Z ∪ Z₁)
    (hdeg₁ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ R₁ S ≤ Cst * D)
    (hpd₁ : ∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends₁ 𝒲₁ S ≤ Cst * D)
    (hrest : RefinerOut q r C ends₁ Z₁ Y₁ Bd₂) :
    RefinerOut q r C ends Z X (Cst * D + Bd₂) := by
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

/-- The hypotheses of the stage lemma, packaged.  The stage is only required for degree
parameters `D ≥ a |Z|` (`a = 0`: no restriction). -/
def StageProp (q r Cs Cst M : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) {E : Type} [DecidableEq E]
    (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → U.card ≤ 8 * Z.card → Cs ≤ Z.card →
    1 ≤ D → a Z.card ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R Y : Finset E') (𝒲 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsResidualMultiRefiner q r Cst ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
      (∀ c ∈ Y, ends' c ⊆ Z) ∧ (∀ e, mult ends' Y e ≤ M) ∧ (∀ c ∈ R, ends' c ⊆ U ∪ Z) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ Cst * D) ∧
      (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ Cst * D)

/-- Choosing the next reserve: a quarter of the current one. -/
theorem exists_quarter {n : ℕ} (Z : Finset (Fin n)) :
    ∃ Z₁ ⊆ Z, Z₁.card = Z.card / 4 :=
  exists_subset_card_eq (Nat.div_le_self _ _)

/-- **Refiners inside a reserve**, from the stage lemma (see the module docstring).  The
additive term of the stage is at most linear: `a m ≤ m`. -/
theorem denseRefiner_of {q r Cs Cst M Cb Ab : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M)
    (hCs : 1 ≤ Cs) (hale : ∀ m, a m ≤ m)
    (hstage : StageProp q r Cs Cst M a)
    (hbase : ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → Z.card ≤ 4 * Cs + 12 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r Cb ends Z X (Ab * D)) :
    ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends Z X
        ((Cst + Ab) * D + (Cst + Ab) * M * Z.card) := by
  intro n
  suffices key : ∀ m, ∀ {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ), Z.card = m →
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends Z X ((Cst + Ab) * D + (Cst + Ab) * M * Z.card) from
    fun E _ ends Z X D => key _ ends Z X D rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro E _ ends Z X D hZm hXr hXZ hD1 hdeg
  by_cases hsmall : Z.card ≤ 4 * Cs + 12
  · refine (hbase n ends Z X D hXr hXZ hsmall hD1 hdeg).mono (by omega) ?_
    nlinarith [Nat.zero_le ((Cst + Ab) * M * Z.card)]
  · obtain ⟨Z₁, hZ₁Z, hZ₁c⟩ := exists_quarter Z
    have hZ8 : Z.card ≤ 8 * Z₁.card := by omega
    have hCsZ : Cs ≤ Z₁.card := by omega
    obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁Z, hmult, hR₁Z,
      hdeg₁, -, hpd₁⟩ := hstage n ends Z₁ Z X (D + Z₁.card) hXr hXZ hZ8 hCsZ (by omega)
        ((hale _).trans (Nat.le_add_left _ _)) (fun S hS => (hdeg S hS).trans (by omega))
    have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
    have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ M * Z₁.card :=
      fun S hS => mdeg_le_of_mult hY₁r hY₁Z hmult S (by omega)
    have hlt : Z₁.card < m := by omega
    have hrest := ih _ hlt ends₁ Z₁ Y₁ (M * Z₁.card) rfl hY₁r hY₁Z
      (Nat.mul_pos (by omega) (by omega)) hdegY
    refine (refinerOut_of_stage (by omega) hZ₁Z hg₁ hends₁ hR₁f h₁ hY₁R hR₁Z hdeg₁ hpd₁
      hrest).mono le_rfl ?_
    have h4 : 4 * Z₁.card ≤ Z.card := by omega
    set A := Cst + Ab
    have hCA : Cst ≤ A * M := le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ hM)
    have e : Cst * (D + Z₁.card) + (A * (M * Z₁.card) + A * M * Z₁.card) =
        Cst * D + (Cst * Z₁.card + 2 * (A * M) * Z₁.card) := by ring
    have h1 : Cst * Z₁.card + 2 * (A * M) * Z₁.card ≤ A * M * Z.card := by
      calc Cst * Z₁.card + 2 * (A * M) * Z₁.card ≤ A * M * Z₁.card + 2 * (A * M) * Z₁.card :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ hCA) _
        _ ≤ A * M * (4 * Z₁.card) := by nlinarith
        _ ≤ A * M * Z.card := Nat.mul_le_mul_left _ h4
    have hCD : Cst * D ≤ A * D := Nat.mul_le_mul_right _ (by omega)
    rw [e]
    linarith

/-- **Staged refiners**: the first `t` stages keep the residue sparse.  The stage may carry a
monotone additive term `a |Z|` with `a m ≤ m`; the budget then has `D + a |Z|` in place of `D`. -/
theorem stagedRefiner_of {q r Cs Cst M Cb Ab : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M)
    (hCs : 1 ≤ Cs) (hale : ∀ m, a m ≤ m) (hamono : Monotone a)
    (hstage : StageProp q r Cs Cst M a)
    (hbase : ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → Z.card ≤ 4 * Cs + 12 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r Cb ends Z X (Ab * D)) :
    ∀ t : ℕ, ∃ Ct : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      ∃ Bd : ℕ, 2 ^ t * Bd ≤ 2 ^ t * Ct * (D + a Z.card) + (Cst + Ab) * M * Z.card ∧
        RefinerOut q r (Cst + Cb) ends Z X Bd := by
  intro t
  induction t with
  | zero =>
    refine ⟨Cst + Ab, fun n E _ ends Z X D hXr hXZ hD1 hdeg => ⟨_, ?_,
      denseRefiner_of hr hM hCs hale hstage hbase n ends Z X D hXr hXZ hD1 hdeg⟩⟩
    have : (Cst + Ab) * D ≤ (Cst + Ab) * (D + a Z.card) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    simp only [pow_zero, one_mul]
    omega
  | succ t ih =>
    obtain ⟨Ct, hCt⟩ := ih
    refine ⟨Cst + Ct * (Cst + 2) + Ab, ?_⟩
    intro n E _ ends Z X D hXr hXZ hD1 hdeg
    set D' := D + a Z.card with hD'
    have hDD' : D ≤ D' := Nat.le_add_right _ _
    by_cases hsmall : Z.card ≤ 4 * Cs + 12
    · refine ⟨Ab * D, ?_, (hbase n ends Z X D hXr hXZ hsmall hD1 hdeg).mono (by omega) le_rfl⟩
      have : Ab * D ≤ (Cst + Ct * (Cst + 2) + Ab) * D' :=
        Nat.mul_le_mul (by omega) hDD'
      calc 2 ^ (t + 1) * (Ab * D) ≤ 2 ^ (t + 1) * ((Cst + Ct * (Cst + 2) + Ab) * D') :=
            Nat.mul_le_mul_left _ this
        _ = 2 ^ (t + 1) * (Cst + Ct * (Cst + 2) + Ab) * D' := by ring
        _ ≤ _ := Nat.le_add_right _ _
    · obtain ⟨Z₁, hZ₁Z, hZ₁c⟩ := exists_quarter Z
      have hZ8 : Z.card ≤ 8 * Z₁.card := by omega
      have hCsZ : Cs ≤ Z₁.card := by omega
      have haZ₁ : a Z₁.card ≤ a Z.card := hamono (card_le_card hZ₁Z)
      obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁Z, -, hR₁Z,
        hdeg₁, -, hpd₁⟩ := hstage n ends Z₁ Z X D' hXr hXZ hZ8 hCsZ (by omega)
          (haZ₁.trans (Nat.le_add_left _ _)) (fun S hS => (hdeg S hS).trans hDD')
      have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
      have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ (Cst + 1) * D' :=
        fun S hS => (mdeg_mono _ hY₁R S).trans ((hdeg₁ S hS).trans
          (Nat.mul_le_mul_right _ (by omega)))
      obtain ⟨Bd₂, hBd₂, hrest⟩ := hCt n ends₁ Z₁ Y₁ ((Cst + 1) * D') hY₁r hY₁Z
        (by nlinarith) hdegY
      refine ⟨Cst * D' + Bd₂, ?_, refinerOut_of_stage (by omega) hZ₁Z hg₁ hends₁ hR₁f h₁ hY₁R
        hR₁Z hdeg₁ hpd₁ hrest⟩
      have h4 : 4 * Z₁.card ≤ Z.card := by omega
      set B := (Cst + Ab) * M
      have hB2 : 2 * (B * Z₁.card) ≤ B * Z.card := by
        calc 2 * (B * Z₁.card) ≤ 4 * (B * Z₁.card) := Nat.mul_le_mul_right _ (by norm_num)
          _ = B * (4 * Z₁.card) := by ring
          _ ≤ B * Z.card := Nat.mul_le_mul_left _ h4
      have hD₂ : (Cst + 1) * D' + a Z₁.card ≤ (Cst + 2) * D' := by
        have : a Z₁.card ≤ D' := haZ₁.trans (Nat.le_add_left _ _)
        nlinarith
      have hBd₂' : 2 ^ t * Bd₂ ≤ 2 ^ t * Ct * ((Cst + 2) * D') + B * Z₁.card :=
        hBd₂.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hD₂) _)
      have e1 : 2 ^ (t + 1) * (Cst * D' + Bd₂) = 2 ^ (t + 1) * Cst * D' + 2 * (2 ^ t * Bd₂) := by
        ring
      have e2 : 2 ^ (t + 1) * (Cst + Ct * (Cst + 2) + Ab) * D' =
          2 ^ (t + 1) * Cst * D' + 2 * (2 ^ t * Ct * ((Cst + 2) * D')) +
            2 ^ (t + 1) * Ab * D' := by ring
      rw [e1, e2]
      nlinarith [Nat.zero_le (2 ^ (t + 1) * Ab * D')]

end RefinedAbsorption.Dense
