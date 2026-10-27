module
public import RequestProject.Window.Native

/-!
# Descent through windows with a geometric potential

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Theorem 3.8 (iterating the
Better Refine Down Lemma 3.14 through windows of geometrically decreasing size).

`Window/Descent.lean` sums the costs `a |U|` of the `≤ log₂ n + 1` windows crudely, by
`(log₂ n + 1) · a n`.  In the proof of Theorem 3.8 the cost of a window of size `m` is
`m^{1-1/r} log m`, and these costs decrease geometrically along the windows, so that their sum is
`O(n^{1-1/r} log n)`.  This file proves the corresponding descent.

* `windowRefiner_pot`: if `Φ` is a potential with `Φ m' + a m ≤ Φ m` whenever `2 m' ≤ m` (and
  `m > m₀`), the windows cost at most `A · D + K · Φ |U|` in total.
* `windowTop_pot`: the same on `Fin n`, as a strong multi-refiner.
* `sharpCost r m = ⌈m^{1-1/r}⌉ · (⌊log₂ m⌋ + 1)` and its potential `sharpPot r`
  (`sharpPot r m = sharpCost r m + sharpPot r (m / 2)`), with
  `sharpPot r n ≤ 30 · n^{1-1/r} · log n` for `n ≥ 3` (`sharpPot_le`).
* **`nativeStrongMultiRefiners_of_windowStage_sharp`**: a window stage with cost `sharpCost r`
  gives `NativeStrongMultiRefiners q r`, i.e. the exact budget `C · max(D, n^{1-1/r} log n)`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Window

/-- **Descent through windows with a potential.** -/
theorem windowRefiner_pot {q r Cst m₀ Cb Ab : ℕ} {a Φ : ℕ → ℕ}
    (hpot : ∀ m m', m₀ < m → 2 * m' ≤ m → Φ m' + a m ≤ Φ m)
    (ha1 : ∀ m, m₀ < m → 1 ≤ a m)
    (hstage : WindowStage q r Cst m₀ a)
    (hbase : ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → Z.card ≤ max m₀ 1 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r Cb ends Z X (Ab * D)) (hCst : 1 ≤ Cst) :
    ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends univ X
        ((Cst + Ab) * D + (Cst + (Cst + Ab) * Cst) * Φ U.card) := by
  intro n
  set A := Cst + Ab with hA
  set K := Cst + A * Cst with hK
  suffices key : ∀ m, ∀ {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) (D : ℕ), U.card = m →
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends univ X (A * D + K * Φ U.card) from
    fun E _ ends U X D => key _ ends U X D rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro E _ ends U X D hUm hXr hXU hD1 hdeg
  by_cases hsmall : U.card ≤ max m₀ 1
  · refine refinerOut_mono_Z ((hbase n ends U X D hXr hXU hsmall hD1 hdeg).mono (by omega) ?_)
      (subset_univ _)
    have : Ab * D ≤ A * D := Nat.mul_le_mul_right _ (by omega)
    omega
  · have hm0 : m₀ < U.card := by omega
    obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, U₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hU₁, hY₁U, hdegY,
      hdeg₁, -, hpd₁⟩ := hstage n ends U X D hXr hXU hm0 hD1 hdeg
    have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
    have ha := ha1 _ hm0
    have hlt : U₁.card < m := by omega
    have hrest := ih _ hlt ends₁ U₁ Y₁ (Cst * a U.card) rfl hY₁r hY₁U
      (Nat.mul_pos (by omega) (by omega)) hdegY
    refine (refinerOut_of_stage (Cst := Cst) (D := D + a U.card) (by omega) (subset_univ univ)
      hg₁ hends₁ hR₁f h₁ hY₁R (fun c _ => by simp) hdeg₁ hpd₁ hrest).mono le_rfl ?_
    have hp := hpot U.card U₁.card hm0 hU₁
    have h1 : K * (Φ U₁.card + a U.card) ≤ K * Φ U.card := Nat.mul_le_mul_left _ hp
    have e2 : Cst * (D + a U.card) + (A * (Cst * a U.card) + K * Φ U₁.card) =
        Cst * D + (Cst + A * Cst) * a U.card + K * Φ U₁.card := by ring
    have e3 : K * (Φ U₁.card + a U.card) = K * Φ U₁.card + (Cst + A * Cst) * a U.card := by
      rw [hK]; ring
    have hCD : Cst * D ≤ A * D := Nat.mul_le_mul_right _ (by omega)
    rw [e2]
    omega

/-- **Strong multi-refiners on `Fin n` from the window stage, with a potential.** -/
theorem windowTop_pot {q r : ℕ} {a Φ : ℕ → ℕ} (hr : 2 ≤ r) (hrq : r < q) {Cst m₀ : ℕ}
    (hCst : 1 ≤ Cst) (hpot : ∀ m m', m₀ < m → 2 * m' ≤ m → Φ m' + a m ≤ Φ m)
    (ha1 : ∀ m, m₀ < m → 1 ≤ a m)
    (hstage : WindowStage q r Cst m₀ a) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n, m₀ < n → ∀ X : Finset (Finset (Fin n)),
      ∀ D : ℕ, IsRGraph r X → 1 ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ D) →
      ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (Xl R : Finset E)
        (𝒲 : Finset (Finset E)) (Bd : ℕ),
        Xl.image ends = X ∧ Bd ≤ C * (D + Φ n) ∧
        IsStrongMultiRefiner q r C ends Xl Xl R 𝒲 Bd := by
  obtain ⟨Cb, Ab, hbase⟩ := baseRefiner q r hr hrq (max m₀ 1)
  have hwin := windowRefiner_pot hpot ha1 hstage hbase hCst
  set A := Cst + Ab with hA
  set K := Cst + A * Cst with hK
  set Cc := Cst + Cb with hCc
  refine ⟨3 * Cc + 1 + (1 + Cst + A * Cst + K), by omega, fun n hn X D hX hD1 hdeg => ?_⟩
  have hXr : MIsRGraph r (id : Finset (Fin n) → Finset (Fin n)) X := hX
  have hn' : m₀ < (univ : Finset (Fin n)).card := by rw [card_univ, Fintype.card_fin]; exact hn
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, U₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hU₁, hY₁U, hdegY,
    hdeg₁, hone₁, hpd₁⟩ := hstage n id univ X D hXr (fun _ _ => subset_univ _) hn' hD1 hdeg
  rw [card_univ, Fintype.card_fin] at hU₁ hdegY hdeg₁ hpd₁
  have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  have ha := ha1 _ hn
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, -, hdeg₂, hpd₂⟩ :=
    hwin n ends₁ U₁ Y₁ (Cst * a n) hY₁r hY₁U (Nat.mul_pos (by omega) (by omega)) hdegY
  have hpre := IsChainRefiner.prepend_relabel h₁ hY₁R (Nat.le_add_right Cst Cb) g₂ hg₂ hends₂ h₂
    hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂.base hR₂f
  rw [image_image] at hpre hone
  set Bd₂ := A * (Cst * a n) + K * Φ U₁.card with hBd₂
  set Bd := D + (Cst * (D + a n) + Bd₂) with hBd
  have hendsX : ∀ e, ends₂ ((g₂ ∘ g₁) e) = e := fun e => by simp [hends₂, hends₁]
  have hBdle : Bd ≤ (3 * Cc + 1 + (1 + Cst + A * Cst + K)) * (D + Φ n) := by
    have hp := hpot n U₁.card hn hU₁
    have hp0 := hpot n 0 hn (by omega)
    set P := Φ n
    have h1 : K * Φ U₁.card ≤ K * P := Nat.mul_le_mul_left _ (by omega)
    have h2 : a n ≤ P := by omega
    have hAC : A * (Cst * a n) ≤ (A * Cst) * P := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_left _ h2
    have hCP : Cst * a n ≤ Cst * P := Nat.mul_le_mul_left _ h2
    have step1 : Bd ≤ (1 + Cst + A * Cst + K) * (D + P) := by
      rw [hBd, hBd₂]
      have e : (1 + Cst + A * Cst + K) * (D + P) =
          D + Cst * D + Cst * P + (A * Cst) * P + K * P + (P + (A * Cst) * D + K * D) := by ring
      rw [e]
      have : Cst * (D + a n) = Cst * D + Cst * a n := by ring
      omega
    exact step1.trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨E₂, inferInstance, ends₂, X.image (g₂ ∘ g₁), R₁.image g₂ ∪ R₂,
    𝒲₁.image (image g₂) ∪ 𝒲₂, Bd, ?_, hBdle, ?_⟩
  · rw [image_image]
    have : ends₂ ∘ (g₂ ∘ g₁) = id := funext hendsX
    rw [this, image_id]
  · have hC1 : 1 ≤ 3 * Cc + 1 + (1 + Cst + A * Cst + K) := by omega
    exact
    { refiner := hpre.base.mono (by omega)
      keep := subset_rfl
      inj := by
        intro x hx y hy hxy
        obtain ⟨u, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
        obtain ⟨v, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
        rw [hendsX, hendsX] at hxy
        rw [hxy]
      oneX := hone
      degX := fun S hS => by
        rw [mdeg_image_eq (A := X) (fun c _ => hendsX c) (hg₂.comp hg₁).injOn subset_rfl]
        exact (hdeg S hS).trans (by omega)
      degR := fun S hS => by
        refine (Dense.mdeg_union_le _ _ _ S).trans ?_
        rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
        have := hdeg₁ S hS
        have := hdeg₂ S hS
        have : Bd ≤ (3 * Cc + 1 + (1 + Cst + A * Cst + K)) * Bd := Nat.le_mul_of_pos_left _ hC1
        omega
      pieceDeg := fun S hS => by
        refine (pdeg_union_le _ _ _ S).trans ?_
        have := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
        have := hpd₂ S hS
        have : Bd ≤ (3 * Cc + 1 + (1 + Cst + A * Cst + K)) * Bd := Nat.le_mul_of_pos_left _ hC1
        unfold pdeg at *
        omega }

/-! ### Window stages preserving a multiplicity bound -/

/-- **One halving stage for multigraphs of multiplicity at most `M`**: as `WindowStage`, but the
input is assumed to have multiplicity at most `M` and the residue again has multiplicity at most
`M`. -/
def WindowStageM (q r M Cst m₀ : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n)) (U : Finset (Fin n))
    (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → m₀ < U.card → 1 ≤ D →
    (∀ e, mult ends X e ≤ M) →
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R Y : Finset E') (𝒲 : Finset (Finset E')) (U' : Finset (Fin n)),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsResidualMultiRefiner q r Cst ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
      2 * U'.card ≤ U.card ∧ (∀ c ∈ Y, ends' c ⊆ U') ∧ (∀ e, mult ends' Y e ≤ M) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' Y S ≤ Cst * a U.card) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ Cst * (D + a U.card)) ∧
      (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ Cst * (D + a U.card))

/-- **Descent through windows with a potential**, for multigraphs of bounded multiplicity. -/
theorem windowRefinerM_pot {q r M Cst m₀ Cb Ab : ℕ} {a Φ : ℕ → ℕ}
    (hpot : ∀ m m', m₀ < m → 2 * m' ≤ m → Φ m' + a m ≤ Φ m)
    (ha1 : ∀ m, m₀ < m → 1 ≤ a m)
    (hstage : WindowStageM q r M Cst m₀ a)
    (hbase : ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → Z.card ≤ max m₀ 1 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r Cb ends Z X (Ab * D)) (hCst : 1 ≤ Cst) :
    ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → 1 ≤ D → (∀ e, mult ends X e ≤ M) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends univ X
        ((Cst + Ab) * D + (Cst + (Cst + Ab) * Cst) * Φ U.card) := by
  intro n
  set A := Cst + Ab with hA
  set K := Cst + A * Cst with hK
  suffices key : ∀ m, ∀ {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) (D : ℕ), U.card = m →
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → 1 ≤ D → (∀ e, mult ends X e ≤ M) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends univ X (A * D + K * Φ U.card) from
    fun E _ ends U X D => key _ ends U X D rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro E _ ends U X D hUm hXr hXU hD1 hXm hdeg
  by_cases hsmall : U.card ≤ max m₀ 1
  · refine refinerOut_mono_Z ((hbase n ends U X D hXr hXU hsmall hD1 hdeg).mono (by omega) ?_)
      (subset_univ _)
    have : Ab * D ≤ A * D := Nat.mul_le_mul_right _ (by omega)
    omega
  · have hm0 : m₀ < U.card := by omega
    obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, U₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hU₁, hY₁U, hY₁m,
      hdegY, hdeg₁, -, hpd₁⟩ := hstage n ends U X D hXr hXU hm0 hD1 hXm hdeg
    have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
    have ha := ha1 _ hm0
    have hlt : U₁.card < m := by omega
    have hrest := ih _ hlt ends₁ U₁ Y₁ (Cst * a U.card) rfl hY₁r hY₁U
      (Nat.mul_pos (by omega) (by omega)) hY₁m hdegY
    refine (refinerOut_of_stage (Cst := Cst) (D := D + a U.card) (by omega) (subset_univ univ)
      hg₁ hends₁ hR₁f h₁ hY₁R (fun c _ => by simp) hdeg₁ hpd₁ hrest).mono le_rfl ?_
    have hp := hpot U.card U₁.card hm0 hU₁
    have h1 : K * (Φ U₁.card + a U.card) ≤ K * Φ U.card := Nat.mul_le_mul_left _ hp
    have e2 : Cst * (D + a U.card) + (A * (Cst * a U.card) + K * Φ U₁.card) =
        Cst * D + (Cst + A * Cst) * a U.card + K * Φ U₁.card := by ring
    have e3 : K * (Φ U₁.card + a U.card) = K * Φ U₁.card + (Cst + A * Cst) * a U.card := by
      rw [hK]; ring
    have hCD : Cst * D ≤ A * D := Nat.mul_le_mul_right _ (by omega)
    rw [e2]
    omega

/-- **Strong multi-refiners on `Fin n` from the window stage with bounded multiplicity, with a
potential.** -/
theorem windowTopM_pot {q r : ℕ} {a Φ : ℕ → ℕ} (hr : 2 ≤ r) (hrq : r < q) {M Cst m₀ : ℕ}
    (hM : 1 ≤ M) (hCst : 1 ≤ Cst) (hpot : ∀ m m', m₀ < m → 2 * m' ≤ m → Φ m' + a m ≤ Φ m)
    (ha1 : ∀ m, m₀ < m → 1 ≤ a m)
    (hstage : WindowStageM q r M Cst m₀ a) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n, m₀ < n → ∀ X : Finset (Finset (Fin n)),
      ∀ D : ℕ, IsRGraph r X → 1 ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ D) →
      ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (Xl R : Finset E)
        (𝒲 : Finset (Finset E)) (Bd : ℕ),
        Xl.image ends = X ∧ Bd ≤ C * (D + Φ n) ∧
        IsStrongMultiRefiner q r C ends Xl Xl R 𝒲 Bd := by
  obtain ⟨Cb, Ab, hbase⟩ := baseRefiner q r hr hrq (max m₀ 1)
  have hwin := windowRefinerM_pot hpot ha1 hstage hbase hCst
  set A := Cst + Ab with hA
  set K := Cst + A * Cst with hK
  set Cc := Cst + Cb with hCc
  refine ⟨3 * Cc + 1 + (1 + Cst + A * Cst + K), by omega, fun n hn X D hX hD1 hdeg => ?_⟩
  have hXr : MIsRGraph r (id : Finset (Fin n) → Finset (Fin n)) X := hX
  have hXm : ∀ e, mult (id : Finset (Fin n) → Finset (Fin n)) X e ≤ M := by
    intro e
    refine le_trans (card_le_one.2 fun x hx y hy => ?_) hM
    rw [mem_filter] at hx hy
    exact hx.2.trans hy.2.symm
  have hn' : m₀ < (univ : Finset (Fin n)).card := by rw [card_univ, Fintype.card_fin]; exact hn
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, U₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hU₁, hY₁U, hY₁m, hdegY,
    hdeg₁, hone₁, hpd₁⟩ := hstage n id univ X D hXr (fun _ _ => subset_univ _) hn' hD1 hXm hdeg
  rw [card_univ, Fintype.card_fin] at hU₁ hdegY hdeg₁ hpd₁
  have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  have ha := ha1 _ hn
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, -, hdeg₂, hpd₂⟩ :=
    hwin n ends₁ U₁ Y₁ (Cst * a n) hY₁r hY₁U (Nat.mul_pos (by omega) (by omega)) hY₁m hdegY
  have hpre := IsChainRefiner.prepend_relabel h₁ hY₁R (Nat.le_add_right Cst Cb) g₂ hg₂ hends₂ h₂
    hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂.base hR₂f
  rw [image_image] at hpre hone
  set Bd₂ := A * (Cst * a n) + K * Φ U₁.card with hBd₂
  set Bd := D + (Cst * (D + a n) + Bd₂) with hBd
  have hendsX : ∀ e, ends₂ ((g₂ ∘ g₁) e) = e := fun e => by simp [hends₂, hends₁]
  have hBdle : Bd ≤ (3 * Cc + 1 + (1 + Cst + A * Cst + K)) * (D + Φ n) := by
    have hp := hpot n U₁.card hn hU₁
    have hp0 := hpot n 0 hn (by omega)
    set P := Φ n
    have h1 : K * Φ U₁.card ≤ K * P := Nat.mul_le_mul_left _ (by omega)
    have h2 : a n ≤ P := by omega
    have hAC : A * (Cst * a n) ≤ (A * Cst) * P := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_left _ h2
    have hCP : Cst * a n ≤ Cst * P := Nat.mul_le_mul_left _ h2
    have step1 : Bd ≤ (1 + Cst + A * Cst + K) * (D + P) := by
      rw [hBd, hBd₂]
      have e : (1 + Cst + A * Cst + K) * (D + P) =
          D + Cst * D + Cst * P + (A * Cst) * P + K * P + (P + (A * Cst) * D + K * D) := by ring
      rw [e]
      have : Cst * (D + a n) = Cst * D + Cst * a n := by ring
      omega
    exact step1.trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨E₂, inferInstance, ends₂, X.image (g₂ ∘ g₁), R₁.image g₂ ∪ R₂,
    𝒲₁.image (image g₂) ∪ 𝒲₂, Bd, ?_, hBdle, ?_⟩
  · rw [image_image]
    have : ends₂ ∘ (g₂ ∘ g₁) = id := funext hendsX
    rw [this, image_id]
  · have hC1 : 1 ≤ 3 * Cc + 1 + (1 + Cst + A * Cst + K) := by omega
    exact
    { refiner := hpre.base.mono (by omega)
      keep := subset_rfl
      inj := by
        intro x hx y hy hxy
        obtain ⟨u, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
        obtain ⟨v, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
        rw [hendsX, hendsX] at hxy
        rw [hxy]
      oneX := hone
      degX := fun S hS => by
        rw [mdeg_image_eq (A := X) (fun c _ => hendsX c) (hg₂.comp hg₁).injOn subset_rfl]
        exact (hdeg S hS).trans (by omega)
      degR := fun S hS => by
        refine (Dense.mdeg_union_le _ _ _ S).trans ?_
        rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
        have := hdeg₁ S hS
        have := hdeg₂ S hS
        have : Bd ≤ (3 * Cc + 1 + (1 + Cst + A * Cst + K)) * Bd := Nat.le_mul_of_pos_left _ hC1
        omega
      pieceDeg := fun S hS => by
        refine (pdeg_union_le _ _ _ S).trans ?_
        have := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
        have := hpd₂ S hS
        have : Bd ≤ (3 * Cc + 1 + (1 + Cst + A * Cst + K)) * Bd := Nat.le_mul_of_pos_left _ hC1
        unfold pdeg at *
        omega }

/-! ### The sharp cost and its potential -/

/-- The cost of one window of size `m` in the proof of Theorem 3.8:
`⌈m^{1-1/r}⌉ · (⌊log₂ m⌋ + 1)`. -/
noncomputable def sharpCost (r m : ℕ) : ℕ := winCost r m * (Nat.log 2 m + 1)

/-- The potential of the sharp cost: `sharpPot r m = Σ_j sharpCost r ⌊m / 2^j⌋`. -/
noncomputable def sharpPot (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | (m + 1) => sharpCost r (m + 1) + sharpPot r ((m + 1) / 2)

theorem sharpPot_succ (r m : ℕ) :
    sharpPot r (m + 1) = sharpCost r (m + 1) + sharpPot r ((m + 1) / 2) := by
  rw [sharpPot]

theorem sharpCost_mono {r : ℕ} (hr : 1 ≤ r) : Monotone (sharpCost r) := by
  intro m m' h
  unfold sharpCost
  exact Nat.mul_le_mul (winCost_mono hr h) (Nat.succ_le_succ (Nat.log_mono_right h))

theorem winCost_le_sharpCost (r m : ℕ) : winCost r m ≤ sharpCost r m :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

theorem one_le_sharpCost (r : ℕ) {m : ℕ} (hm : 1 ≤ m) : 1 ≤ sharpCost r m :=
  (one_le_winCost r hm).trans (winCost_le_sharpCost r m)

theorem sharpPot_mono {r : ℕ} (hr : 1 ≤ r) : Monotone (sharpPot r) := by
  suffices h : ∀ m, ∀ m' ≤ m, sharpPot r m' ≤ sharpPot r m from fun a b hab => h b a hab
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro m' hm'
  rcases Nat.eq_zero_or_pos m' with rfl | hm'0
  · simp [sharpPot]
  obtain ⟨k', rfl⟩ : ∃ k', m' = k' + 1 := ⟨m' - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [sharpPot_succ, sharpPot_succ]
  exact Nat.add_le_add (sharpCost_mono hr hm')
    (ih _ (by omega) _ (Nat.div_le_div_right hm'))

/-- The potential inequality: `sharpPot r m' + sharpCost r m ≤ sharpPot r m` if `2 m' ≤ m`. -/
theorem sharpPot_step {r : ℕ} (hr : 1 ≤ r) {m m' : ℕ} (hm : 1 ≤ m) (h : 2 * m' ≤ m) :
    sharpPot r m' + sharpCost r m ≤ sharpPot r m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [sharpPot_succ]
  have := sharpPot_mono hr (show m' ≤ (k + 1) / 2 by omega)
  omega

/-! ### The real-number bound on the potential -/

lemma half_rpow_le {r : ℕ} (hr : 2 ≤ r) : (1 / 2 : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ 3 / 4 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hθ : (1 / 2 : ℝ) ≤ 1 - 1 / (r : ℝ) := by
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc (1 / 2 : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hθ
    _ ≤ 3 / 4 := by
        rw [← Real.sqrt_eq_rpow]
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num

/-- `sharpPot r m ≤ (⌊log₂ m⌋ + 1) · (4 m^{1-1/r} + ⌊log₂ m⌋ + 1)`. -/
theorem sharpPot_le_aux {r : ℕ} (hr : 2 ≤ r) :
    ∀ m : ℕ, 1 ≤ m → (sharpPot r m : ℝ) ≤
      ((Nat.log 2 m : ℝ) + 1) * (4 * (m : ℝ) ^ (1 - 1 / (r : ℝ)) + (Nat.log 2 m : ℝ) + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [sharpPot_succ]
  set m := k + 1 with hmdef
  set θ := 1 - 1 / (r : ℝ) with hθ
  have hθ0 : 0 ≤ θ := exponent_nonneg (by omega)
  set L : ℝ := (Nat.log 2 m : ℝ) with hL
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmθ : 1 ≤ (m : ℝ) ^ θ := Real.one_le_rpow hm1 hθ0
  -- the cost of the first window
  have hcost : (sharpCost r m : ℝ) ≤ ((m : ℝ) ^ θ + 1) * (L + 1) := by
    unfold sharpCost winCost
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ (m : ℝ) ^ θ by positivity)
    gcongr
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · -- `m = 1`
    have hm1' : m = 1 := by omega
    have : m / 2 = 0 := by omega
    rw [this]
    simp only [sharpPot, add_zero]
    have hL' : L = 0 := by rw [hL, hm1']; simp
    rw [hL'] at hcost ⊢
    nlinarith
  · set m' := m / 2 with hm'
    have hm'1 : 1 ≤ m' := by omega
    have hrec := ih m' (by omega) hm'1
    have hlog' : Nat.log 2 m' + 1 = Nat.log 2 m := by
      rw [hm', Nat.log_div_base]
      have : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) (by simpa using hm2)
      omega
    have hL' : (Nat.log 2 m' : ℝ) = L - 1 := by
      rw [hL, ← hlog']; push_cast; ring
    rw [hL'] at hrec
    have hm'le : (m' : ℝ) ≤ (m : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : m' * 2 ≤ m)
    have hpow : (m' : ℝ) ^ θ ≤ 3 / 4 * (m : ℝ) ^ θ := by
      calc (m' : ℝ) ^ θ ≤ ((m : ℝ) / 2) ^ θ :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hm'le hθ0
        _ = (1 / 2 : ℝ) ^ θ * (m : ℝ) ^ θ := by
            rw [div_eq_mul_one_div, Real.mul_rpow (by positivity) (by norm_num), mul_comm]
        _ ≤ 3 / 4 * (m : ℝ) ^ θ := by
            gcongr
            exact half_rpow_le hr
    have hL1 : 1 ≤ L := by
      rw [hL]; exact_mod_cast Nat.le_log_of_pow_le (by norm_num) (by simpa using hm2)
    push_cast
    calc (sharpCost r m : ℝ) + (sharpPot r m' : ℝ)
        ≤ ((m : ℝ) ^ θ + 1) * (L + 1) + (L - 1 + 1) * (4 * (m' : ℝ) ^ θ + (L - 1) + 1) :=
          add_le_add hcost hrec
      _ ≤ ((m : ℝ) ^ θ + 1) * (L + 1) + L * (3 * (m : ℝ) ^ θ + L) := by
          have : (L - 1 + 1) = L := by ring
          rw [this]
          have hin : 4 * (m' : ℝ) ^ θ + (L - 1) + 1 ≤ 3 * (m : ℝ) ^ θ + L := by linarith
          have := mul_le_mul_of_nonneg_left hin hL0
          linarith
      _ ≤ (L + 1) * (4 * (m : ℝ) ^ θ + L + 1) := by nlinarith

/-- **The potential is `O(n^{1-1/r} log n)`**: `sharpPot r n ≤ 30 · n^{1-1/r} · log n`
for `n ≥ 3`. -/
theorem sharpPot_le {r n : ℕ} (hr : 2 ≤ r) (hn : 3 ≤ n) :
    (sharpPot r n : ℝ) ≤ 30 * ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) := by
  have h := sharpPot_le_aux hr n (by omega)
  set θ := 1 - 1 / (r : ℝ) with hθ
  have hθ0 : 0 ≤ θ := exponent_nonneg (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnθ : 1 ≤ (n : ℝ) ^ θ := Real.one_le_rpow hn1 hθ0
  have hlog := log2_succ_le hn
  push_cast at hlog
  set L : ℝ := (Nat.log 2 n : ℝ)
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hlogn : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- `L + 1 ≤ n^θ`: since `θ ≥ 1/2` and `L + 1 ≤ √n`
  have hLθ : L + 1 ≤ 2 * (n : ℝ) ^ θ := by
    have hθ2 : (1 / 2 : ℝ) ≤ θ := by
      have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      rw [hθ, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]; nlinarith
    have hsq : Real.sqrt n ≤ (n : ℝ) ^ θ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hn1 hθ2
    -- `2^L ≤ n`, and `L + 1 ≤ 2 · 2^{L/2}`
    have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hk : ∀ k : ℕ, ((k : ℝ) + 1) ^ 2 ≤ 4 * 2 ^ k := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        push_cast
        rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · interval_cases k <;> norm_num
        · have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
          have e : ((k : ℝ) + 1 + 1) ^ 2 = ((k : ℝ) + 1) ^ 2 + 2 * (k : ℝ) + 3 := by ring
          rw [e, pow_succ (2 : ℝ) k]
          nlinarith
    have h1 : (L + 1) ^ 2 ≤ 4 * n := by
      have := hk (Nat.log 2 n)
      push_cast at hpow
      linarith
    have h2 : L + 1 ≤ 2 * Real.sqrt n := by
      have hs : (2 * Real.sqrt n) ^ 2 = 4 * n := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
      nlinarith [Real.sqrt_nonneg (n : ℝ)]
    linarith
  calc (sharpPot r n : ℝ) ≤ (L + 1) * (4 * (n : ℝ) ^ θ + L + 1) := h
    _ ≤ (L + 1) * (6 * (n : ℝ) ^ θ) := by gcongr; linarith
    _ ≤ (3 * Real.log n) * (6 * (n : ℝ) ^ θ) := by gcongr
    _ ≤ 30 * ((n : ℝ) ^ θ * Real.log n) := by nlinarith

/-- **`NativeStrongMultiRefiners q r` from a window stage with the sharp cost.**  If every
`r`-multigraph inside a window `U` (`|U| > m₀`) with `Δ_{r-1} ≤ D` has a residual multi-refiner
of cost `Cst · (D + ⌈|U|^{1-1/r}⌉ (⌊log₂ |U|⌋ + 1))` whose residue lies in a window of at most
half the size, with `Δ_{r-1} ≤ Cst · ⌈|U|^{1-1/r}⌉ (⌊log₂ |U|⌋ + 1)`, then strong multi-refiners
with the exact budget `C · max(D, n^{1-1/r} log n)` exist.  (This is how Theorem 3.8 follows from
the Better Refine Down Lemma 3.14.) -/
theorem nativeStrongMultiRefiners_of_windowStage_sharp {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (h : ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStage q r Cst m₀ (sharpCost r)) :
    NativeStrongMultiRefiners q r := by
  obtain ⟨Cst, m₀, hCst, hstage⟩ := h
  obtain ⟨C, hC, htop⟩ := windowTop_pot hr hrq hCst
    (fun m m' hm h2 => sharpPot_step (by omega) (by omega) h2)
    (fun m hm => one_le_sharpCost r (by omega)) hstage
  refine ⟨32 * C, by omega, max (m₀ + 1) 3, ?_⟩
  intro n hn X D hX hXD _
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have hnm : m₀ < n := by have := le_of_max_le_left hn; omega
  set Dn := ⌊D⌋₊ + 1 with hDn
  have hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ Dn := by
    intro S hS
    have h1 := hXD S (by omega)
    have : deg X S ≤ ⌊D⌋₊ := Nat.le_floor h1
    omega
  obtain ⟨E, _, ends, Xl, R, 𝒲, Bd, hXl, hBd, hS⟩ := htop n hnm X Dn hX (by omega) hdeg
  refine ⟨E, inferInstance, ends, Xl, Xl, R, 𝒲, Bd, hXl, ?_,
    OddGrid.IsStrongMultiRefiner.mono' hS (by omega)⟩
  set Lg := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n with hLg
  have hL1 : 1 ≤ Lg := HyperPlan.one_le_rpow_log (by omega) hn3
  set M := max D Lg with hM
  have hM1 : 1 ≤ M := hL1.trans (le_max_right _ _)
  have hDnM : (Dn : ℝ) ≤ 2 * M := by
    have hfl : (⌊D⌋₊ : ℝ) ≤ M := by
      rcases le_or_gt 0 D with hD0 | hD0
      · exact (Nat.floor_le hD0).trans (le_max_left _ _)
      · rw [Nat.floor_of_nonpos hD0.le]; simp only [Nat.cast_zero]; linarith
    rw [hDn]; push_cast; linarith
  have hP : (sharpPot r n : ℝ) ≤ 30 * M :=
    (sharpPot_le hr hn3).trans (by linarith [le_max_right D Lg])
  have hBd' : (Bd : ℝ) ≤ C * ((Dn : ℝ) + (sharpPot r n : ℝ)) := by exact_mod_cast hBd
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  calc (Bd : ℝ) ≤ C * ((Dn : ℝ) + (sharpPot r n : ℝ)) := hBd'
    _ ≤ C * (2 * M + 30 * M) := by gcongr
    _ = ((32 * C : ℕ) : ℝ) * M := by push_cast; ring

/-- **`NativeStrongMultiRefiners q r` from a window stage with the sharp cost, for multigraphs
of bounded multiplicity** (as `nativeStrongMultiRefiners_of_windowStage_sharp`). -/
theorem nativeStrongMultiRefiners_of_windowStageM_sharp {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (h : ∃ M Cst m₀ : ℕ, 1 ≤ M ∧ 1 ≤ Cst ∧ WindowStageM q r M Cst m₀ (sharpCost r)) :
    NativeStrongMultiRefiners q r := by
  obtain ⟨M, Cst, m₀, hM, hCst, hstage⟩ := h
  obtain ⟨C, hC, htop⟩ := windowTopM_pot hr hrq hM hCst
    (fun m m' hm h2 => sharpPot_step (by omega) (by omega) h2)
    (fun m hm => one_le_sharpCost r (by omega)) hstage
  refine ⟨32 * C, by omega, max (m₀ + 1) 3, ?_⟩
  intro n hn X D hX hXD _
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have hnm : m₀ < n := by have := le_of_max_le_left hn; omega
  set Dn := ⌊D⌋₊ + 1 with hDn
  have hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ Dn := by
    intro S hS
    have h1 := hXD S (by omega)
    have : deg X S ≤ ⌊D⌋₊ := Nat.le_floor h1
    omega
  obtain ⟨E, _, ends, Xl, R, 𝒲, Bd, hXl, hBd, hS⟩ := htop n hnm X Dn hX (by omega) hdeg
  refine ⟨E, inferInstance, ends, Xl, Xl, R, 𝒲, Bd, hXl, ?_,
    OddGrid.IsStrongMultiRefiner.mono' hS (by omega)⟩
  set Lg := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n with hLg
  have hL1 : 1 ≤ Lg := HyperPlan.one_le_rpow_log (by omega) hn3
  set M' := max D Lg with hM'
  have hM1 : 1 ≤ M' := hL1.trans (le_max_right _ _)
  have hDnM : (Dn : ℝ) ≤ 2 * M' := by
    have hfl : (⌊D⌋₊ : ℝ) ≤ M' := by
      rcases le_or_gt 0 D with hD0 | hD0
      · exact (Nat.floor_le hD0).trans (le_max_left _ _)
      · rw [Nat.floor_of_nonpos hD0.le]; simp only [Nat.cast_zero]; linarith
    rw [hDn]; push_cast; linarith
  have hP : (sharpPot r n : ℝ) ≤ 30 * M' :=
    (sharpPot_le hr hn3).trans (by linarith [le_max_right D Lg])
  have hBd' : (Bd : ℝ) ≤ C * ((Dn : ℝ) + (sharpPot r n : ℝ)) := by exact_mod_cast hBd
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  calc (Bd : ℝ) ≤ C * ((Dn : ℝ) + (sharpPot r n : ℝ)) := hBd'
    _ ≤ C * (2 * M' + 30 * M') := by gcongr
    _ = ((32 * C : ℕ) : ℝ) * M' := by push_cast; ring

end RefinedAbsorption.Sharp
