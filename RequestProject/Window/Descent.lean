module
public import RequestProject.Dense.Native

/-!
# Descent through windows: the exact budget from one halving stage

The degree budget `C · max(D, n^{1-1/r} log n)` of Theorem 1.10 has the shape
"`D` plus `log n` windows, each costing `n^{1-1/r}`".  This file proves that this budget follows
from a **single halving stage** (`WindowStage q r Cst m₀ a`):

* the input is an `r`-multigraph `X` inside a window `U` (with `|U| > m₀`) with
  `Δ_{r-1}(X) ≤ D`;
* the output is a residual multi-refiner (relabelling the copies of `X` injectively) whose new
  copies and pieces have `(r-1)`-degrees at most `Cst · (D + a |U|)`, whose pieces contain at most
  one copy of `X`, and whose residue lies in a window `U'` with `2 |U'| ≤ |U|` and has
  `(r-1)`-degrees at most `Cst · a |U|`, **independently of `D`**.

Main results.

* `windowRefiner_of`: iterating the stage through the windows `U ⊇ U' ⊇ …` (each at most half the
  previous one) and finishing with the finite base case, every `X` inside `U` has a complete chain
  refiner with degree budget `A · D + K · (log₂ |U| + 1) · a |U|`.  The residue degree is reset to
  `Cst · a |U|` at each stage, so the constants do not grow with the number of stages; the loads
  of the `≤ log₂ |U| + 1` stages are summed.
* `windowTop_of`: the same on `Fin n` for an `r`-graph, as a strong multi-refiner.
* **`nativeStrongMultiRefiners_of_windowStage`**: if the stage holds with
  `a m = ⌈m^{1-1/r}⌉`, then `NativeStrongMultiRefiners q r` holds, i.e. strong multi-refiners with
  the exact budget `C · max(D, n^{1-1/r} log n)`.

The stage itself is **not** proved here for `r ≥ 3`.  It is the "one window" step of the refine
down construction (sparse residue in a window of half the size, at cost `O(D + m^{1-1/r})`).
-/

@[expose] public section

namespace RefinedAbsorption.Window

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense

/-- **One halving stage** (see the module docstring).  For `X` inside a window `U` with
`|U| > m₀` and `Δ_{r-1}(X) ≤ D`, there is a residual multi-refiner with constant `Cst`, new copies
and piece degrees `≤ Cst · (D + a |U|)`, pieces containing at most one copy of `X`, and residue
inside a window `U'` with `2 |U'| ≤ |U|` and `(r-1)`-degrees `≤ Cst · a |U|`. -/
def WindowStage (q r Cst m₀ : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n)) (U : Finset (Fin n))
    (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → m₀ < U.card → 1 ≤ D →
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R Y : Finset E') (𝒲 : Finset (Finset E')) (U' : Finset (Fin n)),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsResidualMultiRefiner q r Cst ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
      2 * U'.card ≤ U.card ∧ (∀ c ∈ Y, ends' c ⊆ U') ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' Y S ≤ Cst * a U.card) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ Cst * (D + a U.card)) ∧
      (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ Cst * (D + a U.card))

/-- Enlarging the reserve of a `RefinerOut`. -/
theorem refinerOut_mono_Z {q r C : ℕ} {n : ℕ} {E : Type} {ends : E → Finset (Fin n)}
    {Z Z' : Finset (Fin n)} {X : Finset E} {Bd : ℕ} (h : RefinerOut q r C ends Z X Bd)
    (hZ : Z ⊆ Z') : RefinerOut q r C ends Z' X Bd := by
  obtain ⟨E', i, g, ends', R, 𝒲, hg, he, hf, hch, hRZ, hd, hp⟩ := h
  exact ⟨E', i, g, ends', R, 𝒲, hg, he, hf, hch, fun c hc => (hRZ c hc).trans hZ, hd, hp⟩

/-- Halving a window lowers `log₂` by one. -/
theorem log_half_succ_le {m m' : ℕ} (hm : 2 ≤ m) (h : 2 * m' ≤ m) :
    Nat.log 2 m' + 1 ≤ Nat.log 2 m := by
  rcases Nat.eq_zero_or_pos m' with rfl | hpos
  · simp only [Nat.log_zero_right, zero_add]
    exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hm)
  · have : Nat.log 2 (m' * 2) = Nat.log 2 m' + 1 := Nat.log_mul_base (by norm_num) (by omega)
    rw [← this]
    exact Nat.log_mono_right (by omega)

/-- **Descent through windows** (see the module docstring). -/
theorem windowRefiner_of {q r Cst m₀ Cb Ab : ℕ} {a : ℕ → ℕ} (hCst : 1 ≤ Cst)
    (hamono : Monotone a) (ha1 : ∀ m, m₀ < m → 1 ≤ a m)
    (hstage : WindowStage q r Cst m₀ a)
    (hbase : ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → Z.card ≤ max m₀ 1 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r Cb ends Z X (Ab * D)) :
    ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends univ X
        ((Cst + Ab) * D + (Cst + (Cst + Ab) * Cst) * (Nat.log 2 U.card + 1) * a U.card) := by
  intro n
  set A := Cst + Ab with hA
  set K := Cst + A * Cst with hK
  suffices key : ∀ m, ∀ {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) (D : ℕ), U.card = m →
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      RefinerOut q r (Cst + Cb) ends univ X (A * D + K * (Nat.log 2 U.card + 1) * a U.card) from
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
    have hm2 : 2 ≤ U.card := by omega
    obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, U₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hU₁, hY₁U, hdegY,
      hdeg₁, -, hpd₁⟩ := hstage n ends U X D hXr hXU hm0 hD1 hdeg
    have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
    have ha := ha1 _ hm0
    have hlt : U₁.card < m := by omega
    have hrest := ih _ hlt ends₁ U₁ Y₁ (Cst * a U.card) rfl hY₁r hY₁U
      (Nat.mul_pos (by omega) (by omega)) hdegY
    refine (refinerOut_of_stage (Cst := Cst) (D := D + a U.card) (by omega) (subset_univ univ)
      hg₁ hends₁ hR₁f h₁ hY₁R (fun c _ => by simp) hdeg₁ hpd₁ hrest).mono le_rfl ?_
    have hlog : Nat.log 2 U₁.card + 1 ≤ Nat.log 2 U.card := log_half_succ_le hm2 hU₁
    have haU : a U₁.card ≤ a U.card := hamono (by omega)
    have h1 : K * (Nat.log 2 U₁.card + 1) * a U₁.card ≤ K * Nat.log 2 U.card * a U.card :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hlog) haU
    have e : A * D + K * (Nat.log 2 U.card + 1) * a U.card =
        A * D + K * Nat.log 2 U.card * a U.card + (Cst + A * Cst) * a U.card := by
      rw [hK]; ring
    have e2 : Cst * (D + a U.card) + (A * (Cst * a U.card) + K * (Nat.log 2 U₁.card + 1) *
        a U₁.card) = Cst * D + (Cst + A * Cst) * a U.card +
          K * (Nat.log 2 U₁.card + 1) * a U₁.card := by ring
    have hCD : Cst * D ≤ A * D := Nat.mul_le_mul_right _ (by omega)
    rw [e, e2]
    omega

/-- **Strong multi-refiners on `Fin n` from the window stage** (natural-number budget). -/
theorem windowTop_of {q r : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r) (hrq : r < q) {Cst m₀ : ℕ}
    (hCst : 1 ≤ Cst) (hamono : Monotone a) (ha1 : ∀ m, m₀ < m → 1 ≤ a m)
    (hstage : WindowStage q r Cst m₀ a) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n, m₀ < n → ∀ X : Finset (Finset (Fin n)),
      ∀ D : ℕ, IsRGraph r X → 1 ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ D) →
      ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (Xl R : Finset E)
        (𝒲 : Finset (Finset E)) (Bd : ℕ),
        Xl.image ends = X ∧ Bd ≤ C * (D + (Nat.log 2 n + 1) * a n) ∧
        IsStrongMultiRefiner q r C ends Xl Xl R 𝒲 Bd := by
  obtain ⟨Cb, Ab, hbase⟩ := baseRefiner q r hr hrq (max m₀ 1)
  have hwin := windowRefiner_of hCst hamono ha1 hstage hbase
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
  set Bd₂ := A * (Cst * a n) + K * (Nat.log 2 U₁.card + 1) * a U₁.card with hBd₂
  set Bd := D + (Cst * (D + a n) + Bd₂) with hBd
  have hendsX : ∀ e, ends₂ ((g₂ ∘ g₁) e) = e := fun e => by simp [hends₂, hends₁]
  have hBdle : Bd ≤ (3 * Cc + 1 + (1 + Cst + A * Cst + K)) * (D + (Nat.log 2 n + 1) * a n) := by
    have hlog : Nat.log 2 U₁.card + 1 ≤ Nat.log 2 n + 1 :=
      Nat.succ_le_succ (Nat.log_mono_right (by omega))
    have haU : a U₁.card ≤ a n := hamono (by omega)
    have h1 : K * (Nat.log 2 U₁.card + 1) * a U₁.card ≤ K * ((Nat.log 2 n + 1) * a n) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hlog haU)
    have h2 : a n ≤ (Nat.log 2 n + 1) * a n := Nat.le_mul_of_pos_left _ (by omega)
    set P := (Nat.log 2 n + 1) * a n
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

end RefinedAbsorption.Window
