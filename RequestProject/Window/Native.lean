module
public import RequestProject.Window.Descent
public import RequestProject.HyperPlan.Native

/-!
# The exact budget of Theorem 1.10 from one window stage

* `winCost r m = ⌈m^{1-1/r}⌉`: the cost of one window of size `m`.
* **`nativeStrongMultiRefiners_of_windowStage`**: if the halving stage `WindowStage q r Cst m₀`
  holds with cost `winCost r`, then `NativeStrongMultiRefiners q r` holds (strong multi-refiners
  with degree budget `C · max(D, n^{1-1/r} log n)`).  The `log n` comes from the `≤ log₂ n + 1`
  windows, each costing `⌈n^{1-1/r}⌉`.
* `refinerAbsorbersFor_of_windowStage`: hence `RefinerAbsorbersFor q r` (Theorem 1.10 in the form
  used by the project).
-/

@[expose] public section

namespace RefinedAbsorption.Window

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.HyperPlan

/-- The cost of one window of size `m`: `⌈m^{1-1/r}⌉`. -/
noncomputable def winCost (r m : ℕ) : ℕ := ⌈(m : ℝ) ^ (1 - 1 / (r : ℝ))⌉₊

lemma exponent_nonneg {r : ℕ} (hr : 1 ≤ r) : 0 ≤ 1 - 1 / (r : ℝ) := by
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr
  rw [sub_nonneg, div_le_one (by linarith)]; exact this

theorem winCost_mono {r : ℕ} (hr : 1 ≤ r) : Monotone (winCost r) := by
  intro m m' h
  unfold winCost
  exact Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h)
    (exponent_nonneg hr))

theorem one_le_winCost (r : ℕ) {m : ℕ} (hm : 1 ≤ m) : 1 ≤ winCost r m := by
  unfold winCost
  rw [Nat.one_le_ceil_iff]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem winCost_le {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) :
    (winCost r n : ℝ) ≤ 2 * (n : ℝ) ^ (1 - 1 / (r : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ (n : ℝ) ^ (1 - 1 / (r : ℝ)) := Real.one_le_rpow hn1 (exponent_nonneg hr)
  have := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (1 - 1 / (r : ℝ)) by linarith)
  unfold winCost
  linarith

theorem log2_succ_le {n : ℕ} (hn : 3 ≤ n) : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk0 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- **`NativeStrongMultiRefiners q r` from one window stage.**  If, for some `Cst ≥ 1` and `m₀`,
every `r`-multigraph inside a window `U` (`|U| > m₀`) with `Δ_{r-1} ≤ D` has a residual
multi-refiner of cost `Cst · (D + ⌈|U|^{1-1/r}⌉)` whose residue lies in a window of at most half
the size with `Δ_{r-1} ≤ Cst · ⌈|U|^{1-1/r}⌉` (`WindowStage`), then strong multi-refiners with
the exact budget `C · max(D, n^{1-1/r} log n)` exist. -/
theorem nativeStrongMultiRefiners_of_windowStage {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (h : ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStage q r Cst m₀ (winCost r)) :
    NativeStrongMultiRefiners q r := by
  obtain ⟨Cst, m₀, hCst, hstage⟩ := h
  obtain ⟨C, hC, htop⟩ := windowTop_of hr hrq hCst (winCost_mono (by omega))
    (fun m hm => one_le_winCost r (by omega)) hstage
  refine ⟨8 * C, by omega, max (m₀ + 1) 3, ?_⟩
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
  refine ⟨E, inferInstance, ends, Xl, Xl, R, 𝒲, Bd, hXl, ?_, OddGrid.IsStrongMultiRefiner.mono' hS (by omega)⟩
  set Lg := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n with hLg
  have hL1 : 1 ≤ Lg := one_le_rpow_log (by omega) hn3
  set M := max D Lg with hM
  have hM1 : 1 ≤ M := hL1.trans (le_max_right _ _)
  have hDnM : (Dn : ℝ) ≤ 2 * M := by
    have hfl : (⌊D⌋₊ : ℝ) ≤ M := by
      rcases le_or_gt 0 D with hD0 | hD0
      · exact (Nat.floor_le hD0).trans (le_max_left _ _)
      · rw [Nat.floor_of_nonpos hD0.le]; simp only [Nat.cast_zero]; linarith
    rw [hDn]; push_cast; linarith
  have hpow0 : 0 ≤ (n : ℝ) ^ (1 - 1 / (r : ℝ)) := by positivity
  have hP : (((Nat.log 2 n + 1) * winCost r n : ℕ) : ℝ) ≤ 6 * M := by
    rw [Nat.cast_mul]
    have h1 := log2_succ_le hn3
    have h2 := winCost_le (r := r) (by omega) (show 1 ≤ n by omega)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    calc ((Nat.log 2 n + 1 : ℕ) : ℝ) * (winCost r n : ℝ)
        ≤ (3 * Real.log n) * (2 * (n : ℝ) ^ (1 - 1 / (r : ℝ))) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ = 6 * Lg := by rw [hLg]; ring
      _ ≤ 6 * M := by linarith [le_max_right D Lg]
  have hBd' : (Bd : ℝ) ≤ C * ((Dn : ℝ) + (((Nat.log 2 n + 1) * winCost r n : ℕ) : ℝ)) := by
    exact_mod_cast hBd
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  calc (Bd : ℝ) ≤ C * ((Dn : ℝ) + (((Nat.log 2 n + 1) * winCost r n : ℕ) : ℝ)) := hBd'
    _ ≤ C * (2 * M + 6 * M) := by gcongr
    _ = ((8 * C : ℕ) : ℝ) * M := by push_cast; ring

/-- **Theorem 1.10 (in the form used) from one window stage.** -/
theorem refinerAbsorbersFor_of_windowStage {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (h : ∃ Cst m₀ : ℕ, 1 ≤ Cst ∧ WindowStage q r Cst m₀ (winCost r)) :
    RefinerAbsorbersFor q r :=
  refinerAbsorbersFor_of_native hr hrq (nativeStrongMultiRefiners_of_windowStage hr hrq h)

end RefinedAbsorption.Window
