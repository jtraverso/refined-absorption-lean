module
public import RefinedAbsorption.OddGrid.Base
public import RefinedAbsorption.OddGrid.PlanStrong
public import RefinedAbsorption.LocalRefiner.Native
public import RefinedAbsorption.RefinerOne.Existence

/-!
# Strong multi-refiners with the exact budget for `r = 2` and every `q ≥ 3`

* `nativeStrongMultiRefiners_two`: `NativeStrongMultiRefiners q 2` for every `q ≥ 3`, in particular
  for odd `q` (`nativeStrongMultiRefiners_two_odd`).  The budget is
  `5 ⌊D⌋ + 400 ⌊√n⌋ ⌈log₂ n⌉ ≤ 1205 · max(D, √n log n)`.
* `refinerAbsorbersFor_two`: hence `RefinerAbsorbersFor q 2` for every `q ≥ 3`.

The refiner is the one given by a valid plan (`plan_strong`) for the grid plan on `Fin n`
(`base_plan`): the input pairs are routed into rook pairs of a `√n × √n` grid, and the grid is then
compressed by halving columns and rows; every halving merges each emptied vertex into a hub and
then moves the single remaining pair at the emptied vertex.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.LocalRefiner

theorem IsStrongMultiRefiner.mono' {q r C C' n : ℕ} {E : Type*} [DecidableEq E]
    {ends : E → Finset (Fin n)} {K X R : Finset E} {𝒲 : Finset (Finset E)} {D : ℕ}
    (h : IsStrongMultiRefiner q r C ends K X R 𝒲 D) (hC : C ≤ C') :
    IsStrongMultiRefiner q r C' ends K X R 𝒲 D where
  refiner := IsResidualMultiRefiner.mono h.refiner hC
  keep := h.keep
  inj := h.inj
  oneX := h.oneX
  degX := h.degX
  degR S hS := (h.degR S hS).trans (Nat.mul_le_mul_right _ hC)
  pieceDeg S hS := (h.pieceDeg S hS).trans (Nat.mul_le_mul_right _ hC)

lemma clog_le_log {n : ℕ} (hn : 3 ≤ n) : (Nat.clog 2 n : ℝ) ≤ 3 * Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : (1 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n by omega)
  have hlt' : ((2 : ℝ) ^ (Nat.clog 2 n).pred) < n := by exact_mod_cast hlt
  have hl := Real.log_lt_log (by positivity) hlt'
  rw [Real.log_pow] at hl
  have hl2 := Real.log_two_gt_d9
  have hpred : ((Nat.clog 2 n : ℕ) : ℝ) ≤ ((Nat.clog 2 n).pred : ℕ) + 1 := by
    have : Nat.clog 2 n ≤ (Nat.clog 2 n).pred + 1 := by rw [Nat.pred_eq_sub_one]; omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) ≤ ((Nat.clog 2 n).pred : ℕ) := Nat.cast_nonneg _
  nlinarith

lemma sqrt_le_rpow (n : ℕ) : (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) := by
  have h : (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [h, ← Real.sqrt_eq_rpow]
  apply Real.le_sqrt_of_sq_le
  have := Nat.sqrt_le' n
  exact_mod_cast this

/-- **`NativeStrongMultiRefiners q 2` for every `q ≥ 3`.** -/
theorem nativeStrongMultiRefiners_two {q : ℕ} (hq : 3 ≤ q) : NativeStrongMultiRefiners q 2 := by
  set K := q * (q - 1) with hKdef
  have hK1 : 1 < K := by
    have : 3 * 2 ≤ q * (q - 1) := Nat.mul_le_mul hq (by omega)
    omega
  haveI : NeZero K := ⟨by omega⟩
  have hd : q - 1 ∣ K := Dvd.intro_left _ rfl
  have hN : q.choose 2 ∣ K := by
    rw [Nat.choose_two_right]
    exact Nat.div_dvd_of_dvd (Nat.even_mul_pred_self q).two_dvd
  refine ⟨Cpl K 256 + 1205, by omega, 25, ?_⟩
  intro n hn X D hX hXD _
  set Dn := ⌊D⌋₊
  have hD : ∀ y : Fin n, (X.filter (y ∈ ·)).card ≤ Dn := by
    intro y
    have h := hXD {y} (by simp)
    have heq : deg X {y} = (X.filter (y ∈ ·)).card := by
      unfold deg; congr 1; apply filter_congr; intro e _; exact singleton_subset_iff
    rw [heq] at h
    exact Nat.le_floor h
  obtain ⟨sp, hok, hT, hM, hP⟩ := base_plan hn hX hD
  set B := 5 * Dn + 400 * Nat.sqrt n * Nat.clog 2 n with hBdef
  have hXB : ∀ v, (X.filter (v ∈ ·)).card ≤ B := fun v => (hD v).trans (by omega)
  obtain ⟨himg, hS⟩ := plan_strong (K := K) (q := q) hd hN hK1 hok hT hM hXB hP
  refine ⟨_, inferInstance, _, _, _, _, _, B, himg, ?_, IsStrongMultiRefiner.mono' hS (by omega)⟩
  set L := (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) * Real.log n
  have hL : 1 ≤ L := one_le_sqrt_log (by omega)
  have hfl : (Dn : ℝ) ≤ max D 0 := by
    rcases le_or_gt 0 D with h0 | h0
    · exact (Nat.floor_le h0).trans (le_max_left _ _)
    · have : Dn = 0 := Nat.floor_eq_zero.2 (by linarith)
      rw [this]; simp
  have hmax : max D 0 ≤ max D L := max_le_max le_rfl (by linarith)
  have hLm : L ≤ max D L := le_max_right _ _
  have hs := sqrt_le_rpow n
  have hc := clog_le_log (n := n) (by omega)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hs0 : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _
  have hsc : (Nat.sqrt n : ℝ) * Nat.clog 2 n ≤ 3 * L := by
    calc (Nat.sqrt n : ℝ) * Nat.clog 2 n
        ≤ (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) * (3 * Real.log n) :=
          mul_le_mul hs hc hc0 (by positivity)
      _ = 3 * L := by ring
  have hCpl : (0 : ℝ) ≤ Cpl K 256 := Nat.cast_nonneg _
  have hm1 : 1 ≤ max D L := le_trans hL hLm
  rw [hBdef]
  push_cast
  calc 5 * (Dn : ℝ) + 400 * (Nat.sqrt n : ℝ) * (Nat.clog 2 n : ℝ)
      ≤ 5 * max D L + 1200 * max D L := by nlinarith
    _ = 1205 * max D L := by ring
    _ ≤ ((Cpl K 256 : ℝ) + 1205) * max D L := by nlinarith

/-- **`NativeStrongMultiRefiners q 2` for odd `q`.** -/
theorem nativeStrongMultiRefiners_two_odd {q : ℕ} (hq : 3 ≤ q) (_hodd : Odd q) :
    NativeStrongMultiRefiners q 2 :=
  nativeStrongMultiRefiners_two hq

/-- **`RefinerAbsorbersFor q 2` for every `q ≥ 3`**: refined refiners with attached absorbers and
`Δ(R ∪ ⋃ A_W) ≤ C · max(D, √n log n)` (Theorem 1.10 for `r = 2` in the form used by the
project). -/
theorem refinerAbsorbersFor_two {q : ℕ} (hq : 3 ≤ q) : RefinerAbsorbersFor q 2 :=
  refinerAbsorbersFor_of_native le_rfl (by omega) (nativeStrongMultiRefiners_two hq)

/-- **The Existence Conjecture from the refiners for uniformities `r ≥ 3`.**  The cases `r = 1`
and `r = 2` of `RefinerAbsorbersFor` are now theorems, so only `r ≥ 3` remains as a hypothesis. -/
theorem steinerExistence_of_refinerAbsorbers_three_le
    (h : ∀ q r : ℕ, 3 ≤ r → r < q → RefinerAbsorbersFor q r) : SteinerExistenceConjecture := by
  apply steinerExistence_of_refinerAbsorbers_two_le
  intro q r hr hrq
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · obtain rfl : r = 2 := by omega
    exact refinerAbsorbersFor_two (by omega)
  · exact h q r h3 hrq

end RefinedAbsorption.OddGrid
