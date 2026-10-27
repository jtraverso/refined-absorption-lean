module
public import RequestProject.Sharp.Descent
public import RequestProject.Placement.Assembly

/-!
# Two bounds on the potential `sharpPot 2`

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `sharpPot_two_le`: `sharpPot 2 m ≤ 6 · sharpCost 2 m` for every `m`.
* `exists_mul_sharpPot_le`: for every `c`, `c · sharpPot r m ≤ m` for all large `m` (`r ≥ 2`).
-/

@[expose] public section

namespace RefinedAbsorption.FlatOmni

open RefinedAbsorption.Sharp RefinedAbsorption.Window

theorem succ_sq_le_four_pow (k : ℕ) : (k + 1) ^ 2 ≤ 4 * 2 ^ k ∧ 2 * k + 3 ≤ 4 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e]
    constructor <;> nlinarith

/-- `sharpPot 2 m ≤ 6 · sharpCost 2 m`. -/
theorem sharpPot_two_le (m : ℕ) : sharpPot 2 m ≤ 6 * sharpCost 2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sharpPot]
  have h := sharpPot_le_aux (r := 2) le_rfl m hm
  set L : ℕ := Nat.log 2 m with hL
  set x : ℝ := (m : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxsq : x ^ 2 = m := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hpow : 2 ^ L ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hLsq : ((L : ℝ) + 1) ^ 2 ≤ 4 * x ^ 2 := by
    rw [hxsq]
    have := (succ_sq_le_four_pow L).1
    have h' : (L + 1) ^ 2 ≤ 4 * m := this.trans (Nat.mul_le_mul_left _ hpow)
    exact_mod_cast h'
  have hL2 : (L : ℝ) + 1 ≤ 2 * x := by nlinarith
  have hcost : x * ((L : ℝ) + 1) ≤ (sharpCost 2 m : ℝ) := by
    unfold sharpCost winCost
    push_cast
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  have hfin : (sharpPot 2 m : ℝ) ≤ 6 * (sharpCost 2 m : ℝ) := by
    calc (sharpPot 2 m : ℝ) ≤ ((L : ℝ) + 1) * (4 * x + (L : ℝ) + 1) := h
      _ ≤ ((L : ℝ) + 1) * (6 * x) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = 6 * (x * ((L : ℝ) + 1)) := by ring
      _ ≤ 6 * (sharpCost 2 m : ℝ) := by linarith
  exact_mod_cast hfin

/-- For every `c`, eventually `c · sharpPot r m ≤ m`. -/
theorem exists_mul_sharpPot_le {r : ℕ} (hr : 2 ≤ r) (c : ℕ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → c * sharpPot r m ≤ m := by
  obtain ⟨n₁, hn₁⟩ := RefinedAbsorption.Placement.eventually_mul_rpow_log_le (r := r) (by omega)
    (30 * c) (by positivity)
  refine ⟨max n₁ 3, fun m hm => ?_⟩
  have h1 := hn₁ m (le_of_max_le_left hm)
  have h2 := sharpPot_le (r := r) (n := m) hr (le_of_max_le_right hm)
  have h3 : ((c * sharpPot r m : ℕ) : ℝ) ≤ m := by
    push_cast
    calc (c : ℝ) * sharpPot r m ≤ c * (30 * ((m : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log m)) :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = 30 * c * ((m : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log m) := by ring
      _ ≤ m := h1
  exact_mod_cast h3

end RefinedAbsorption.FlatOmni
