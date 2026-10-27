module
public import RefinedAbsorption.Extensions.PolynomialExternal

/-!
# Generic tools for applying `PippengerSpencerPolynomial`

Elementary facts used by both quantitative consumers:
* a proper colouring needs at least `degree H v` colours;
* double counting `k · |H| = ∑_v degree H v` for `k`-uniform `H`;
* `C · D² ≤ exp(D^γ)` for all large `D`;
* the error term `D^{1-γ₀}` can be replaced by `D^{1-γ}` for `γ ≤ γ₀`, `D ≥ 1`.
-/

@[expose] public section

namespace RefinedAbsorption.External

open Finset PippengerSpencer

variable {V : Type*} [DecidableEq V]

/-- The edges through a vertex receive pairwise distinct colours. -/
theorem degree_le_of_isProperEdgeColouring {H : Finset (Finset V)} {m : ℕ}
    {c : Finset V → Fin m} (hc : IsProperEdgeColouring H m c) (v : V) :
    degree H v ≤ m := by
  have := card_le_card_of_injOn (s := H.filter (fun e => v ∈ e))
    (t := (univ : Finset (Fin m))) c (fun _ _ => mem_coe.2 (mem_univ _)) (by
      intro e he f hf hcc
      by_contra hne
      rw [mem_coe, mem_filter] at he hf
      exact disjoint_left.1 (hc e he.1 f hf.1 hne hcc) he.2 hf.2)
  simpa [degree] using this

/-- Double counting for a `k`-uniform hypergraph. -/
theorem uniform_card_mul_eq_sum_degree [Fintype V] {H : Finset (Finset V)} {k : ℕ}
    (hH : IsUniform H k) : k * H.card = ∑ v, degree H v := by
  classical
  have h1 : ∑ v, degree H v = ∑ v : V, ∑ e ∈ H, (if v ∈ e then 1 else 0) := by
    refine sum_congr rfl fun v _ => ?_
    rw [degree, card_filter]
  rw [h1, sum_comm]
  have h2 : ∀ e ∈ H, (∑ v : V, (if v ∈ e then 1 else 0)) = k := by
    intro e he
    rw [← card_filter, filter_mem_eq_inter, univ_inter]; exact hH e he
  rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]

/-- `C · D² ≤ exp(D^γ)` for all sufficiently large `D` (any `γ > 0`). -/
theorem eventually_mul_sq_le_exp_rpow {γ : ℝ} (hγ : 0 < γ) (C : ℝ) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → C * D ^ 2 ≤ Real.exp (D ^ γ) := by
  have hlog : ∀ᶠ D in Filter.atTop, Real.log D ≤ (1 / 4) * D ^ γ := by
    have := (isLittleO_log_rpow_atTop hγ).bound (show (0 : ℝ) < 1 / 4 by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 1] with D hD hD1
    have h0 : 0 ≤ Real.log D := Real.log_nonneg hD1.le
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hD
    exact hD
  have hbig : ∀ᶠ D in Filter.atTop, 2 * (|C| + 1) ≤ D ^ γ :=
    (tendsto_rpow_atTop hγ).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨D₁, hD₁⟩ := Filter.eventually_atTop.1
    ((hlog.and hbig).and (Filter.eventually_gt_atTop 1))
  refine ⟨D₁, fun D hD => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hD₁ D hD
  have hD0 : 0 < D := by linarith
  have hC1 : 0 < |C| + 1 := by positivity
  have hlogC : Real.log (|C| + 1) ≤ |C| + 1 := by
    have := Real.add_one_le_exp (Real.log (|C| + 1))
    rw [Real.exp_log hC1] at this; linarith
  calc C * D ^ 2 ≤ (|C| + 1) * D ^ 2 := by
        gcongr; linarith [le_abs_self C]
    _ = Real.exp (Real.log (|C| + 1) + 2 * Real.log D) := by
        rw [Real.exp_add, Real.exp_log hC1, ← Real.log_rpow hD0, Real.exp_log (by positivity)]
        norm_cast
    _ ≤ Real.exp (D ^ γ) := by
        apply Real.exp_le_exp.2
        linarith

/-- For `D ≥ 1` and `γ ≤ γ₀`, the error `D^{1-γ₀}` is at most `D^{1-γ}`. -/
theorem rpow_error_mono {D γ γ₀ : ℝ} (hD : 1 ≤ D) (h : γ ≤ γ₀) :
    D ^ (1 - γ₀) ≤ D ^ (1 - γ) :=
  Real.rpow_le_rpow_of_exponent_le hD (by linarith)

end RefinedAbsorption.External
