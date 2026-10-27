module
public import RefinedAbsorption.Local.Chernoff

/-!
# Independent random choices with all sums small at once

Mathematics: the Chernoff bound with the union bound, as in the proof of Lemma 4.1 of
M. Delcourt and L. Postle, arXiv:2402.17855.  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

**`exists_spread_choice`**: let `X e v ω ∈ [0, μ]` be bounded integer-valued variables, one for
every event `e ∈ ev`, every index `v` and every choice `ω ∈ Ω`.  If for every event the sum over
`v` of the means is at most `Mn e`, there is a choice `σ : ι → Ω` with
`∑_v X e v (σ v) < (e - 1) Mn e + μ log (|ev| + 1)` for every event simultaneously.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.Local

/-- **All sums small at once.** -/
theorem exists_spread_choice {ι Ω κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [Nonempty Ω] (ev : Finset κ) (X : κ → ι → Ω → ℕ) {μ : ℕ} (hμ : 1 ≤ μ)
    (hXb : ∀ e ∈ ev, ∀ v ω, X e v ω ≤ μ) (Mn : κ → ℝ)
    (hM : ∀ e ∈ ev, ∑ v, (∑ ω, (X e v ω : ℝ)) / Fintype.card Ω ≤ Mn e) :
    ∃ σ : ι → Ω, ∀ e ∈ ev,
      ((∑ v, X e v (σ v) : ℕ) : ℝ) < (Real.exp 1 - 1) * Mn e + μ * Real.log (ev.card + 1) := by
  classical
  set L : ℝ := Real.log (ev.card + 1) with hL
  have hμpos : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hpos : (0 : ℝ) < ev.card + 1 := by positivity
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hcount : ∀ e ∈ ev, ((univ.filter fun σ : ι → Ω =>
      (Real.exp 1 - 1) * Mn e + μ * L ≤ ∑ v, (X e v (σ v) : ℝ)).card : ℝ) ≤
      (Fintype.card Ω : ℝ) ^ Fintype.card ι / (ev.card + 1) := by
    intro e he'
    have hch := card_sum_ge_le (fun v ω => (X e v ω : ℝ)) hμpos (fun _ _ => Nat.cast_nonneg _)
      (fun v ω => by show (X e v ω : ℝ) ≤ μ; exact_mod_cast hXb e he' v ω)
      ((Real.exp 1 - 1) * Mn e + μ * L)
    refine hch.trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hexp : (Real.exp 1 - 1) * (∑ v, (∑ ω, (X e v ω : ℝ)) / Fintype.card Ω) / μ -
        ((Real.exp 1 - 1) * Mn e + μ * L) / μ ≤ -L := by
      rw [div_sub_div_same, div_le_iff₀ hμpos]
      nlinarith [mul_le_mul_of_nonneg_left (hM e he') he]
    calc Real.exp _ ≤ Real.exp (-L) := Real.exp_le_exp.2 hexp
      _ = ((ev.card : ℝ) + 1)⁻¹ := by rw [Real.exp_neg, hL, Real.exp_log hpos]
  obtain ⟨σ, hσ⟩ := exists_good_choice ev (fun e (σ : ι → Ω) =>
    (Real.exp 1 - 1) * Mn e + μ * L ≤ ∑ v, (X e v (σ v) : ℝ)) (by
      have htot : (0 : ℝ) < (Fintype.card Ω : ℝ) ^ Fintype.card ι := by positivity
      calc ∑ e ∈ ev, _ ≤ ∑ _e ∈ ev,
            (Fintype.card Ω : ℝ) ^ Fintype.card ι / (ev.card + 1) := sum_le_sum hcount
        _ = ev.card * ((Fintype.card Ω : ℝ) ^ Fintype.card ι / (ev.card + 1)) := by
            rw [sum_const, nsmul_eq_mul]
        _ < (Fintype.card Ω : ℝ) ^ Fintype.card ι := by
            rw [mul_div_assoc', div_lt_iff₀ hpos]; nlinarith)
  refine ⟨σ, fun e he' => ?_⟩
  have := hσ e he'
  push_neg at this
  push_cast
  exact this

end RefinedAbsorption.General
