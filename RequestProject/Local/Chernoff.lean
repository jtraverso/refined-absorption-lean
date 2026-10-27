module
public import Mathlib

/-!
# A Chernoff bound on finite product spaces (counting form)

Mathematics: the exponential-moment bound used in the random embedding step of the Refine Down
Lemma (M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1, Claim 4.1.1 and the
Chernoff bound after it).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The probability space is the set of all maps `σ : ι → Ω` (independent uniform choices, one for
each `i : ι`), and probabilities are written as counts.  For bounded non-negative functions
`X i : Ω → ℝ` with `0 ≤ X i ≤ b`,

`#{σ | T ≤ ∑ i, X i (σ i)} ≤ |Ω|^|ι| · exp((e - 1) μ / b - T / b)`,

where `μ = ∑ i, (∑ ω, X i ω) / |Ω|` is the expectation of the sum (**`card_sum_ge_le`**).

`exists_good_choice` is the union bound: if the counts of finitely many bad events add up to less
than `|Ω|^|ι|`, some `σ` avoids all of them.
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset

/-- `exp t ≤ 1 + (e - 1) t` on `[0, 1]` (convexity of `exp`). -/
theorem exp_le_one_add_mul {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.exp t ≤ 1 + (Real.exp 1 - 1) * t := by
  have := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ)) (sub_nonneg.2 h1) h0
    (by ring)
  simp at this
  nlinarith [this]

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The exponential moment of one coordinate. -/
theorem sum_exp_le (X : Ω → ℝ) {b : ℝ} (hb : 0 < b) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXb : ∀ ω, X ω ≤ b) :
    ∑ ω, Real.exp (X ω / b) ≤
      (Fintype.card Ω : ℝ) * Real.exp ((Real.exp 1 - 1) * ((∑ ω, X ω) / Fintype.card Ω) / b) := by
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · have : IsEmpty Ω := Fintype.card_eq_zero_iff.1 h0
    simp
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hpos
  calc ∑ ω, Real.exp (X ω / b) ≤ ∑ ω, (1 + (Real.exp 1 - 1) * (X ω / b)) :=
        sum_le_sum fun ω _ => exp_le_one_add_mul (div_nonneg (hX0 ω) hb.le)
          ((div_le_one hb).2 (hXb ω))
    _ = Fintype.card Ω * (1 + (Real.exp 1 - 1) * ((∑ ω, X ω) / Fintype.card Ω) / b) := by
        rw [sum_add_distrib, ← mul_sum, ← sum_div]
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
        field_simp
    _ ≤ Fintype.card Ω * Real.exp ((Real.exp 1 - 1) * ((∑ ω, X ω) / Fintype.card Ω) / b) := by
        gcongr
        linarith [Real.add_one_le_exp ((Real.exp 1 - 1) * ((∑ ω, X ω) / Fintype.card Ω) / b)]

/-- **Chernoff bound, counting form.** -/
theorem card_sum_ge_le (X : ι → Ω → ℝ) {b : ℝ} (hb : 0 < b) (hX0 : ∀ i ω, 0 ≤ X i ω)
    (hXb : ∀ i ω, X i ω ≤ b) (T : ℝ) :
    ((univ.filter fun σ : ι → Ω => T ≤ ∑ i, X i (σ i)).card : ℝ) ≤
      (Fintype.card Ω : ℝ) ^ Fintype.card ι *
        Real.exp ((Real.exp 1 - 1) * (∑ i, (∑ ω, X i ω) / Fintype.card Ω) / b - T / b) := by
  set F := univ.filter fun σ : ι → Ω => T ≤ ∑ i, X i (σ i)
  have hmgf : (F.card : ℝ) * Real.exp (T / b) ≤
      ∑ σ : ι → Ω, Real.exp ((∑ i, X i (σ i)) / b) := by
    calc (F.card : ℝ) * Real.exp (T / b) = ∑ σ ∈ F, Real.exp (T / b) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ σ ∈ F, Real.exp ((∑ i, X i (σ i)) / b) :=
          sum_le_sum fun σ hσ => Real.exp_le_exp.2
            (div_le_div_of_nonneg_right (mem_filter.1 hσ).2 hb.le)
      _ ≤ ∑ σ : ι → Ω, Real.exp ((∑ i, X i (σ i)) / b) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => (Real.exp_pos _).le
  have hprod : ∑ σ : ι → Ω, Real.exp ((∑ i, X i (σ i)) / b) =
      ∏ i, ∑ ω, Real.exp (X i ω / b) := by
    rw [prod_univ_sum, Fintype.piFinset_univ]
    refine sum_congr rfl fun σ _ => ?_
    rw [sum_div, Real.exp_sum]
  have hbound : ∏ i, ∑ ω, Real.exp (X i ω / b) ≤
      ∏ i, ((Fintype.card Ω : ℝ) *
        Real.exp ((Real.exp 1 - 1) * ((∑ ω, X i ω) / Fintype.card Ω) / b)) :=
    prod_le_prod (fun i _ => sum_nonneg fun ω _ => (Real.exp_pos _).le)
      fun i _ => sum_exp_le (X i) hb (hX0 i) (hXb i)
  have hprod2 : ∏ i, ((Fintype.card Ω : ℝ) *
        Real.exp ((Real.exp 1 - 1) * ((∑ ω, X i ω) / Fintype.card Ω) / b)) =
      (Fintype.card Ω : ℝ) ^ Fintype.card ι *
        Real.exp ((Real.exp 1 - 1) * (∑ i, (∑ ω, X i ω) / Fintype.card Ω) / b) := by
    rw [prod_mul_distrib, prod_const, card_univ, ← Real.exp_sum, mul_sum, sum_div]
  have hexp : Real.exp ((Real.exp 1 - 1) * (∑ i, (∑ ω, X i ω) / Fintype.card Ω) / b - T / b) =
      Real.exp ((Real.exp 1 - 1) * (∑ i, (∑ ω, X i ω) / Fintype.card Ω) / b) /
        Real.exp (T / b) := Real.exp_sub _ _
  rw [hexp, mul_div_assoc', le_div_iff₀ (Real.exp_pos _)]
  rw [hprod] at hmgf
  linarith [hbound, hprod2]

/-- **Union bound**: if the bad events have total count `< |Ω|^|ι|`, some `σ` avoids them all. -/
theorem exists_good_choice {κ : Type*} (ev : Finset κ) (bad : κ → (ι → Ω) → Prop)
    [∀ k σ, Decidable (bad k σ)]
    (h : ∑ k ∈ ev, ((univ.filter fun σ => bad k σ).card : ℝ) <
      (Fintype.card Ω : ℝ) ^ Fintype.card ι) :
    ∃ σ : ι → Ω, ∀ k ∈ ev, ¬ bad k σ := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsub : (univ : Finset (ι → Ω)) ⊆ ev.biUnion fun k => univ.filter fun σ => bad k σ := by
    intro σ _
    obtain ⟨k, hk, hb⟩ := hcon σ
    exact mem_biUnion.2 ⟨k, hk, mem_filter.2 ⟨mem_univ _, hb⟩⟩
  have h1 := card_le_card hsub
  have h2 := card_biUnion_le (s := ev) (t := fun k => univ.filter fun σ => bad k σ)
  rw [card_univ, Fintype.card_fun] at h1
  have h3 : ((Fintype.card Ω ^ Fintype.card ι : ℕ) : ℝ) ≤
      ∑ k ∈ ev, ((univ.filter fun σ => bad k σ).card : ℝ) := by
    exact_mod_cast h1.trans h2
  push_cast at h3
  linarith

end RefinedAbsorption.Local
