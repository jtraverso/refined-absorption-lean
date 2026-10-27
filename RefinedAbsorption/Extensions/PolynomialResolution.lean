module
public import RefinedAbsorption.Extensions.AlmostResolvable
public import RefinedAbsorption.Extensions.PolynomialTools

/-!
# Steiner systems are almost resolvable with a polynomial error term

Taking the external endpoint `PippengerSpencerPolynomial` as the **only** external hypothesis
(`hPSPoly`, not proved in this project), we prove:

* `steiner_quantitatively_almost_resolvable`: for `q > r ≥ 2` there are `0 < γ < 1` and `n₀`
  such that for all `n ≥ n₀` the blocks of **every** `(n, q, r)`-Steiner system admit a proper
  colouring (blocks of equal colour are vertex-disjoint, i.e. each colour class is a *partial*
  parallel class) with `m` colours where `R ≤ m ≤ R + R^{1-γ}`,
  `R = binom(n-1, r-1) / binom(q-1, r-1)`;
* `exists_quantitatively_almost_resolvable_steiner`: for all large admissible `n` such a Steiner
  system exists (using the existence theorem `steiner_exists` proved in this project).

Route: the blocks form a `q`-uniform hypergraph, `R`-regular (`steiner_deg_point_mul`), with
codegrees `R (q-1)/(n-1)` (`steiner_codeg_mul`), and with `q |𝒮| = n R` blocks.  We apply the
external theorem with `D = R` and `δ = 1/(2(r-1))`; the external `γ₀` is replaced by
`γ = min γ₀ (1/2)` (valid since `R ≥ 1`), while the exponential bound `|𝒮| ≤ exp(R^{γ₀})` is
checked for the exponent `γ₀` actually passed to the external theorem.  The lower bound is
`resolution_classes_lower`.
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset RefinedAbsorption.Original2024 RefinedAbsorption.External
  RefinedAbsorption.External.PippengerSpencer

/-- Adapter: the vertex degree of the external contract is `deg H {v}`. -/
theorem degree_eq_deg_singleton {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (v : V) :
    degree H v = deg H {v} := by
  simp [degree, deg, singleton_subset_iff]

/-- Adapter: the codegree of the external contract is `deg H {u, v}`. -/
theorem codegree_eq_deg_pair {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (u v : V) :
    codegree H u v = deg H {u, v} := by
  simp [codegree, deg, insert_subset_iff, singleton_subset_iff]

/-- Real-arithmetic step of the codegree bound. -/
theorem codeg_le_rpow_aux {c a n q δ : ℝ} (ha : 0 < a) (hn : 0 < n - 1)
    (h' : c * (n - 1) = a * (q - 1)) (haδ : a ^ δ ≤ Real.sqrt (n - 1))
    (hqs : q - 1 ≤ Real.sqrt (n - 1)) : c ≤ a ^ (1 - δ) := by
  have hpos : 0 < a ^ δ := Real.rpow_pos_of_pos ha _
  rw [Real.rpow_sub ha, Real.rpow_one, le_div_iff₀ hpos]
  have hss : Real.sqrt (n - 1) * Real.sqrt (n - 1) = n - 1 := Real.mul_self_sqrt hn.le
  have key : c * a ^ δ * (n - 1) ≤ a * (n - 1) := by
    calc c * a ^ δ * (n - 1) = a * ((q - 1) * a ^ δ) := by rw [mul_right_comm, h']; ring
      _ ≤ a * (Real.sqrt (n - 1) * Real.sqrt (n - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hqs haδ hpos.le (Real.sqrt_nonneg _)) ha.le
      _ = a * (n - 1) := by rw [hss]
  exact le_of_mul_le_mul_right key hn

/-- Real-arithmetic step of the bound on the number of blocks. -/
theorem card_le_mul_sq_aux {S n a q : ℝ} (hsum : q * S = n * a) (hq : 1 ≤ q) (hS : 0 ≤ S)
    (ha : 1 ≤ a) (haq : n - 1 ≤ a * (q - 1)) : S ≤ q * a ^ 2 := by
  have hn_le : n ≤ q * a := by nlinarith
  have h1 : S ≤ q * S := by nlinarith
  have h2 : n * a ≤ q * a * a := mul_le_mul_of_nonneg_right hn_le (by linarith)
  nlinarith

/-- `a ≤ N^(r-1)` implies `a^(1/(2(r-1))) ≤ √N`. -/
theorem rpow_inv_two_pred_le_sqrt {a N : ℝ} {r : ℕ} (hr : 2 ≤ r) (ha : 0 ≤ a) (hN : 0 ≤ N)
    (h : a ≤ N ^ (r - 1)) : a ^ (1 / (2 * ((r : ℝ) - 1))) ≤ Real.sqrt N := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  calc a ^ (1 / (2 * ((r : ℝ) - 1))) ≤ (N ^ (r - 1)) ^ (1 / (2 * ((r : ℝ) - 1))) :=
        Real.rpow_le_rpow ha h (by positivity)
    _ = N ^ (((r - 1 : ℕ) : ℝ) * (1 / (2 * ((r : ℝ) - 1)))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
    _ = Real.sqrt N := by
        rw [Real.sqrt_eq_rpow]
        congr 1
        rw [Nat.cast_sub (by omega)]
        field_simp
        norm_num

variable {q r : ℕ}

/-- Regularity data of a large Steiner system: all points have the same degree `a`,
`R = a`, the codegree identity `codeg · (n-1) = a (q-1)`, and `n - 1 ≤ a (q - 1)`. -/
theorem steiner_regular_data (hr : 2 ≤ r) (hrq : r < q) {n : ℕ} (hn : q + 2 < n)
    {𝒮 : Finset (Finset (Fin n))} (h𝒮 : IsSteinerSystem q r 𝒮) :
    ∃ a : ℕ, (∀ v : Fin n, deg 𝒮 {v} = a) ∧
      (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) = a ∧
      (∀ u v : Fin n, u ≠ v →
        ((deg 𝒮 {u, v} : ℕ) : ℝ) * ((n : ℝ) - 1) = (a : ℝ) * ((q : ℝ) - 1)) ∧
      (n : ℝ) - 1 ≤ (a : ℝ) * ((q : ℝ) - 1) ∧
      (a : ℝ) ≤ ((n : ℝ) - 1) ^ (r - 1) := by
  let v₀ : Fin n := ⟨0, by omega⟩
  let v₁ : Fin n := ⟨1, by omega⟩
  have h01 : v₁ ≠ v₀ := by simp [v₀, v₁, Fin.ext_iff]
  have hqpos : 0 < (q - 1).choose (r - 1) := Nat.choose_pos (by omega)
  have hdeg : ∀ v : Fin n, deg 𝒮 {v} = deg 𝒮 {v₀} := by
    intro v
    have h1 := steiner_deg_point_mul h𝒮 (by omega) v
    have h2 := steiner_deg_point_mul h𝒮 (by omega) v₀
    exact Nat.eq_of_mul_eq_mul_left hqpos (h1.trans h2.symm)
  have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hqc : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hcod : ∀ u v : Fin n, u ≠ v →
      ((deg 𝒮 {u, v} : ℕ) : ℝ) * ((n : ℝ) - 1) = (deg 𝒮 {v₀} : ℝ) * ((q : ℝ) - 1) := by
    intro u v huv
    rw [← hnc, ← hqc]
    exact_mod_cast (steiner_codeg_mul h𝒮 hr hrq.le huv).trans (by rw [hdeg v])
  refine ⟨deg 𝒮 {v₀}, hdeg, ?_, hcod, ?_, ?_⟩
  · rw [div_eq_iff (by exact_mod_cast hqpos.ne'), ← steiner_deg_point_mul h𝒮 (by omega) v₀]
    push_cast; ring
  · have hb1 : 1 ≤ deg 𝒮 {v₁, v₀} := by
      have := steiner_deg_pair_mul h𝒮 hr h01
      have hpos : 0 < (n - 2).choose (r - 2) := Nat.choose_pos (by omega)
      rcases Nat.eq_zero_or_pos (deg 𝒮 {v₁, v₀}) with h0 | h0
      · rw [h0, mul_zero] at this; omega
      · exact h0
    have h' := hcod v₁ v₀ h01
    have hb1' : (1 : ℝ) ≤ (deg 𝒮 {v₁, v₀} : ℝ) := by exact_mod_cast hb1
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith
    nlinarith
  · have h1 : (deg 𝒮 {v₀} : ℝ) ≤ ((n - 1).choose (r - 1) : ℕ) := by
      rw [← steiner_deg_point_mul h𝒮 (by omega) v₀]
      have : (1 : ℝ) ≤ ((q - 1).choose (r - 1) : ℕ) := by exact_mod_cast hqpos
      push_cast; nlinarith
    have h2 : (((n - 1).choose (r - 1) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) ^ (r - 1) := by
      refine (Nat.choose_le_pow_div (r - 1) (n - 1)).trans ?_
      exact div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos _)
    rw [hnc] at h2; linarith

/-- **Every large Steiner system is almost resolvable with a polynomial error**
(conditional on the external endpoint `hPSPoly`).  For `q > r ≥ 2` there are `0 < γ < 1` and `n₀`
(depending only on `q`, `r` and the external theorem) such that for all `n ≥ n₀` and every
`(n, q, r)`-Steiner system `𝒮`, the blocks admit a colouring `c` with `m` colours, distinct blocks
of equal colour being vertex-disjoint, where `R ≤ m ≤ R + R^{1-γ}` and
`R = binom(n-1, r-1) / binom(q-1, r-1)`. -/
theorem steiner_quantitatively_almost_resolvable (hPSPoly : PippengerSpencerPolynomial)
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮 : Finset (Finset (Fin n)),
      IsSteinerSystem q r 𝒮 →
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by
  set δ : ℝ := 1 / (2 * ((r : ℝ) - 1)) with hδ_def
  have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hδ0 : 0 < δ := by rw [hδ_def]; positivity
  have hδ1 : δ < 1 := by
    rw [hδ_def, div_lt_one (by positivity)]; linarith
  obtain ⟨γ₀, hγ₀, D₀, hP⟩ := hPSPoly q (by omega) δ hδ0 hδ1
  obtain ⟨D₁, hD₁⟩ := eventually_mul_sq_le_exp_rpow hγ₀ (q : ℝ)
  refine ⟨min γ₀ (1 / 2), lt_min hγ₀ (by norm_num), by
    have := min_le_right γ₀ (1 / 2 : ℝ); linarith, ?_⟩
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((|D₀| + |D₁| + 1) * (q : ℝ) + (q : ℝ) ^ 2 + q + 2)
  refine ⟨N₁, fun n hn 𝒮 h𝒮 => ?_⟩
  have hnR : (N₁ : ℝ) ≤ n := by exact_mod_cast hn
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hA : 0 ≤ |D₀| + |D₁| := by positivity
  have hnq : (q : ℝ) + 2 < n := by nlinarith
  have hnq' : q + 2 < n := by exact_mod_cast hnq
  obtain ⟨a, hdeg, hcast, hcod, haq, hapow⟩ := steiner_regular_data hr hrq hnq' h𝒮
  rw [hcast]
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  -- `a` is large
  have haL : |D₀| + |D₁| + 1 ≤ (a : ℝ) := by
    by_contra hlt
    push_neg at hlt
    have : (a : ℝ) * ((q : ℝ) - 1) < (|D₀| + |D₁| + 1) * ((q : ℝ) - 1) :=
      mul_lt_mul_of_pos_right hlt (by linarith)
    nlinarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have haD₀ : D₀ ≤ (a : ℝ) := by linarith [le_abs_self D₀, abs_nonneg D₁]
  have haD₁ : D₁ ≤ (a : ℝ) := by linarith [le_abs_self D₁, abs_nonneg D₀]
  -- codegree bound `codeg ≤ a^(1-δ)`
  have haδ : (a : ℝ) ^ δ ≤ Real.sqrt ((n : ℝ) - 1) :=
    rpow_inv_two_pred_le_sqrt hr ha0.le hn1.le hapow
  have hqs : (q : ℝ) - 1 ≤ Real.sqrt ((n : ℝ) - 1) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hcodR : ∀ u v : Fin n, u ≠ v → (codegree 𝒮 u v : ℝ) ≤ (a : ℝ) ^ (1 - δ) := by
    intro u v huv
    rw [codegree_eq_deg_pair]
    exact codeg_le_rpow_aux ha0 hn1 (hcod u v huv) haδ hqs
  -- number of blocks `|𝒮| ≤ q a² ≤ exp(a^γ₀)`
  have hcardS : (𝒮.card : ℝ) ≤ Real.exp ((a : ℝ) ^ γ₀) := by
    have hsum := uniform_card_mul_eq_sum_degree (k := q) (H := 𝒮) h𝒮.card_eq
    have hsum' : q * 𝒮.card = n * a := by
      rw [hsum]
      simp [degree_eq_deg_singleton, hdeg]
    have hsumR : (q : ℝ) * 𝒮.card = (n : ℝ) * a := by exact_mod_cast hsum'
    have : (𝒮.card : ℝ) ≤ (q : ℝ) * (a : ℝ) ^ 2 :=
      card_le_mul_sq_aux hsumR (by linarith) (Nat.cast_nonneg _) ha1 haq
    exact this.trans (hD₁ a haD₁)
  obtain ⟨m, c, hm, hc⟩ := hP (Fin n) 𝒮 (a : ℝ) haD₀ h𝒮.card_eq
    (fun v => by rw [degree_eq_deg_singleton, hdeg v]) hcodR hcardS
  refine ⟨m, c, ?_, ?_, hc⟩
  · rw [← hcast]
    exact resolution_classes_lower (by omega) hrq.le h𝒮 (by omega) hc
  · exact hm.trans (by linarith [rpow_error_mono ha1 (min_le_left γ₀ (1 / 2))])

/-- **Existence of Steiner systems that are almost resolvable with a polynomial error**
(conditional on `hPSPoly`): for `q > r ≥ 2` there are `0 < γ < 1` and `n₀` such that for every
admissible `n ≥ n₀` there is an `(n, q, r)`-Steiner system whose blocks admit a proper colouring
with `m` colours, `R ≤ m ≤ R + R^{1-γ}`. -/
theorem exists_quantitatively_almost_resolvable_steiner (hPSPoly : PippengerSpencerPolynomial)
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by
  obtain ⟨γ, hγ0, hγ1, n₁, h1⟩ := steiner_quantitatively_almost_resolvable hPSPoly hr hrq
  obtain ⟨n₂, h2⟩ := steiner_exists (by omega) hrq
  refine ⟨γ, hγ0, hγ1, max n₁ n₂, fun n hn hdiv => ?_⟩
  obtain ⟨𝒮, h𝒮⟩ := h2 n (le_of_max_le_right hn) hdiv
  exact ⟨𝒮, h𝒮, h1 n (le_of_max_le_left hn) 𝒮 h𝒮⟩

end RefinedAbsorption.Extensions
