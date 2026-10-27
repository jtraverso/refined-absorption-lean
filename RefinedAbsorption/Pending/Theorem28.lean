module
public import RefinedAbsorption.Pending.Core28

/-!
# Theorem 2.8 of arXiv:2402.17855v1 (Nibble with Reserves): proof

`RefinedAbsorption.Pending.theorem_2_8 : RefinedAbsorption.Faithful2024.Theorem_2_8`.

Parameters: for `r ≥ 2` and `β ∈ (0,1)` the multi-hypergraph nibble `multiNibbleA` with
`δ = β/2` and test-set exponent `3` gives `c > 0` and `Δ₀`; we put `c' = min c (β/2)` and
`α = c'/8`.  For every real `D` above a threshold (`thm28_eventually`), the numerical conditions
of `thm28_core` hold with `D₀ = ⌊D⌋`, `t = ⌈D^{1-α}⌉` and `p = D^α / t`; the threshold `D_β` is the
natural number `⌈max D* 0⌉`.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset Filter RefinedAbsorption.Faithful2024

theorem mul_one_sub_rpow_neg {x a : ℝ} (hx : 0 < x) : x * (1 - x ^ (-a)) = x - x ^ (1 - a) := by
  rw [mul_sub, mul_one, sub_eq_add_neg 1 a, Real.rpow_add hx, Real.rpow_one]

/-- The only non-polynomial limit: `e^{-D^α}(3 + 24 r D²) → 0`. -/
theorem tendsto_exp_neg_rpow_mul {α : ℝ} (hα : 0 < α) (r : ℝ) :
    Tendsto (fun D : ℝ => Real.exp (-(D ^ α)) * (3 + 24 * r * D ^ 2)) atTop (nhds 0) := by
  have h1 : Tendsto (fun D : ℝ => Real.exp (-(D ^ α))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop hα)
  have h2 : Tendsto (fun D : ℝ => D ^ 2 * Real.exp (-(D ^ α))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 / α) 1 one_pos).comp
      (tendsto_rpow_atTop hα)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with D hD
    simp only [Function.comp, neg_mul, one_mul]
    congr 1
    rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hα.ne', Real.rpow_two]
  have : (fun D : ℝ => Real.exp (-(D ^ α)) * (3 + 24 * r * D ^ 2)) =
      fun D => 3 * Real.exp (-(D ^ α)) + 24 * r * (D ^ 2 * Real.exp (-(D ^ α))) := by
    funext D; ring
  rw [this]
  simpa using (h1.const_mul 3).add (h2.const_mul (24 * r))

set_option maxHeartbeats 1000000 in
/-- **The numerical conditions of `thm28_core` hold for all large `D`.** -/
theorem thm28_eventually (r : ℕ) {β c Δ₀ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    ∀ᶠ D : ℝ in atTop,
      let c' := min c (β / 2)
      let α := c' / 8
      let D₀ := ⌊D⌋₊
      let t := ⌈D ^ (1 - α)⌉₊
      let p := D ^ α / t
      0 ≤ D ∧ Δ₀ ≤ D₀ ∧
      (D₀ : ℝ) * (1 - (D₀ : ℝ) ^ (-(β / 2))) ≤ D * (1 - D ^ (-β)) ∧
      D ^ (1 - β) ≤ (D₀ : ℝ) ^ (1 - β / 2) ∧
      D ≤ (D₀ : ℝ) ^ 3 ∧
      (r : ℝ) * t * ⌊D ^ (1 - β)⌋₊ ≤ (D₀ : ℝ) ^ 3 ∧
      0 ≤ p ∧ p ≤ 1 ∧
      4 * max ((1 - p) ^ t) (p ^ 2) *
        (2 + 2 * r * ((D₀ : ℝ) ^ (-c) * D + ⌊D ^ (1 - β)⌋₊ * (D₀ : ℝ) ^ (β / 2)) * (t + 2) + 1)
          ≤ 1 := by
  set c' := min c (β / 2) with hc'
  set α := c' / 8 with hα
  have hc'0 : 0 < c' := lt_min hc (by linarith)
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'β : c' ≤ β / 2 := min_le_right _ _
  have hα0 : 0 < α := by positivity
  have hαs : α ≤ 1 / 16 := by rw [hα]; linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  -- eventual facts
  have E1 : ∀ᶠ D : ℝ in atTop, max (max Δ₀ 0 + 1) (16 * r + 16) ≤ D := eventually_ge_atTop _
  have E2 : ∀ᶠ D : ℝ in atTop, 2 ≤ D ^ (β / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < β / 2)).eventually_ge_atTop 2
  have E3 : ∀ᶠ D : ℝ in atTop, Real.exp (-(D ^ α)) * (3 + 24 * r * D ^ 2) ≤ 1 / 8 :=
    (tendsto_order.1 (tendsto_exp_neg_rpow_mul hα0 r)).2 _ (by norm_num) |>.mono
      fun _ h => h.le
  have E4a : ∀ᶠ D : ℝ in atTop, D ^ (-(2 - 4 * α)) ≤ 1 / 96 :=
    (tendsto_order.1 (tendsto_rpow_neg_atTop (by linarith : 0 < 2 - 4 * α))).2 _
      (by norm_num) |>.mono fun _ h => h.le
  have E4b : ∀ᶠ D : ℝ in atTop, (96 * r + 1) * D ^ (-(c' - 3 * α)) ≤ 1 / 16 := by
    have hpos : 0 < c' - 3 * α := by rw [hα]; linarith
    have h := (tendsto_rpow_neg_atTop hpos).const_mul (96 * (r : ℝ) + 1)
    rw [mul_zero] at h
    exact (tendsto_order.1 h).2 _ (by norm_num) |>.mono fun _ h => h.le
  filter_upwards [E1, E2, E3, E4a, E4b] with D hD1 hD2 hD3 hD4a hD4b
  intro c'' α' D₀ t p
  -- basic bounds
  have hD16 : 16 * r + 16 ≤ D := le_trans (le_max_right _ _) hD1
  have hDΔ : max Δ₀ 0 + 1 ≤ D := le_trans (le_max_left _ _) hD1
  have hD1' : (16 : ℝ) ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hD₀lo : D - 1 < D₀ := Nat.sub_one_lt_floor D
  have hD₀hi : (D₀ : ℝ) ≤ D := Nat.floor_le hDpos.le
  have hD₀half : D / 2 ≤ D₀ := by linarith
  have hD₀1 : (1 : ℝ) ≤ D₀ := by linarith
  have hD₀pos : (0 : ℝ) < D₀ := by linarith
  -- N3
  have N3 : D ^ (1 - β) ≤ (D₀ : ℝ) ^ (1 - β / 2) := by
    have h1 : (D / 2) ^ (1 - β / 2) ≤ (D₀ : ℝ) ^ (1 - β / 2) :=
      Real.rpow_le_rpow (by positivity) hD₀half (by linarith)
    have h2 : (2 : ℝ) ^ (1 - β / 2) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - β / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h3 : D ^ (1 - β / 2) = D ^ (1 - β) * D ^ (β / 2) := by
      rw [← Real.rpow_add hDpos]; ring_nf
    rw [Real.div_rpow hDpos.le (by norm_num)] at h1
    have h4 : D ^ (1 - β) ≤ D ^ (1 - β / 2) / 2 := by
      rw [h3]
      have : 0 ≤ D ^ (1 - β) := by positivity
      nlinarith
    have h5 : D ^ (1 - β / 2) / 2 ≤ D ^ (1 - β / 2) / (2 : ℝ) ^ (1 - β / 2) := by
      gcongr
    linarith
  -- `t` and `smax`
  have hDα1 : (1 : ℝ) ≤ D ^ (1 - α) := Real.one_le_rpow (by linarith) (by linarith)
  have hDαD : D ^ (1 - α) ≤ D := by
    calc D ^ (1 - α) ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by linarith)
      _ = D := Real.rpow_one D
  have ht_lo : D ^ (1 - α) ≤ t := Nat.le_ceil _
  have ht_hi : (t : ℝ) < D ^ (1 - α) + 1 := Nat.ceil_lt_add_one (by positivity)
  have htpos : (0 : ℝ) < t := by linarith
  have hsmax_hi : (⌊D ^ (1 - β)⌋₊ : ℝ) ≤ D ^ (1 - β) := Nat.floor_le (by positivity)
  have hDβD : D ^ (1 - β) ≤ D := by
    calc D ^ (1 - β) ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by linarith)
      _ = D := Real.rpow_one D
  refine ⟨hDpos.le, ?_, ?_, N3, ?_, ?_, ?_⟩
  · have : Δ₀ ≤ D - 1 := by linarith [le_max_left Δ₀ 0]
    linarith
  · rw [mul_one_sub_rpow_neg hD₀pos, mul_one_sub_rpow_neg hDpos]
    linarith
  · have h1 : D ≤ (D / 2) ^ 3 := by nlinarith
    exact h1.trans (by gcongr)
  · -- N5
    have h1 : (r : ℝ) * t * ⌊D ^ (1 - β)⌋₊ ≤ r * (D + 1) * D := by
      gcongr
      · linarith
      · linarith
    have h2 : (r : ℝ) * (D + 1) * D ≤ (D / 2) ^ 3 := by nlinarith
    exact h1.trans (h2.trans (by gcongr))
  -- `p`
  have hDα_le : D ^ α ≤ D ^ (1 - α) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    show D ^ α / t ≤ 1
    rw [div_le_one htpos]; linarith
  refine ⟨hp0, hp1, ?_⟩
  -- the Local Lemma condition
  have hpt : (t : ℝ) * p = D ^ α := by
    show (t : ℝ) * (D ^ α / t) = D ^ α
    field_simp
  have hT1 : (1 - p) ^ t ≤ Real.exp (-(D ^ α)) := by
    calc (1 - p) ^ t ≤ Real.exp (-p) ^ t :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) t
      _ = Real.exp (t * (-p)) := (Real.exp_nat_mul _ t).symm
      _ = Real.exp (-(D ^ α)) := by rw [← hpt]; ring_nf
  have hp_le : p ≤ D ^ (2 * α - 1) := by
    show D ^ α / t ≤ D ^ (2 * α - 1)
    rw [div_le_iff₀ htpos]
    calc D ^ α = D ^ (2 * α - 1) * D ^ (1 - α) := by
          rw [← Real.rpow_add hDpos]; ring_nf
      _ ≤ D ^ (2 * α - 1) * t := by gcongr
  have hT2 : p ^ 2 ≤ D ^ (-(2 - 4 * α)) := by
    calc p ^ 2 ≤ (D ^ (2 * α - 1)) ^ 2 := pow_le_pow_left₀ hp0 hp_le 2
      _ = D ^ (-(2 - 4 * α)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]; ring_nf
  -- `ΔB`
  have hΔB : (D₀ : ℝ) ^ (-c) * D + ⌊D ^ (1 - β)⌋₊ * (D₀ : ℝ) ^ (β / 2) ≤ 3 * D ^ (1 - c') := by
    have h1 : (D₀ : ℝ) ^ (-c) ≤ (D₀ : ℝ) ^ (-c') :=
      Real.rpow_le_rpow_of_exponent_le hD₀1 (by linarith)
    have h2 : (D₀ : ℝ) ^ (-c') ≤ (D / 2) ^ (-c') :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hD₀half (by linarith)
    have h3 : (D / 2) ^ (-c') ≤ 2 * D ^ (-c') := by
      rw [Real.div_rpow hDpos.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        neg_neg, mul_comm]
      gcongr
      calc (2 : ℝ) ^ c' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 : D ^ (-c') * D = D ^ (1 - c') := by
      rw [sub_eq_neg_add, Real.rpow_add hDpos, Real.rpow_one]
    have h5 : (⌊D ^ (1 - β)⌋₊ : ℝ) * (D₀ : ℝ) ^ (β / 2) ≤ D ^ (1 - β) * D ^ (β / 2) := by
      gcongr
    have h6 : D ^ (1 - β) * D ^ (β / 2) ≤ D ^ (1 - c') := by
      rw [← Real.rpow_add hDpos]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h7 : (D₀ : ℝ) ^ (-c) * D ≤ 2 * D ^ (1 - c') := by
      rw [← h4]
      have := h1.trans (h2.trans h3)
      nlinarith
    linarith
  have hΔB0 : 0 ≤ (D₀ : ℝ) ^ (-c) * D + ⌊D ^ (1 - β)⌋₊ * (D₀ : ℝ) ^ (β / 2) := by positivity
  have ht2 : (t : ℝ) + 2 ≤ 4 * D ^ (1 - α) := by linarith
  set F := 2 + 2 * r * ((D₀ : ℝ) ^ (-c) * D + ⌊D ^ (1 - β)⌋₊ * (D₀ : ℝ) ^ (β / 2)) * (t + 2) + 1
    with hF
  have hF1 : F ≤ 3 + 24 * r * D ^ (2 - c' - α) := by
    have h1 : 2 * r * ((D₀ : ℝ) ^ (-c) * D + ⌊D ^ (1 - β)⌋₊ * (D₀ : ℝ) ^ (β / 2)) * (t + 2) ≤
        2 * r * (3 * D ^ (1 - c')) * (4 * D ^ (1 - α)) := by
      gcongr
    have h2 : D ^ (1 - c') * D ^ (1 - α) = D ^ (2 - c' - α) := by
      rw [← Real.rpow_add hDpos]; ring_nf
    have : 2 * r * (3 * D ^ (1 - c')) * (4 * D ^ (1 - α)) = 24 * r * D ^ (2 - c' - α) := by
      rw [← h2]; ring
    linarith
  have hD2 : D ^ (2 - c' - α) ≤ D ^ 2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hF0 : 0 ≤ F := by positivity
  have hA : 4 * (1 - p) ^ t * F ≤ 1 / 2 := by
    have : 4 * (1 - p) ^ t * F ≤ 4 * Real.exp (-(D ^ α)) * (3 + 24 * r * D ^ 2) := by
      have h0 : 0 ≤ (1 - p) ^ t := pow_nonneg (by linarith) _
      have hF2 : F ≤ 3 + 24 * r * D ^ 2 := by nlinarith
      calc 4 * (1 - p) ^ t * F ≤ 4 * Real.exp (-(D ^ α)) * F := by gcongr
        _ ≤ 4 * Real.exp (-(D ^ α)) * (3 + 24 * r * D ^ 2) := by gcongr
    linarith
  have hB : 4 * p ^ 2 * F ≤ 1 / 2 := by
    have h1 : 4 * p ^ 2 * F ≤ 4 * D ^ (-(2 - 4 * α)) * (3 + 24 * r * D ^ (2 - c' - α)) := by
      gcongr
    have h2 : D ^ (-(2 - 4 * α)) * D ^ (2 - c' - α) = D ^ (-(c' - 3 * α)) := by
      rw [← Real.rpow_add hDpos]; ring_nf
    have h3 : 4 * D ^ (-(2 - 4 * α)) * (3 + 24 * r * D ^ (2 - c' - α)) =
        12 * D ^ (-(2 - 4 * α)) + 96 * r * D ^ (-(c' - 3 * α)) := by
      rw [← h2]; ring
    have h4 : 96 * r * D ^ (-(c' - 3 * α)) ≤ (96 * r + 1) * D ^ (-(c' - 3 * α)) := by
      have : 0 ≤ D ^ (-(c' - 3 * α)) := by positivity
      nlinarith
    linarith
  rcases le_total ((1 - p) ^ t) (p ^ 2) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- **Theorem 2.8 of arXiv:2402.17855v1 (Nibble with Reserves).** -/
theorem theorem_2_8 : RefinedAbsorption.Faithful2024.Theorem_2_8 := by
  intro r hr β hβ hβ1
  obtain ⟨c, hc, Δ₀, hNib⟩ := multiNibbleA r hr (β / 2) (by linarith) (by linarith) 3
  obtain ⟨Dst, hDst⟩ := eventually_atTop.1 (thm28_eventually r (Δ₀ := Δ₀) hβ hβ1 hc)
  set c' := min c (β / 2) with hc'
  have hc'0 : 0 < c' := lt_min hc (by linarith)
  have hc'β : c' ≤ β / 2 := min_le_right _ _
  refine ⟨⌈max Dst 0⌉₊, c' / 8, by positivity, by linarith, ?_⟩
  intro D hD V E _ _ ends V₁ V₂ A B G₁ G₂ hcard hcod _ hbip hBdeg hAres hV₁ hV hdeg1 hdegA
  have hD' : Dst ≤ D := le_trans (le_max_left _ _) (le_trans (Nat.le_ceil _) hD)
  obtain ⟨hD0, hΔ, N2, N3, N4, N5, hp0, hp1, N7⟩ := hDst D hD'
  exact thm28_core (hNib ⌊D⌋₊ hΔ) hD0 rfl rfl N2 N3 N4 N5 hp0 hp1 N7 V E ends V₁ V₂ A B G₁ G₂
    hcard hcod hbip hBdeg hAres hV₁ hV hdeg1 hdegA

end RefinedAbsorption.Pending
