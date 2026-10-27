module
public import RequestProject.Nibble.Params

/-!
# The nibble with test sets for nearly regular hypergraphs

`nearRegularNibble`: for `k ≥ 2`, `δ ∈ (0,1]` and `K ∈ ℕ` there are `c > 0` and `Δ₀` such that
for every `Δ ≥ Δ₀` the following holds.  Let `E` be a `k`-uniform hypergraph on a vertex set
`V` with `|V| ≤ Δ^K`, all of whose vertex degrees lie in `[Δ(1 - Δ^{-δ}), Δ]` and all of whose
codegrees are at most `Δ^{1-δ}`, and let `𝒯` be a family of at most `Δ^K` test sets.  Then there
is a matching `M ⊆ E` such that every test set `T` with `|T ∩ V| ≥ Δ^δ` has at most
`Δ^{-c} |T ∩ V|` vertices not covered by `M`.

This is proved from scratch by the iterated Rödl nibble (`nibble_of_params`); here we only check
that the finitely many numerical conditions on the parameters hold for large `Δ`.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset Filter

theorem ev_lin_exp_neg {p A ε : ℝ} (hp : 0 < p) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, A * (s + 1) * Real.exp (-(p * s)) ≤ ε := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (8 * (A + 1) / (p ^ 2 * ε))]
    with s hs1 hs2
  have hs0 : 0 < s := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ p * s by positivity)
  have hexp : (p * s) ^ 2 / 2 ≤ Real.exp (p * s) := by nlinarith [mul_pos hp hs0]
  have hE : 0 < Real.exp (p * s) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
  have h1 : A * (s + 1) ≤ (A + 1) * (2 * s) := by nlinarith
  have h2 : 8 * (A + 1) ≤ s * (p ^ 2 * ε) := by
    rw [div_le_iff₀ (by positivity)] at hs2; linarith
  have h3 : (A + 1) * (2 * s) ≤ ε * ((p * s) ^ 2 / 2) := by nlinarith
  nlinarith

theorem ev_exp_exp {K c p ε : ℝ} (hc : 0 < c) (hp : 0 < p) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, Real.exp (K * s) * Real.exp (-(c * Real.exp (p * s))) ≤ ε := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 * (K + 1) / (c * p ^ 2)),
    eventually_ge_atTop (-Real.log ε)] with s hs1 hs2 hs3
  have hs0 : 0 < s := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ p * s by positivity)
  have hexp : (p * s) ^ 2 / 2 ≤ Real.exp (p * s) := by nlinarith [mul_pos hp hs0]
  rw [← Real.exp_add]
  have h2 : 2 * (K + 1) ≤ s * (c * p ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at hs2; linarith
  have h4 : K * s + -(c * Real.exp (p * s)) ≤ Real.log ε := by
    have : c * ((p * s) ^ 2 / 2) ≤ c * Real.exp (p * s) := by gcongr
    nlinarith
  calc Real.exp (K * s + -(c * Real.exp (p * s))) ≤ Real.exp (Real.log ε) :=
        Real.exp_le_exp.2 h4
    _ = ε := Real.exp_log hε

theorem ev_exp_neg {p A ε : ℝ} (hp : 0 < p) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, A * Real.exp (-(p * s)) ≤ ε := by
  filter_upwards [ev_lin_exp_neg hp hA hε, eventually_ge_atTop 0] with s hs hs0
  have : A * Real.exp (-(p * s)) ≤ A * (s + 1) * Real.exp (-(p * s)) := by
    have := Real.exp_pos (-(p * s))
    have h2 := mul_nonneg (mul_nonneg hA hs0) this.le
    linarith
  linarith

/-- All numerical conditions of `nibble_of_params` hold for large `s`. -/
theorem ev_params (k K L : ℕ) (hk2 : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ s : ℝ in atTop, 0 ≤ s ∧
      k * Real.exp (-(δ / 8 * s)) ≤ 1 / 4 ∧
      2 ≤ (1 - δ / 32) * s ∧
      2 * k * Real.exp 2 ≤ Real.exp (31 * δ / 32 * s) ∧
      Real.exp 1 * Real.exp (-(δ / 16 * s)) *
        (1 + (δ / (64 * k) * s + 1) * (4 * k ^ 2 * (Real.exp 2 + 1) + 2)) ≤ 1 / 4 ∧
      2 ^ L * Real.exp (-s) ≤ 1 / 8 ∧
      2 * Real.exp (K * s) *
        Real.exp (-(Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2))) ≤ 1 / 8 ∧
      Real.exp (K * s) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k))) ≤ 1 / 8 ∧
      Real.exp (K * s) * Real.exp (-(160 * k * Real.exp (δ / 4 * s))) ≤ 1 / 8 ∧
      Real.exp (-(δ / (64 * k) / 2 * s)) + Real.exp (-(δ / 2 * s)) +
        320 * k ^ 2 * (1 + k * L) * (δ / (64 * k) * s + 1) * Real.exp (-(δ / 8 * s)) ≤
          Real.exp (-(δ / (64 * k) / 4 * s)) := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < k := by linarith
  set c₁ := δ / (64 * k) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hc₁δ : c₁ ≤ δ / 128 := by
    rw [hc₁, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set B := 4 * (k : ℝ) ^ 2 * (Real.exp 2 + 1) + 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- P1
  have e1 := ev_exp_neg (p := δ / 8) (A := k) (ε := 1 / 4) (by positivity) hkpos.le
    (by norm_num)
  -- P2
  have e2 : ∀ᶠ s : ℝ in atTop, 2 ≤ (1 - δ / 32) * s := by
    filter_upwards [eventually_ge_atTop 3] with s hs
    nlinarith
  -- P3
  have e3 : ∀ᶠ s : ℝ in atTop, 2 * k * Real.exp 2 ≤ Real.exp (31 * δ / 32 * s) := by
    filter_upwards [eventually_ge_atTop (2 * k * Real.exp 2 * (32 / (31 * δ)))] with s hs
    have h := Real.add_one_le_exp (31 * δ / 32 * s)
    have : 2 * k * Real.exp 2 ≤ 31 * δ / 32 * s := by
      have h' : 2 * k * Real.exp 2 * (32 / (31 * δ)) * (31 * δ / 32) = 2 * k * Real.exp 2 := by
        field_simp
      have : 2 * k * Real.exp 2 * (32 / (31 * δ)) * (31 * δ / 32) ≤ s * (31 * δ / 32) := by
        gcongr
      nlinarith
    linarith
  -- P4
  have e4 := ev_lin_exp_neg (p := δ / 16) (A := Real.exp 1 * (1 + B) * (1 + c₁)) (ε := 1 / 4)
    (by positivity) (by positivity) (by norm_num)
  -- P5
  have e5 := ev_exp_neg (p := 1) (A := 2 ^ L) (ε := 1 / 8) one_pos (by positivity) (by norm_num)
  -- P6
  have e6 := ev_exp_exp (K := K) (c := 1 / (16 * k ^ 2 * Real.exp 2)) (p := 19 * δ / 32)
    (ε := 1 / 16) (by positivity) (by positivity) (by norm_num)
  -- P7
  have e7 := ev_exp_exp (K := K) (c := 1 / (512 * k)) (p := 3 * δ / 8) (ε := 1 / 8)
    (by positivity) (by positivity) (by norm_num)
  -- P8
  have e8 := ev_exp_exp (K := K) (c := 160 * k) (p := δ / 4) (ε := 1 / 8)
    (by positivity) (by positivity) (by norm_num)
  -- P9
  have e9a := ev_exp_neg (p := c₁ / 4) (A := 1) (ε := 1 / 3) (by positivity) zero_le_one
    (by norm_num)
  have e9b := ev_exp_neg (p := δ / 2 - c₁ / 4) (A := 1) (ε := 1 / 3) (by linarith) zero_le_one
    (by norm_num)
  have e9c := ev_lin_exp_neg (p := δ / 8 - c₁ / 4)
    (A := 320 * k ^ 2 * (1 + k * L) * (1 + c₁)) (ε := 1 / 3) (by linarith) (by positivity)
    (by norm_num)
  filter_upwards [eventually_ge_atTop 0, e1, e2, e3, e4, e5, e6, e7, e8, e9a, e9b, e9c]
    with s hs0 h1 h2 h3 h4 h5 h6 h7 h8 h9a h9b h9c
  refine ⟨hs0, h1, h2, h3, ?_, by simpa only [one_mul] using h5, ?_, ?_, ?_, ?_⟩
  · have hle : 1 + (c₁ * s + 1) * B ≤ (1 + B) * (1 + c₁) * (s + 1) := by nlinarith
    calc Real.exp 1 * Real.exp (-(δ / 16 * s)) * (1 + (c₁ * s + 1) * B)
        ≤ Real.exp 1 * Real.exp (-(δ / 16 * s)) * ((1 + B) * (1 + c₁) * (s + 1)) := by gcongr
      _ = Real.exp 1 * (1 + B) * (1 + c₁) * (s + 1) * Real.exp (-(δ / 16 * s)) := by ring
      _ ≤ 1 / 4 := h4
  · have : Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2) =
        1 / (16 * k ^ 2 * Real.exp 2) * Real.exp (19 * δ / 32 * s) := by ring
    rw [this]; linarith
  · have : Real.exp (3 * δ / 8 * s) / (512 * k) = 1 / (512 * k) * Real.exp (3 * δ / 8 * s) := by
      ring
    rw [this]; exact h7
  · exact h8
  · -- divide by `exp(-(c₁/4) s)`
    have hE : 0 < Real.exp (-(c₁ / 4 * s)) := Real.exp_pos _
    have ha : Real.exp (-(c₁ / 2 * s)) = Real.exp (-(c₁ / 4 * s)) * Real.exp (-(c₁ / 4 * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hb : Real.exp (-(δ / 2 * s)) =
        Real.exp (-(c₁ / 4 * s)) * Real.exp (-((δ / 2 - c₁ / 4) * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hc : Real.exp (-(δ / 8 * s)) =
        Real.exp (-(c₁ / 4 * s)) * Real.exp (-((δ / 8 - c₁ / 4) * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hle : 320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) ≤
        320 * k ^ 2 * (1 + k * L) * (1 + c₁) * (s + 1) := by
      have h0 : (0 : ℝ) ≤ 320 * k ^ 2 * (1 + k * L) := by positivity
      have h1 : c₁ * s + 1 ≤ (1 + c₁) * (s + 1) := by nlinarith
      calc 320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1)
          ≤ 320 * k ^ 2 * (1 + k * L) * ((1 + c₁) * (s + 1)) := mul_le_mul_of_nonneg_left h1 h0
        _ = 320 * k ^ 2 * (1 + k * L) * (1 + c₁) * (s + 1) := by ring
    have hpos : 0 ≤ Real.exp (-((δ / 8 - c₁ / 4) * s)) := (Real.exp_pos _).le
    have h9c' : 320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) * Real.exp (-((δ / 8 - c₁ / 4) * s))
        ≤ 1 / 3 := by
      calc 320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) * Real.exp (-((δ / 8 - c₁ / 4) * s))
          ≤ 320 * k ^ 2 * (1 + k * L) * (1 + c₁) * (s + 1) *
              Real.exp (-((δ / 8 - c₁ / 4) * s)) := by gcongr
        _ ≤ 1 / 3 := h9c
    rw [ha, hb, hc]
    have h9a' : Real.exp (-(c₁ / 4 * s)) ≤ 1 / 3 := by simpa using h9a
    have h9b' : Real.exp (-((δ / 2 - c₁ / 4) * s)) ≤ 1 / 3 := by simpa using h9b
    have : Real.exp (-(c₁ / 4 * s)) * Real.exp (-(c₁ / 4 * s)) +
        Real.exp (-(c₁ / 4 * s)) * Real.exp (-((δ / 2 - c₁ / 4) * s)) +
        320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) *
          (Real.exp (-(c₁ / 4 * s)) * Real.exp (-((δ / 8 - c₁ / 4) * s))) =
        Real.exp (-(c₁ / 4 * s)) * (Real.exp (-(c₁ / 4 * s)) +
          Real.exp (-((δ / 2 - c₁ / 4) * s)) +
          320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) * Real.exp (-((δ / 8 - c₁ / 4) * s))) := by
      ring
    rw [this]
    calc Real.exp (-(c₁ / 4 * s)) * (Real.exp (-(c₁ / 4 * s)) +
          Real.exp (-((δ / 2 - c₁ / 4) * s)) +
          320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) * Real.exp (-((δ / 8 - c₁ / 4) * s)))
        ≤ Real.exp (-(c₁ / 4 * s)) * 1 := by gcongr; linarith
      _ = Real.exp (-(c₁ / 4 * s)) := mul_one _

/-- **Pseudorandom matchings with test sets in nearly regular hypergraphs** (statement). -/
def NearRegularNibble : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℝ, ∀ Δ : ℝ,
    Δ₀ ≤ Δ → ∀ (α : Type) [DecidableEq α] (E : Finset (Finset α)) (V : Finset α)
      (𝒯 : Finset (Finset α)),
      (∀ F ∈ E, F.card = k) → (∀ F ∈ E, F ⊆ V) →
      (∀ v ∈ V, Δ * (1 - Δ ^ (-δ)) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ Δ) →
      (∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ Δ ^ (1 - δ)) →
      (V.card : ℝ) ≤ Δ ^ K → (𝒯.card : ℝ) ≤ Δ ^ K →
      ∃ M ⊆ E, (∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
        ∀ T ∈ 𝒯, Δ ^ δ ≤ (T ∩ V).card →
          (((T ∩ V) \ cov M).card : ℝ) ≤ Δ ^ (-c) * (T ∩ V).card

/-- **Pseudorandom matchings with test sets in nearly regular hypergraphs**, proved by the
iterated nibble. -/
theorem nearRegularNibble : NearRegularNibble := by
  intro k hk2 δ hδ hδ1 K
  set L : ℕ := ⌈8 * (K + 1) / δ⌉₊ with hL
  have hLK : (K + 1 : ℝ) ≤ δ / 8 * L := by
    have := Nat.le_ceil (8 * (K + 1) / δ)
    rw [← hL, div_le_iff₀ hδ] at this
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨δ / (64 * k) / 4, by positivity, ?_⟩
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 (ev_params k K L hk2 hδ hδ1)
  refine ⟨Real.exp s₀, fun Δ hΔ α _ E V 𝒯 hk hEV hdeg hcod hV h𝒯 => ?_⟩
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (Real.exp_pos _) hΔ
  set s := Real.log Δ with hs
  have hss₀ : s₀ ≤ s := by
    rw [hs, ← Real.log_exp s₀]; exact Real.log_le_log (Real.exp_pos _) hΔ
  have hΔs : Δ = Real.exp s := (Real.exp_log hΔ0).symm
  have hrpow : ∀ x : ℝ, Δ ^ x = Real.exp (x * s) := fun x => by
    rw [Real.rpow_def_of_pos hΔ0, mul_comm]
  have hpow : (Δ : ℝ) ^ K = Real.exp (K * s) := by rw [hΔs, ← Real.exp_nat_mul]
  obtain ⟨hs0, P1, P2, P3, P4, P5, P6, P7, P8, P9⟩ := hs₀ s hss₀
  obtain ⟨M, hME, hMdisj, hMT⟩ := nibble_of_params hk2 hδ hLK hs0 P1 P2 P3 P4 P5 P6 P7 P8 P9
    E V 𝒯 hk hEV
    (fun v hv => by
      have h := hdeg v hv
      rw [hrpow, show -δ * s = -(δ * s) by ring] at h
      rw [← hΔs]
      exact h)
    (fun u v huv => by have := hcod u v huv; rwa [hrpow] at this)
    (by rw [← hpow]; exact hV) (by rw [← hpow]; exact h𝒯)
  refine ⟨M, hME, hMdisj, fun T hT hTbig => ?_⟩
  have h := hMT T hT (by rwa [hrpow] at hTbig)
  rw [hrpow, show -(δ / (64 * k) / 4) * s = -(δ / (64 * k) / 4 * s) by ring]
  exact h

end RefinedAbsorption.Nibble
