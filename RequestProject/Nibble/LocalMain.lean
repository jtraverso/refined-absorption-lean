module
public import RequestProject.Nibble.LocalIterate
public import RequestProject.Nibble.Main

/-!
# The nibble without a bound on the number of vertices

`localNibble`: the statement of `nearRegularNibble` in which the bounds `|V| ≤ Δ^K` and
`|𝒯| ≤ Δ^K` are replaced by local bounds — every test set has at most `Δ^K` elements and every
vertex lies in at most `Δ^K` test sets.  The proof is the same iterated nibble, with the union
bound in each round replaced by the Lovász Local Lemma.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset Filter

theorem params_prob_real {k K L : ℕ} {δ s θ : ℝ} (N : ℝ)
    (hk2 : 2 ≤ k) (hL : (K + 1 : ℝ) ≤ δ / 8 * L) (hs : 0 ≤ s)
    (hθdef : θ = Real.exp (-(δ / 8 * s)))
    (P5 : 2 ^ L * Real.exp (-s) ≤ 1 / 8)
    (P6 : 2 * Real.exp (K * s) *
      Real.exp (-(Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2))) ≤ 1 / 8)
    (P7 : Real.exp (K * s) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k))) ≤ 1 / 8)
    (P8 : Real.exp (K * s) * Real.exp (-(160 * k * Real.exp (δ / 4 * s))) ≤ 1 / 8)
    (hN : N ≤ Real.exp (K * s))
    {D : ℝ} (hD : Real.exp ((1 - δ / 32) * s - 2) ≤ D) :
    N * (2 * θ) ^ L
      + 2 * N * Real.exp (-(θ * θ ^ 2 * D / (16 * k ^ 2 * Real.exp ((1 - δ) * s))))
      + N * (Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) +
        Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s)))) < 1 := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < k := by linarith
  have hA : N * (2 * θ) ^ L ≤ 1 / 8 := by
    have h1 : (2 * θ) ^ L = 2 ^ L * Real.exp (-(δ / 8 * L * s)) := by
      rw [mul_pow, hθdef, ← Real.exp_nat_mul]; congr 2; ring
    rw [h1]
    have h2 : Real.exp (K * s + -(δ / 8 * L * s)) ≤ Real.exp (-s) := by
      apply Real.exp_le_exp.2; nlinarith
    calc N * (2 ^ L * Real.exp (-(δ / 8 * L * s)))
        ≤ Real.exp (K * s) * (2 ^ L * Real.exp (-(δ / 8 * L * s))) := by gcongr
      _ = 2 ^ L * Real.exp (K * s + -(δ / 8 * L * s)) := by rw [Real.exp_add]; ring
      _ ≤ 2 ^ L * Real.exp (-s) := by gcongr
      _ ≤ 1 / 8 := P5
  have hB : 2 * N *
      Real.exp (-(θ * θ ^ 2 * D / (16 * k ^ 2 * Real.exp ((1 - δ) * s)))) ≤ 1 / 8 := by
    have h1 : θ * θ ^ 2 * Real.exp ((1 - δ / 32) * s - 2) /
        (16 * k ^ 2 * Real.exp ((1 - δ) * s)) =
        Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      have h2 : θ * θ ^ 2 * Real.exp ((1 - δ / 32) * s - 2) * Real.exp 2 =
          Real.exp (19 * δ / 32 * s) * Real.exp ((1 - δ) * s) := by
        rw [hθdef, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add]
        congr 1; push_cast; ring
      calc θ * θ ^ 2 * Real.exp ((1 - δ / 32) * s - 2) * (16 * k ^ 2 * Real.exp 2)
          = 16 * k ^ 2 * (θ * θ ^ 2 * Real.exp ((1 - δ / 32) * s - 2) * Real.exp 2) := by ring
        _ = 16 * k ^ 2 * (Real.exp (19 * δ / 32 * s) * Real.exp ((1 - δ) * s)) := by rw [h2]
        _ = _ := by ring
    have hexp : Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2) ≤
        θ * θ ^ 2 * D / (16 * k ^ 2 * Real.exp ((1 - δ) * s)) := by
      rw [← h1]
      have hθ0 : 0 < θ := by rw [hθdef]; exact Real.exp_pos _
      gcongr
    calc 2 * N * Real.exp (-(θ * θ ^ 2 * D / (16 * k ^ 2 * Real.exp ((1 - δ) * s))))
        ≤ 2 * Real.exp (K * s) *
          Real.exp (-(Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2))) := by
          gcongr
      _ ≤ 1 / 8 := P6
  have hC1 : N * Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) ≤ 1 / 8 := by
    have : θ * Real.exp (δ / 2 * s) = Real.exp (3 * δ / 8 * s) := by
      rw [hθdef, ← Real.exp_add]; congr 1; ring
    rw [this]
    calc N * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k)))
        ≤ Real.exp (K * s) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k))) := by gcongr
      _ ≤ 1 / 8 := P7
  have hC2 : N * Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s))) ≤ 1 / 8 := by
    have : 160 * k * θ ^ 2 * Real.exp (δ / 2 * s) = 160 * k * Real.exp (δ / 4 * s) := by
      rw [hθdef, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2; push_cast; ring
    rw [this]
    calc N * Real.exp (-(160 * k * Real.exp (δ / 4 * s)))
        ≤ Real.exp (K * s) * Real.exp (-(160 * k * Real.exp (δ / 4 * s))) := by gcongr
      _ ≤ 1 / 8 := P8
  have : N * (Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) +
      Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s)))) =
      N * Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) +
      N * Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s))) := by ring
  linarith

theorem count_bound {k Mt A Di : ℝ} (hk : 1 ≤ k) (hMt : 1 ≤ Mt) (hA : 1 ≤ A) (hDi0 : 0 ≤ Di)
    (hDiA : Di ≤ A) (P10 : 132 * k ^ 3 ≤ A) :
    4 * ((k * (Mt + 1) * (2 * Di) ^ 2) * ((k * k * (2 * Di)) * (Mt + 1)) + 1) ≤ A ^ 4 * Mt ^ 2 := by
  have hX : (k * (Mt + 1) * (2 * Di) ^ 2) * ((k * k * (2 * Di)) * (Mt + 1)) ≤
      (k * (2 * Mt) * (2 * A) ^ 2) * ((k * k * (2 * A)) * (2 * Mt)) := by
    gcongr <;> linarith
  have hprod : (1 : ℝ) ≤ k ^ 3 * A ^ 3 * Mt ^ 2 := by
    have h0 : (1 : ℝ) ≤ k ^ 3 := one_le_pow₀ hk
    have h1 : (1 : ℝ) ≤ A ^ 3 := one_le_pow₀ hA
    have h2 : (1 : ℝ) ≤ Mt ^ 2 := one_le_pow₀ hMt
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ k ^ 3 * A ^ 3 * Mt ^ 2 := by gcongr
  have h132 : 132 * k ^ 3 * (A ^ 3 * Mt ^ 2) ≤ A * (A ^ 3 * Mt ^ 2) :=
    mul_le_mul_of_nonneg_right P10 (by positivity)
  have hX' : (k * (Mt + 1) * (2 * Di) ^ 2) * ((k * k * (2 * Di)) * (Mt + 1)) ≤
      32 * (k ^ 3 * A ^ 3 * Mt ^ 2) := hX.trans (le_of_eq (by ring))
  have e1 : 132 * k ^ 3 * (A ^ 3 * Mt ^ 2) = 132 * (k ^ 3 * A ^ 3 * Mt ^ 2) := by ring
  have e2 : A * (A ^ 3 * Mt ^ 2) = A ^ 4 * Mt ^ 2 := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **The nibble with explicit parameters, via the Local Lemma.**  Instead of bounds on `|V|`
and `|𝒯|`, every test set has at most `e^{Ks}` elements and every vertex is in at most `e^{Ks}`
test sets; the probabilistic conditions use the exponent `K' = 2K + 4`. -/
theorem nibble_of_params_lll {α : Type*} [DecidableEq α] {k K K' L : ℕ} {δ s : ℝ}
    (hK' : K' = 2 * K + 4)
    (hk2 : 2 ≤ k) (hδ : 0 < δ) (hL : (K' + 1 : ℝ) ≤ δ / 8 * L) (hs : 0 ≤ s)
    (P1 : k * Real.exp (-(δ / 8 * s)) ≤ 1 / 4)
    (P2 : 2 ≤ (1 - δ / 32) * s)
    (P3 : 2 * k * Real.exp 2 ≤ Real.exp (31 * δ / 32 * s))
    (P4 : Real.exp 1 * Real.exp (-(δ / 16 * s)) *
      (1 + (δ / (64 * k) * s + 1) * (4 * k ^ 2 * (Real.exp 2 + 1) + 2)) ≤ 1 / 4)
    (P5 : 2 ^ L * Real.exp (-s) ≤ 1 / 8)
    (P6 : 2 * Real.exp (K' * s) *
      Real.exp (-(Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2))) ≤ 1 / 8)
    (P7 : Real.exp (K' * s) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k))) ≤ 1 / 8)
    (P8 : Real.exp (K' * s) * Real.exp (-(160 * k * Real.exp (δ / 4 * s))) ≤ 1 / 8)
    (P9 : Real.exp (-(δ / (64 * k) / 2 * s)) + Real.exp (-(δ / 2 * s)) +
      320 * k ^ 2 * (1 + k * L) * (δ / (64 * k) * s + 1) * Real.exp (-(δ / 8 * s)) ≤
        Real.exp (-(δ / (64 * k) / 4 * s)))
    (P10 : 132 * (k : ℝ) ^ 3 ≤ Real.exp s)
    (E : Finset (Finset α)) (V : Finset α) (𝒯 : Finset (Finset α))
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, Real.exp s * (1 - Real.exp (-(δ * s))) ≤ (star E v).card ∧
      ((star E v).card : ℝ) ≤ Real.exp s)
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ Real.exp ((1 - δ) * s))
    (h𝒯size : ∀ T ∈ 𝒯, (T.card : ℝ) ≤ Real.exp (K * s))
    (h𝒯mult : ∀ w : α, ((𝒯.filter (fun T => w ∈ T)).card : ℝ) ≤ Real.exp (K * s)) :
    ∃ M ⊆ E, (∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
      ∀ T ∈ 𝒯, Real.exp (δ * s) ≤ (T ∩ V).card →
        (((T ∩ V) \ cov M).card : ℝ) ≤ Real.exp (-(δ / (64 * k) / 4 * s)) * (T ∩ V).card := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < k := by linarith
  set c₁ := δ / (64 * k) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set θ := Real.exp (-(δ / 8 * s)) with hθdef
  have hθ0 : 0 < θ := Real.exp_pos _
  have hθ1 : θ ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set R : ℕ := ⌈c₁ * s / θ⌉₊ with hR
  have hRθ_lo : c₁ * s ≤ R * θ := by
    have := Nat.le_ceil (c₁ * s / θ)
    rw [← hR] at this
    rwa [div_le_iff₀ hθ0] at this
  have hRθ_hi : R * θ ≤ c₁ * s + θ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ c₁ * s / θ by positivity)
    rw [← hR] at this
    have h2 : (R : ℝ) * θ < (c₁ * s / θ + 1) * θ := mul_lt_mul_of_pos_right this hθ0
    rw [add_mul, div_mul_cancel₀ _ hθ0.ne', one_mul] at h2
    linarith
  have hDi := params_deg (δ := δ) (s := s) hk2 hθ0 P1 hRθ_hi
  have herr := params_err hk2 hδ hs hθdef hRθ_hi P1 hDi P4
  have hDmin1 : 1 ≤ Real.exp ((1 - δ / 32) * s - 2) := Real.one_le_exp (by linarith)
  set Mt := Real.exp (K * s) with hMt
  have hMt1 : 1 ≤ Mt := Real.one_le_exp (by positivity)
  have hA1 : 1 ≤ Real.exp s := Real.one_le_exp hs
  have hx0 : 0 ≤ 1 - (k - 1) * θ := by nlinarith
  have hx1 : 1 - (k - 1) * θ ≤ 1 := by nlinarith
  have hDup : ∀ i : ℕ, Real.exp s * (1 - (k - 1) * θ) ^ i ≤ Real.exp s := by
    intro i
    exact mul_le_of_le_one_right (Real.exp_pos s).le (pow_le_one₀ hx0 hx1)
  have hN : ∀ i : ℕ, 4 * ((k * (Mt + 1) * (2 * (Real.exp s * (1 - (k - 1) * θ) ^ i)) ^ 2) *
      ((k * k * (2 * (Real.exp s * (1 - (k - 1) * θ) ^ i))) * (Mt + 1)) + 1) ≤
        Real.exp (K' * s) := by
    intro i
    have hexp : Real.exp (K' * s) = Real.exp s ^ 4 * Mt ^ 2 := by
      rw [hK', hMt, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    rw [hexp]
    exact count_bound (by linarith) hMt1 hA1 (by positivity) (hDup i) P10
  obtain ⟨M, hME, hMdisj, hMT⟩ := nibble_iterate_lll (D0 := Real.exp s)
    (e0 := Real.exp (-(δ * s)))
    (C := Real.exp ((1 - δ) * s)) (θ := θ) (η := θ) (τ := Real.exp (δ / 2 * s))
    (ζ := 160 * k * θ ^ 2) (R := R) (L := L) 𝒯 hk2 hk hEV
    (fun v hv => ⟨(hdeg v hv).1, (hdeg v hv).2.trans (by
      have := Real.exp_pos (-(δ * s)); nlinarith [Real.exp_pos s])⟩) hcod (Real.exp_pos s)
    (Real.exp_pos _) (Real.exp_pos _).le hθ0 P1 hθ0 hθ1 (Real.exp_pos _) le_rfl
    hMt1 h𝒯size h𝒯mult
    (fun i hi => ⟨hDmin1.trans (hDi i hi.le), params_kC P3 (hDi i hi.le), herr i hi.le, by
      have h := params_prob_real _ hk2 hL hs hθdef P5 P6 P7 P8 (hN i) (hDi i hi.le)
      linarith⟩)
  refine ⟨M, hME, hMdisj, fun T hT hTbig => ?_⟩
  have h := hMT T hT
  set X0 := ((T ∩ V).card : ℝ)
  have hX0 : 0 ≤ X0 := Nat.cast_nonneg _
  have h1 : (1 - θ / 2) ^ R ≤ Real.exp (-(c₁ / 2 * s)) := by
    refine (one_sub_pow_le_exp' (by linarith) R).trans
      (Real.exp_le_exp.2 ?_)
    have : θ / 2 * R = (R * θ) / 2 := by ring
    rw [this]; linarith
  have h2 : Real.exp (δ / 2 * s) ≤ Real.exp (-(δ / 2 * s)) * X0 := by
    calc Real.exp (δ / 2 * s) = Real.exp (-(δ / 2 * s)) * Real.exp (δ * s) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(δ / 2 * s)) * X0 := by gcongr
  have h3 : (R : ℝ) * (2 * k * (1 + k * L) * (160 * k * θ ^ 2)) ≤
      320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) * Real.exp (-(δ / 8 * s)) := by
    have e1 : (R : ℝ) * (2 * k * (1 + k * L) * (160 * k * θ ^ 2)) =
        320 * k ^ 2 * (1 + k * L) * (R * θ) * θ := by ring
    rw [e1]
    have : (R : ℝ) * θ ≤ c₁ * s + 1 := by linarith
    gcongr
  calc (((T ∩ V) \ cov M).card : ℝ)
      ≤ (1 - θ / 2) ^ R * X0 + Real.exp (δ / 2 * s) +
          R * (2 * k * (1 + k * L) * (160 * k * θ ^ 2)) * X0 := h
    _ ≤ Real.exp (-(c₁ / 2 * s)) * X0 + Real.exp (-(δ / 2 * s)) * X0 +
          320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) * Real.exp (-(δ / 8 * s)) * X0 := by
        gcongr
    _ = (Real.exp (-(c₁ / 2 * s)) + Real.exp (-(δ / 2 * s)) +
          320 * k ^ 2 * (1 + k * L) * (c₁ * s + 1) * Real.exp (-(δ / 8 * s))) * X0 := by ring
    _ ≤ Real.exp (-(c₁ / 4 * s)) * X0 := by gcongr

/-- **Pseudorandom matchings with local test sets** (statement).  As `NearRegularNibble`, but
with no bound on the number of vertices or of test sets: it suffices that every test set has
at most `Δ^K` elements and every vertex lies in at most `Δ^K` test sets. -/
def LocalNibble : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℝ, ∀ Δ : ℝ,
    Δ₀ ≤ Δ → ∀ (α : Type) [DecidableEq α] (E : Finset (Finset α)) (V : Finset α)
      (𝒯 : Finset (Finset α)),
      (∀ F ∈ E, F.card = k) → (∀ F ∈ E, F ⊆ V) →
      (∀ v ∈ V, Δ * (1 - Δ ^ (-δ)) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ Δ) →
      (∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ Δ ^ (1 - δ)) →
      (∀ T ∈ 𝒯, (T.card : ℝ) ≤ Δ ^ K) →
      (∀ v : α, ((𝒯.filter (fun T => v ∈ T)).card : ℝ) ≤ Δ ^ K) →
      ∃ M ⊆ E, (∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
        ∀ T ∈ 𝒯, Δ ^ δ ≤ (T ∩ V).card →
          (((T ∩ V) \ cov M).card : ℝ) ≤ Δ ^ (-c) * (T ∩ V).card

/-- **Pseudorandom matchings with local test sets**, proved by the iterated nibble and the
Lovász Local Lemma. -/
theorem localNibble : LocalNibble := by
  intro k hk2 δ hδ hδ1 K
  set K' : ℕ := 2 * K + 4 with hK'
  set L : ℕ := ⌈8 * (K' + 1) / δ⌉₊ with hL
  have hLK : (K' + 1 : ℝ) ≤ δ / 8 * L := by
    have := Nat.le_ceil (8 * (K' + 1) / δ)
    rw [← hL, div_le_iff₀ hδ] at this
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨δ / (64 * k) / 4, by positivity, ?_⟩
  have ev10 : ∀ᶠ s : ℝ in atTop, 132 * (k : ℝ) ^ 3 ≤ Real.exp s := by
    filter_upwards [eventually_ge_atTop (Real.log (132 * (k : ℝ) ^ 3))] with s hs
    calc 132 * (k : ℝ) ^ 3 = Real.exp (Real.log (132 * (k : ℝ) ^ 3)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp s := Real.exp_le_exp.2 hs
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 ((ev_params k K' L hk2 hδ hδ1).and ev10)
  refine ⟨Real.exp s₀, fun Δ hΔ α _ E V 𝒯 hk hEV hdeg hcod hsize hmult => ?_⟩
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (Real.exp_pos _) hΔ
  set s := Real.log Δ with hs
  have hss₀ : s₀ ≤ s := by
    rw [hs, ← Real.log_exp s₀]; exact Real.log_le_log (Real.exp_pos _) hΔ
  have hΔs : Δ = Real.exp s := (Real.exp_log hΔ0).symm
  have hrpow : ∀ x : ℝ, Δ ^ x = Real.exp (x * s) := fun x => by
    rw [Real.rpow_def_of_pos hΔ0, mul_comm]
  have hpow : (Δ : ℝ) ^ K = Real.exp (K * s) := by rw [hΔs, ← Real.exp_nat_mul]
  obtain ⟨⟨hs0, P1, P2, P3, P4, P5, P6, P7, P8, P9⟩, P10⟩ := hs₀ s hss₀
  obtain ⟨M, hME, hMdisj, hMT⟩ := nibble_of_params_lll hK' hk2 hδ hLK hs0 P1 P2 P3 P4 P5 P6 P7
    P8 P9 P10 E V 𝒯 hk hEV
    (fun v hv => by
      have h := hdeg v hv
      rw [hrpow, show -δ * s = -(δ * s) by ring] at h
      rw [← hΔs]
      exact h)
    (fun u v huv => by have := hcod u v huv; rwa [hrpow] at this)
    (fun T hT => by rw [← hpow]; exact hsize T hT) (fun w => by rw [← hpow]; exact hmult w)
  refine ⟨M, hME, hMdisj, fun T hT hTbig => ?_⟩
  have h := hMT T hT (by rwa [hrpow] at hTbig)
  rw [hrpow, show -(δ / (64 * k) / 4) * s = -(δ / (64 * k) / 4 * s) by ring]
  exact h

end RefinedAbsorption.Nibble
