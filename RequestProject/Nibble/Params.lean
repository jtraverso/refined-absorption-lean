module
public import RequestProject.Nibble.Iterate

/-!
# Choice of parameters for the iterated nibble

All parameters are powers of `Δ = e^s`:  `θ = η = Δ^{-δ/8}`, `τ = Δ^{δ/2}`, `ζ = 160kθ²`,
`C = Δ^{1-δ}`, `R = ⌈c₁ log Δ / θ⌉` rounds with `c₁ = δ/(64k)`, and `L` with `(δ/8) L ≥ K + 1`.
`nibble_of_params` shows that, if `s` satisfies finitely many explicit numerical conditions
(all of which hold for large `s`), the iterated nibble leaves at most `Δ^{-c₁/4} |T ∩ V|`
vertices of every test set uncovered.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

theorem one_sub_ge_exp_neg_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have := exp_neg_le_quad (show 0 ≤ 2 * x by linarith) (by linarith)
  nlinarith

theorem one_sub_pow_ge_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (n : ℕ) :
    Real.exp (-(2 * x * n)) ≤ (1 - x) ^ n := by
  calc Real.exp (-(2 * x * n)) = Real.exp (-(2 * x)) ^ n := by
        rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ (1 - x) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le (one_sub_ge_exp_neg_two hx0 hx) n

theorem one_sub_pow_le_exp' {x : ℝ} (hx : x ≤ 1) (n : ℕ) :
    (1 - x) ^ n ≤ Real.exp (-(x * n)) := by
  calc (1 - x) ^ n ≤ Real.exp (-x) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-x)]) n
    _ = Real.exp (-(x * n)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- Growth of the error sequence. -/
theorem errSeq_le {k θ η C D0 e0 β : ℝ} (hk : 0 ≤ k) (hθ : 0 ≤ θ) (i : ℕ)
    (hβ : ∀ j < i, 4 * k ^ 2 * θ * (C / (D0 * (1 - (k - 1) * θ) ^ j) + θ) + 2 * θ * η ≤ θ * β)
    (hβ0 : 0 ≤ θ * β) :
    errSeq k θ η C D0 e0 i ≤ (1 + 4 * k * θ) ^ i * (e0 + i * (θ * β)) := by
  induction i with
  | zero => simp [errSeq]
  | succ j ih =>
    have ih' := ih (fun l hl => hβ l (by omega))
    have hj := hβ j (by omega)
    have h1 : 1 ≤ (1 + 4 * k * θ) := by nlinarith
    have h1j : 1 ≤ (1 + 4 * k * θ) ^ (j + 1) := one_le_pow₀ h1
    simp only [errSeq]
    calc errSeq k θ η C D0 e0 j + 4 * k * θ * errSeq k θ η C D0 e0 j +
          4 * k ^ 2 * θ * (C / (D0 * (1 - (k - 1) * θ) ^ j) + θ) + 2 * θ * η
        ≤ (1 + 4 * k * θ) * errSeq k θ η C D0 e0 j + θ * β := by linarith
      _ ≤ (1 + 4 * k * θ) * ((1 + 4 * k * θ) ^ j * (e0 + j * (θ * β))) + θ * β := by
          gcongr
      _ ≤ (1 + 4 * k * θ) ^ (j + 1) * (e0 + (j + 1 : ℕ) * (θ * β)) := by
          have h2 := mul_le_mul_of_nonneg_right h1j hβ0
          have h3 : (1 + 4 * k * θ) ^ (j + 1) * (e0 + (j + 1 : ℕ) * (θ * β)) =
              (1 + 4 * k * θ) * ((1 + 4 * k * θ) ^ j * (e0 + j * (θ * β))) +
              (1 + 4 * k * θ) ^ (j + 1) * (θ * β) := by
            push_cast; ring
          linarith

theorem params_deg {k : ℕ} {δ s θ : ℝ} {R : ℕ} (hk2 : 2 ≤ k) (hθ0 : 0 < θ)
    (hkθ : k * θ ≤ 1 / 4) (hRhi : (R : ℝ) * θ ≤ δ / (64 * k) * s + θ) :
    ∀ i ≤ R, Real.exp ((1 - δ / 32) * s - 2) ≤ Real.exp s * (1 - (k - 1) * θ) ^ i := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hx0 : 0 ≤ (k - 1) * θ := mul_nonneg (by linarith) hθ0.le
  have hxk : (k - 1) * θ ≤ k * θ := by nlinarith
  have hx1 : (k - 1) * θ ≤ 1 / 4 := hxk.trans hkθ
  intro i hi
  have h1 : Real.exp (-(2 * ((k - 1) * θ) * R)) ≤ (1 - (k - 1) * θ) ^ i := by
    refine (one_sub_pow_ge_exp hx0 hx1 R).trans ?_
    exact pow_le_pow_of_le_one (by linarith) (by linarith) hi
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have h3 : 2 * ((k - 1) * θ) * R ≤ 2 * k * (R * θ) := by
    have := mul_le_mul_of_nonneg_right hxk hR0
    linarith
  have h4 : 2 * k * (R * θ) ≤ 2 * k * (δ / (64 * k) * s + θ) :=
    mul_le_mul_of_nonneg_left hRhi (by linarith)
  have h5 : 2 * k * (δ / (64 * k) * s + θ) = δ / 32 * s + 2 * (k * θ) := by
    field_simp; ring
  have h2 : (1 - δ / 32) * s - 2 ≤ s + -(2 * ((k - 1) * θ) * R) := by linarith
  calc Real.exp ((1 - δ / 32) * s - 2) ≤ Real.exp (s + -(2 * ((k - 1) * θ) * R)) :=
        Real.exp_le_exp.2 h2
    _ = Real.exp s * Real.exp (-(2 * ((k - 1) * θ) * R)) := Real.exp_add _ _
    _ ≤ Real.exp s * (1 - (k - 1) * θ) ^ i := by gcongr

theorem params_err {k : ℕ} {δ s θ : ℝ} {R : ℕ} (hk2 : 2 ≤ k) (hδ : 0 < δ)
    (hs : 0 ≤ s) (hθdef : θ = Real.exp (-(δ / 8 * s))) (hRhi : (R : ℝ) * θ ≤ δ / (64 * k) * s + θ)
    (hkθ : k * θ ≤ 1 / 4)
    (hDi : ∀ i ≤ R, Real.exp ((1 - δ / 32) * s - 2) ≤ Real.exp s * (1 - (k - 1) * θ) ^ i)
    (P4 : Real.exp 1 * Real.exp (-(δ / 16 * s)) *
      (1 + (δ / (64 * k) * s + 1) * (4 * k ^ 2 * (Real.exp 2 + 1) + 2)) ≤ 1 / 4) :
    ∀ i ≤ R, errSeq k θ θ (Real.exp ((1 - δ) * s)) (Real.exp s) (Real.exp (-(δ * s))) i ≤ 1 / 4 := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < k := by linarith
  have hθ0 : 0 < θ := by rw [hθdef]; exact Real.exp_pos _
  set C := Real.exp ((1 - δ) * s) with hCdef
  have hC0 : 0 < C := Real.exp_pos _
  set Dmin := Real.exp ((1 - δ / 32) * s - 2) with hDmin
  have hDmin0 : 0 < Dmin := Real.exp_pos _
  set B := 4 * k ^ 2 * (Real.exp 2 + 1) + 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set β := B * θ with hβ
  have hCD : C / Dmin ≤ Real.exp 2 * θ := by
    rw [div_le_iff₀ hDmin0, hCdef, hDmin, hθdef, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  intro i hi
  have hb : ∀ j < i, 4 * k ^ 2 * θ * (C / (Real.exp s * (1 - (k - 1) * θ) ^ j) + θ) +
      2 * θ * θ ≤ θ * β := by
    intro j hj
    have hD := hDi j (by omega)
    have h1 : C / (Real.exp s * (1 - (k - 1) * θ) ^ j) ≤ C / Dmin :=
      div_le_div_of_nonneg_left hC0.le hDmin0 hD
    have h2 : C / (Real.exp s * (1 - (k - 1) * θ) ^ j) + θ ≤ (Real.exp 2 + 1) * θ := by
      linarith
    have h3 : 4 * k ^ 2 * θ * (C / (Real.exp s * (1 - (k - 1) * θ) ^ j) + θ) ≤
        4 * k ^ 2 * θ * ((Real.exp 2 + 1) * θ) := by gcongr
    have h4 : θ * β = 4 * k ^ 2 * θ * ((Real.exp 2 + 1) * θ) + 2 * θ * θ := by
      rw [hβ, hB]; ring
    linarith
  have hβ0 : 0 ≤ θ * β := by positivity
  refine (errSeq_le hkpos.le hθ0.le i hb hβ0).trans ?_
  have hiθ : (i : ℝ) * θ ≤ δ / (64 * k) * s + θ := by
    have : (i : ℝ) * θ ≤ R * θ := by gcongr
    linarith
  have hpow : (1 + 4 * k * θ) ^ i ≤ Real.exp 1 * Real.exp (δ / 16 * s) := by
    have h4 : 4 * k * (i * θ) ≤ 4 * k * (δ / (64 * k) * s + θ) :=
      mul_le_mul_of_nonneg_left hiθ (by linarith)
    have h5 : 4 * k * (δ / (64 * k) * s + θ) = δ / 16 * s + 4 * (k * θ) := by
      field_simp; ring
    calc (1 + 4 * k * θ) ^ i ≤ Real.exp (4 * k * θ) ^ i :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (4 * k * θ)]) i
      _ = Real.exp (4 * k * (i * θ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (1 + δ / 16 * s) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 * Real.exp (δ / 16 * s) := Real.exp_add _ _
  have he0 : Real.exp (-(δ * s)) ≤ θ := by rw [hθdef]; exact Real.exp_le_exp.2 (by nlinarith)
  have hiθ' : (i : ℝ) * θ ≤ δ / (64 * k) * s + 1 := by
    have : θ ≤ 1 := by rw [hθdef]; exact Real.exp_le_one_iff.2 (by nlinarith)
    linarith
  have hsum : Real.exp (-(δ * s)) + i * (θ * β) ≤ θ * (1 + (δ / (64 * k) * s + 1) * B) := by
    have h1 : (i : ℝ) * (θ * β) = θ * ((i * θ) * B) := by rw [hβ]; ring
    have h2 : θ * ((i * θ) * B) ≤ θ * ((δ / (64 * k) * s + 1) * B) := by gcongr
    have h3 : θ * (1 + (δ / (64 * k) * s + 1) * B) = θ + θ * ((δ / (64 * k) * s + 1) * B) := by
      ring
    linarith
  have hθe : Real.exp (δ / 16 * s) * θ = Real.exp (-(δ / 16 * s)) := by
    rw [hθdef, ← Real.exp_add]; congr 1; ring
  have hpos : 0 ≤ Real.exp (-(δ * s)) + i * (θ * β) := by positivity
  calc (1 + 4 * k * θ) ^ i * (Real.exp (-(δ * s)) + i * (θ * β))
      ≤ (Real.exp 1 * Real.exp (δ / 16 * s)) * (θ * (1 + (δ / (64 * k) * s + 1) * B)) := by
        gcongr
    _ = Real.exp 1 * (Real.exp (δ / 16 * s) * θ) * (1 + (δ / (64 * k) * s + 1) * B) := by ring
    _ ≤ 1 / 4 := by rw [hθe]; exact P4

theorem params_kC {k : ℕ} {δ s : ℝ}
    (P3 : 2 * k * Real.exp 2 ≤ Real.exp (31 * δ / 32 * s)) {D : ℝ}
    (hD : Real.exp ((1 - δ / 32) * s - 2) ≤ D) :
    k * Real.exp ((1 - δ) * s) ≤ D / 2 := by
  have h1 : 2 * k * Real.exp 2 * Real.exp ((1 - δ) * s) ≤
      Real.exp (31 * δ / 32 * s) * Real.exp ((1 - δ) * s) :=
    mul_le_mul_of_nonneg_right P3 (Real.exp_pos _).le
  have h2 : Real.exp (31 * δ / 32 * s) * Real.exp ((1 - δ) * s) =
      Real.exp ((1 - δ / 32) * s - 2) * Real.exp 2 := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h3 : 2 * k * Real.exp ((1 - δ) * s) ≤ Real.exp ((1 - δ / 32) * s - 2) := by
    have := Real.exp_pos 2
    have h4 : (2 * k * Real.exp ((1 - δ) * s)) * Real.exp 2 ≤
        Real.exp ((1 - δ / 32) * s - 2) * Real.exp 2 := by linarith
    exact le_of_mul_le_mul_right h4 this
  linarith

theorem params_prob {α : Type*} {k K L : ℕ} {δ s θ : ℝ} (V : Finset α) (𝒯 : Finset (Finset α))
    (hk2 : 2 ≤ k) (hL : (K + 1 : ℝ) ≤ δ / 8 * L) (hs : 0 ≤ s)
    (hθdef : θ = Real.exp (-(δ / 8 * s)))
    (P5 : 2 ^ L * Real.exp (-s) ≤ 1 / 8)
    (P6 : 2 * Real.exp (K * s) *
      Real.exp (-(Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2))) ≤ 1 / 8)
    (P7 : Real.exp (K * s) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k))) ≤ 1 / 8)
    (P8 : Real.exp (K * s) * Real.exp (-(160 * k * Real.exp (δ / 4 * s))) ≤ 1 / 8)
    (hV : (V.card : ℝ) ≤ Real.exp (K * s)) (h𝒯 : (𝒯.card : ℝ) ≤ Real.exp (K * s))
    {D : ℝ} (hD : Real.exp ((1 - δ / 32) * s - 2) ≤ D) :
    (V.card : ℝ) * (2 * θ) ^ L
      + 2 * V.card * Real.exp (-(θ * θ ^ 2 * D / (16 * k ^ 2 * Real.exp ((1 - δ) * s))))
      + 𝒯.card * (Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) +
        Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s)))) < 1 := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < k := by linarith
  have hA : (V.card : ℝ) * (2 * θ) ^ L ≤ 1 / 8 := by
    have h1 : (2 * θ) ^ L = 2 ^ L * Real.exp (-(δ / 8 * L * s)) := by
      rw [mul_pow, hθdef, ← Real.exp_nat_mul]; congr 2; ring
    rw [h1]
    have h2 : Real.exp (K * s + -(δ / 8 * L * s)) ≤ Real.exp (-s) := by
      apply Real.exp_le_exp.2; nlinarith
    calc (V.card : ℝ) * (2 ^ L * Real.exp (-(δ / 8 * L * s)))
        ≤ Real.exp (K * s) * (2 ^ L * Real.exp (-(δ / 8 * L * s))) := by gcongr
      _ = 2 ^ L * Real.exp (K * s + -(δ / 8 * L * s)) := by rw [Real.exp_add]; ring
      _ ≤ 2 ^ L * Real.exp (-s) := by gcongr
      _ ≤ 1 / 8 := P5
  have hB : 2 * (V.card : ℝ) *
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
    calc 2 * (V.card : ℝ) * Real.exp (-(θ * θ ^ 2 * D / (16 * k ^ 2 * Real.exp ((1 - δ) * s))))
        ≤ 2 * Real.exp (K * s) *
          Real.exp (-(Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2))) := by
          gcongr
      _ ≤ 1 / 8 := P6
  have hC1 : (𝒯.card : ℝ) * Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) ≤ 1 / 8 := by
    have : θ * Real.exp (δ / 2 * s) = Real.exp (3 * δ / 8 * s) := by
      rw [hθdef, ← Real.exp_add]; congr 1; ring
    rw [this]
    calc (𝒯.card : ℝ) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k)))
        ≤ Real.exp (K * s) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k))) := by gcongr
      _ ≤ 1 / 8 := P7
  have hC2 : (𝒯.card : ℝ) * Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s))) ≤ 1 / 8 := by
    have : 160 * k * θ ^ 2 * Real.exp (δ / 2 * s) = 160 * k * Real.exp (δ / 4 * s) := by
      rw [hθdef, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2; push_cast; ring
    rw [this]
    calc (𝒯.card : ℝ) * Real.exp (-(160 * k * Real.exp (δ / 4 * s)))
        ≤ Real.exp (K * s) * Real.exp (-(160 * k * Real.exp (δ / 4 * s))) := by gcongr
      _ ≤ 1 / 8 := P8
  have : (𝒯.card : ℝ) * (Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) +
      Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s)))) =
      (𝒯.card : ℝ) * Real.exp (-(θ * Real.exp (δ / 2 * s) / (512 * k))) +
      (𝒯.card : ℝ) * Real.exp (-(160 * k * θ ^ 2 * Real.exp (δ / 2 * s))) := by ring
  linarith

/-- **The nibble with explicit parameters.** -/
theorem nibble_of_params {α : Type*} [DecidableEq α] {k K L : ℕ} {δ s : ℝ}
    (hk2 : 2 ≤ k) (hδ : 0 < δ) (hL : (K + 1 : ℝ) ≤ δ / 8 * L) (hs : 0 ≤ s)
    (P1 : k * Real.exp (-(δ / 8 * s)) ≤ 1 / 4)
    (P2 : 2 ≤ (1 - δ / 32) * s)
    (P3 : 2 * k * Real.exp 2 ≤ Real.exp (31 * δ / 32 * s))
    (P4 : Real.exp 1 * Real.exp (-(δ / 16 * s)) *
      (1 + (δ / (64 * k) * s + 1) * (4 * k ^ 2 * (Real.exp 2 + 1) + 2)) ≤ 1 / 4)
    (P5 : 2 ^ L * Real.exp (-s) ≤ 1 / 8)
    (P6 : 2 * Real.exp (K * s) *
      Real.exp (-(Real.exp (19 * δ / 32 * s) / (16 * k ^ 2 * Real.exp 2))) ≤ 1 / 8)
    (P7 : Real.exp (K * s) * Real.exp (-(Real.exp (3 * δ / 8 * s) / (512 * k))) ≤ 1 / 8)
    (P8 : Real.exp (K * s) * Real.exp (-(160 * k * Real.exp (δ / 4 * s))) ≤ 1 / 8)
    (P9 : Real.exp (-(δ / (64 * k) / 2 * s)) + Real.exp (-(δ / 2 * s)) +
      320 * k ^ 2 * (1 + k * L) * (δ / (64 * k) * s + 1) * Real.exp (-(δ / 8 * s)) ≤
        Real.exp (-(δ / (64 * k) / 4 * s)))
    (E : Finset (Finset α)) (V : Finset α) (𝒯 : Finset (Finset α))
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, Real.exp s * (1 - Real.exp (-(δ * s))) ≤ (star E v).card ∧
      ((star E v).card : ℝ) ≤ Real.exp s)
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ Real.exp ((1 - δ) * s))
    (hV : (V.card : ℝ) ≤ Real.exp (K * s)) (h𝒯 : (𝒯.card : ℝ) ≤ Real.exp (K * s)) :
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
  obtain ⟨M, hME, hMdisj, hMT⟩ := nibble_iterate (D0 := Real.exp s) (e0 := Real.exp (-(δ * s)))
    (C := Real.exp ((1 - δ) * s)) (θ := θ) (η := θ) (τ := Real.exp (δ / 2 * s))
    (ζ := 160 * k * θ ^ 2) (R := R) (L := L) 𝒯 hk2 hk hEV
    (fun v hv => ⟨(hdeg v hv).1, (hdeg v hv).2.trans (by
      have := Real.exp_pos (-(δ * s)); nlinarith [Real.exp_pos s])⟩) hcod (Real.exp_pos s)
    (Real.exp_pos _) (Real.exp_pos _).le hθ0 P1 hθ0 hθ1 (Real.exp_pos _) le_rfl
    (fun i hi => ⟨hDmin1.trans (hDi i hi.le), params_kC P3 (hDi i hi.le), herr i hi.le,
      params_prob V 𝒯 hk2 hL hs hθdef P5 P6 P7 P8 hV h𝒯 (hDi i hi.le)⟩)
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

end RefinedAbsorption.Nibble
