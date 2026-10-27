module
public import RefinedAbsorption.Sharp.Descent

/-!
# Arithmetic of the Edge Sparsification Lemma

Numerical facts about `w = winCost r m = ⌈m^{1-1/r}⌉` used in the proof of Lemma 3.12
(Delcourt–Postle, arXiv:2402.17855): `m^{r-1} ≤ w^r ≤ 2^r m^{r-1}`, `m^ℓ ≤ w^{ℓ+1}` for
`ℓ ≤ r - 1`, the lower bound `m^ℓ ≤ 8^ℓ ℓ! binom(⌊m/2⌋, ℓ)`, and the two exponential estimates
behind the union bound of the random partition.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.Window

lemma rpow_exponent_pow {r m : ℕ} (hr : 1 ≤ r) :
    ((m : ℝ) ^ (1 - 1 / (r : ℝ))) ^ r = (m : ℝ) ^ (r - 1) := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast]
  congr 1
  rw [Nat.cast_sub hr]
  field_simp
  push_cast
  ring

theorem pow_le_winCost_pow {r : ℕ} (hr : 1 ≤ r) (m : ℕ) : m ^ (r - 1) ≤ winCost r m ^ r := by
  have h1 : (m : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ winCost r m := Nat.le_ceil _
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg m) _) h1 r
  rw [rpow_exponent_pow hr] at h2
  exact_mod_cast h2

theorem winCost_pow_le {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    winCost r m ^ r ≤ 2 ^ r * m ^ (r - 1) := by
  have h1 := winCost_le hr hm
  have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 r
  rw [mul_pow, rpow_exponent_pow hr] at h2
  exact_mod_cast h2

/-- `m^ℓ ≤ w^{ℓ+1}` for `ℓ ≤ r - 1`. -/
theorem pow_le_winCost_pow_succ {r ℓ : ℕ} (hr : 1 ≤ r) (hℓ : ℓ ≤ r - 1) {m : ℕ} (hm : 1 ≤ m) :
    m ^ ℓ ≤ winCost r m ^ (ℓ + 1) := by
  set w := winCost r m
  have hw : 1 ≤ w := one_le_winCost r hm
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
  · simpa using hw
  have hr1 : 1 ≤ r - 1 := by omega
  have h1 : (m ^ ℓ) ^ (r - 1) ≤ (w ^ (ℓ + 1)) ^ (r - 1) := by
    calc (m ^ ℓ) ^ (r - 1) = (m ^ (r - 1)) ^ ℓ := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (w ^ r) ^ ℓ := Nat.pow_le_pow_left (pow_le_winCost_pow hr m) _
      _ = w ^ (r * ℓ) := by rw [← pow_mul]
      _ ≤ w ^ ((ℓ + 1) * (r - 1)) := Nat.pow_le_pow_right hw (by
          have : r * ℓ ≤ (ℓ + 1) * (r - 1) := by
            obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
            have : ℓ ≤ s := by omega
            simp only [Nat.add_sub_cancel]
            nlinarith
          exact this)
      _ = (w ^ (ℓ + 1)) ^ (r - 1) := by rw [← pow_mul]
  exact (Nat.pow_le_pow_iff_left (by omega)).1 h1

theorem winCost_le_self {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) : winCost r m ≤ m := by
  unfold winCost
  refine Nat.ceil_le.2 ?_
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc (m : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ (m : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by
          have : 0 ≤ 1 / (r : ℝ) := by positivity
          linarith)
    _ = m := Real.rpow_one _

/-- `m ≤ w^2` for `r ≥ 2`. -/
theorem le_winCost_sq {r : ℕ} (hr : 2 ≤ r) {m : ℕ} (hm : 1 ≤ m) : m ≤ winCost r m ^ 2 := by
  have := pow_le_winCost_pow_succ (r := r) (ℓ := 1) (by omega) (by omega) hm
  simpa using this

/-- Lower bound for binomial coefficients of `⌊m/2⌋`. -/
theorem pow_le_choose_half {m ℓ : ℕ} (h : 8 * ℓ ≤ m) :
    m ^ ℓ ≤ 8 ^ ℓ * ℓ.factorial * (m / 2).choose ℓ := by
  have h1 : m / 4 ≤ m / 2 + 1 - ℓ := by omega
  have h2 : (m / 2 + 1 - ℓ) ^ ℓ ≤ (m / 2).descFactorial ℓ := Nat.pow_sub_le_descFactorial _ _
  have h3 : (m / 2).descFactorial ℓ = ℓ.factorial * (m / 2).choose ℓ :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  have hm : m ≤ 8 * (m / 4) := by omega
  calc m ^ ℓ ≤ (8 * (m / 4)) ^ ℓ := Nat.pow_le_pow_left hm _
    _ = 8 ^ ℓ * (m / 4) ^ ℓ := mul_pow _ _ _
    _ ≤ 8 ^ ℓ * (ℓ.factorial * (m / 2).choose ℓ) :=
        Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left h1 _).trans (h2.trans h3.le))
    _ = 8 ^ ℓ * ℓ.factorial * (m / 2).choose ℓ := by ring

/-- `m < e^{⌊log₂ m⌋ + 1}`. -/
theorem lt_exp_log2 (m : ℕ) : (m : ℝ) < Real.exp ((Nat.log 2 m + 1 : ℕ) : ℝ) := by
  have h1 : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  calc (m : ℝ) < (2 : ℝ) ^ (Nat.log 2 m + 1) := by exact_mod_cast h1
    _ ≤ (Real.exp 1) ^ (Nat.log 2 m + 1) := pow_le_pow_left₀ (by norm_num) h2 _
    _ = Real.exp ((Nat.log 2 m + 1 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul, mul_one]

/-- The size term of the union bound: `w · e^{-m/(4w)} ≤ 1/4` for `m` large. -/
theorem winCost_exp_le {r : ℕ} (hr : 1 ≤ r) {m : ℕ}
    (hm : 4 * 64 ^ r * (2 * r).factorial ≤ m) :
    (winCost r m : ℝ) * Real.exp (-((m : ℝ) / (4 * winCost r m))) ≤ 1 / 4 := by
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_iff_ne_zero.2 (by positivity)) hm
  set w := winCost r m with hw
  have hw1 : 1 ≤ w := one_le_winCost r hm1
  have hwm : w ≤ m := winCost_le_self hr hm1
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  set y : ℝ := (m : ℝ) / (4 * w) with hy
  have hy0 : 0 ≤ y := by positivity
  -- `y^r ≥ m / 8^r`
  have hwr : (w : ℝ) ^ r ≤ 2 ^ r * (m : ℝ) ^ (r - 1) := by exact_mod_cast winCost_pow_le hr hm1
  have hyr : (m : ℝ) / 8 ^ r ≤ y ^ r := by
    rw [hy, div_pow, mul_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (m : ℝ) ^ r = m * m ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    have : (8 : ℝ) ^ r = 4 ^ r * 2 ^ r := by rw [← mul_pow]; norm_num
    rw [this]
    have := mul_le_mul_of_nonneg_left hwr (show (0 : ℝ) ≤ m * 4 ^ r by positivity)
    nlinarith
  have hy2r : (m : ℝ) ^ 2 / 64 ^ r ≤ y ^ (2 * r) := by
    have := pow_le_pow_left₀ (by positivity) hyr 2
    rw [← pow_mul, mul_comm r 2, div_pow, ← pow_mul, mul_comm r 2, pow_mul] at this
    rw [pow_mul] at this ⊢
    calc (m : ℝ) ^ 2 / 64 ^ r = (m : ℝ) ^ 2 / (8 ^ 2) ^ r := by norm_num
      _ ≤ _ := this
  have hexp : (m : ℝ) ^ 2 / (64 ^ r * (2 * r).factorial) ≤ Real.exp y := by
    refine le_trans ?_ (Real.pow_div_factorial_le_exp y hy0 (2 * r))
    rw [← div_div]
    exact div_le_div_of_nonneg_right hy2r (by positivity)
  have hbig : 4 * (w : ℝ) ≤ (m : ℝ) ^ 2 / (64 ^ r * (2 * r).factorial) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (4 * 64 ^ r * (2 * r).factorial : ℝ) ≤ m := by exact_mod_cast hm
    have h2 : (w : ℝ) ≤ m := by exact_mod_cast hwm
    nlinarith
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **The union bound of the random partition** with `k = w = winCost r m` parts and
`D* = D + 4 M₀ (r+1) w (⌊log₂ m⌋ + 1)`. -/
theorem partition_union_bound {r m M₀ D : ℕ} (hr : 1 ≤ r) (hM₀ : 1 ≤ M₀)
    (hm : 4 * 64 ^ r * (2 * r).factorial ≤ m) :
    (winCost r m : ℝ) * (Real.exp (-((m : ℝ) / (4 * winCost r m))) +
      (m : ℝ) ^ (r - 1) * Real.exp (-(((D + 4 * M₀ * (r + 1) * winCost r m *
        (Nat.log 2 m + 1) : ℕ) : ℝ) / (4 * M₀ * winCost r m)))) < 1 := by
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_iff_ne_zero.2 (by positivity)) hm
  have hm4 : 4 ≤ m := le_trans (by
    calc 4 ≤ 4 * (64 ^ r * (2 * r).factorial) := Nat.le_mul_of_pos_right _ (by positivity)
      _ = 4 * 64 ^ r * (2 * r).factorial := by ring) hm
  set w := winCost r m with hw
  set L := Nat.log 2 m + 1 with hL
  have hw1 : 1 ≤ w := one_le_winCost r hm1
  have hwm : w ≤ m := winCost_le_self hr hm1
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hM0 : (0 : ℝ) < M₀ := by exact_mod_cast hM₀
  have h1 := winCost_exp_le hr hm
  rw [← hw] at h1
  -- the degree term
  have hD : ((r + 1 : ℕ) : ℝ) * L ≤
      ((D + 4 * M₀ * (r + 1) * w * L : ℕ) : ℝ) / (4 * M₀ * w) := by
    rw [le_div_iff₀ (by positivity)]
    have : (((D + 4 * M₀ * (r + 1) * w * L : ℕ) : ℝ)) =
        (D : ℝ) + ((r + 1 : ℕ) : ℝ) * L * (4 * M₀ * w) := by
      push_cast; ring
    rw [this]; linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  have hexpL : (m : ℝ) ^ (r + 1) ≤ Real.exp (((r + 1 : ℕ) : ℝ) * L) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hm0.le (lt_exp_log2 m).le _
  have h2 : (w : ℝ) * ((m : ℝ) ^ (r - 1) * Real.exp (-(((D + 4 * M₀ * (r + 1) * w * L : ℕ) : ℝ) /
      (4 * M₀ * w)))) ≤ 1 / 4 := by
    have e1 : Real.exp (-(((D + 4 * M₀ * (r + 1) * w * L : ℕ) : ℝ) / (4 * M₀ * w))) ≤
        1 / (m : ℝ) ^ (r + 1) := by
      rw [Real.exp_neg, ← one_div]
      refine one_div_le_one_div_of_le (by positivity) (hexpL.trans (Real.exp_le_exp.2 hD))
    have e2 : (w : ℝ) * (m : ℝ) ^ (r - 1) ≤ (m : ℝ) ^ (r + 1) / 4 := by
      have : (m : ℝ) ^ (r + 1) = m * m ^ (r - 1) * m := by
        rw [show r + 1 = 1 + (r - 1) + 1 by omega, pow_succ, pow_add, pow_one]
      rw [this]
      have hm4' : (4 : ℝ) ≤ m := by exact_mod_cast hm4
      have hwm' : (w : ℝ) ≤ m := by exact_mod_cast hwm
      have hp : (0 : ℝ) ≤ (m : ℝ) ^ (r - 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hwm' hp,
        mul_le_mul_of_nonneg_left hm4' (mul_nonneg hm0.le hp)]
    calc (w : ℝ) * ((m : ℝ) ^ (r - 1) * Real.exp _) = (w * (m : ℝ) ^ (r - 1)) * Real.exp _ := by
          ring
      _ ≤ ((m : ℝ) ^ (r + 1) / 4) * (1 / (m : ℝ) ^ (r + 1)) :=
          mul_le_mul e2 e1 (Real.exp_pos _).le (by positivity)
      _ = 1 / 4 := by field_simp
  rw [mul_add]
  linarith

/-! ### The spread terms -/

/-- One term of the bound on the cliques through an `(r-1)`-set. -/
theorem spread_term_le {B m k ℓ P Q Dst K r : ℕ} (hk : 1 ≤ k)
    (hB : B * m ^ ℓ ≤ K * k ^ (ℓ + 1)) (hP : P * k ≤ 2 * m) (hQ : Q * k ≤ 2 * Dst) :
    B * ((r * P) ^ ℓ * (r * Q)) ≤ (2 * r) ^ (ℓ + 1) * K * Dst := by
  have hkpos : 0 < k ^ (ℓ + 1) := Nat.pow_pos hk
  refine Nat.le_of_mul_le_mul_right ?_ hkpos
  calc B * ((r * P) ^ ℓ * (r * Q)) * k ^ (ℓ + 1) = B * ((r * (P * k)) ^ ℓ * (r * (Q * k))) := by
        ring
    _ ≤ B * ((r * (2 * m)) ^ ℓ * (r * (2 * Dst))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hP) _)
          (Nat.mul_le_mul_left _ hQ))
    _ = (2 * r) ^ (ℓ + 1) * Dst * (B * m ^ ℓ) := by ring
    _ ≤ (2 * r) ^ (ℓ + 1) * Dst * (K * k ^ (ℓ + 1)) := Nat.mul_le_mul_left _ hB
    _ = (2 * r) ^ (ℓ + 1) * K * Dst * k ^ (ℓ + 1) := by ring

/-- One term of the bound on the link of an `(r-1)`-set. -/
theorem link_term_le {B m k ℓ P K r : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hℓ : 1 ≤ ℓ)
    (hB : B * m ^ ℓ ≤ K * k ^ (ℓ + 1)) (hP : P * k ≤ 2 * m) :
    B * (r * P) ≤ 2 * r * K * k := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  have hm : 1 ≤ m := hk.trans hkm
  have hpos : 0 < k * m ^ j := Nat.mul_pos hk (Nat.pow_pos hm)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc B * (r * P) * (k * m ^ j) = r * B * (P * k) * m ^ j := by ring
    _ ≤ r * B * (2 * m) * m ^ j := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP)
    _ = 2 * r * (B * m ^ (j + 1)) := by ring
    _ ≤ 2 * r * (K * k ^ (j + 1 + 1)) := Nat.mul_le_mul_left _ hB
    _ = 2 * r * K * k * (k * k ^ j) := by ring
    _ ≤ 2 * r * K * k * (k * m ^ j) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkm _))

theorem spread_le {B m k ℓ K : ℕ} (hkm : k ≤ m) (hm : 1 ≤ m)
    (hB : B * m ^ ℓ ≤ K * k ^ (ℓ + 1)) : B ≤ K * k := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.pow_pos (n := ℓ) hm)
  calc B * m ^ ℓ ≤ K * k ^ (ℓ + 1) := hB
    _ = K * k * k ^ ℓ := by ring
    _ ≤ K * k * m ^ ℓ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkm _)

/-- The spread bounds `B ℓ` of the special sets satisfy `B ℓ · m^ℓ ≤ K₀ · w^{ℓ+1}`. -/
theorem spreadBound_le {r s m w ℓ : ℕ} (hr : 1 ≤ r) (hℓ : ℓ ≤ r - 1)
    (hm8 : 8 * r ≤ m) (hmw : m ^ ℓ ≤ w ^ (ℓ + 1)) :
    (r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) / (m / 2).choose ℓ + 1) * m ^ ℓ ≤
      (r * 2 ^ r * (2 ^ s) ^ 2 * 8 ^ r * r.factorial + 1) * w ^ (ℓ + 1) := by
  set c := (m / 2).choose ℓ with hc
  set Xn := r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) with hXn
  have hch : m ^ ℓ ≤ 8 ^ ℓ * ℓ.factorial * c := pow_le_choose_half (by omega)
  have hA : Xn / c * m ^ ℓ ≤ Xn * (8 ^ ℓ * ℓ.factorial) := by
    calc Xn / c * m ^ ℓ ≤ Xn / c * (8 ^ ℓ * ℓ.factorial * c) := Nat.mul_le_mul_left _ hch
      _ = Xn / c * c * (8 ^ ℓ * ℓ.factorial) := by ring
      _ ≤ Xn * (8 ^ ℓ * ℓ.factorial) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
  have hXle : Xn * (8 ^ ℓ * ℓ.factorial) ≤
      (r * 2 ^ r * (2 ^ s) ^ 2 * 8 ^ r * r.factorial) * w ^ (ℓ + 1) := by
    have e1 : s.choose ℓ ≤ 2 ^ s := Nat.choose_le_two_pow s ℓ
    have e2 : 8 ^ ℓ ≤ 8 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e3 : ℓ.factorial ≤ r.factorial := Nat.factorial_le (by omega)
    calc Xn * (8 ^ ℓ * ℓ.factorial) = r * 2 ^ r * s.choose ℓ ^ 2 * 8 ^ ℓ * ℓ.factorial *
          w ^ (ℓ + 1) := by rw [hXn]; ring
      _ ≤ r * 2 ^ r * (2 ^ s) ^ 2 * 8 ^ r * r.factorial * w ^ (ℓ + 1) := by
          gcongr
  calc (Xn / c + 1) * m ^ ℓ = Xn / c * m ^ ℓ + m ^ ℓ := by ring
    _ ≤ (r * 2 ^ r * (2 ^ s) ^ 2 * 8 ^ r * r.factorial) * w ^ (ℓ + 1) + w ^ (ℓ + 1) :=
        Nat.add_le_add (hA.trans hXle) hmw
    _ = _ := by ring
