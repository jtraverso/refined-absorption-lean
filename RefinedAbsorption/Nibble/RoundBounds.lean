module
public import RefinedAbsorption.Nibble.Waste
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical estimates for one nibble round

Elementary real inequalities and the resulting bounds on the expectations of the new degrees
and of the number of uncovered vertices of a test set.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

theorem one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ Real.exp (-(p * n)) := by
  have h : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc (1 - p) ^ n ≤ Real.exp (-p) ^ n := pow_le_pow_left₀ (by linarith) h n
    _ = Real.exp (-(p * n)) := by rw [← Real.exp_nat_mul]; ring_nf

theorem one_sub_mul_le_pow {p : ℝ} (hp1 : p ≤ 2) (n : ℕ) : 1 - p * n ≤ (1 - p) ^ n := by
  have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -p by linarith) n
  rw [show (1 : ℝ) + -p = 1 - p by ring] at this
  linarith

theorem exp_neg_le_quad {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 := by
  have h : |-x| ≤ 1 := by rw [abs_neg, abs_of_nonneg hx0]; exact hx1
  have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le h)).2
  nlinarith

/-- `binom(N, s) p^{2s} ≤ e^{-s}` when `40 N p² ≤ s`. -/
theorem choose_mul_pow_le_exp {N s : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (h : 40 * (N * p ^ 2) ≤ s) : (N.choose s : ℝ) * p ^ (2 * s) ≤ Real.exp (-(s : ℝ)) := by
  have h1 : (N.choose s : ℝ) ≤ (N : ℝ) ^ s / s.factorial := Nat.choose_le_pow_div s N
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have h2 : (s : ℝ) ^ s / s.factorial ≤ Real.exp s := Real.pow_div_factorial_le_exp _ (by positivity) s
  have hy : (N : ℝ) * p ^ 2 ≤ s / 40 := by linarith
  have hy0 : (0 : ℝ) ≤ N * p ^ 2 := by positivity
  have he : Real.exp 1 ^ 2 ≤ 40 := by
    have := Real.exp_one_lt_d9; nlinarith [Real.exp_pos 1]
  calc (N.choose s : ℝ) * p ^ (2 * s) ≤ (N : ℝ) ^ s / s.factorial * p ^ (2 * s) := by gcongr
    _ = (N * p ^ 2) ^ s / s.factorial := by rw [mul_pow, ← pow_mul, mul_comm 2 s]; ring
    _ ≤ (s / 40) ^ s / s.factorial := by gcongr
    _ = (1 / 40) ^ s * ((s : ℝ) ^ s / s.factorial) := by rw [div_pow, one_div, inv_pow]; ring
    _ ≤ (1 / 40) ^ s * Real.exp s := by gcongr
    _ = (Real.exp 1 / 40) ^ s := by
        rw [div_pow, div_pow, ← Real.exp_nat_mul, mul_one]; ring
    _ ≤ (Real.exp (-1)) ^ s := by
        gcongr
        rw [Real.exp_neg, div_le_iff₀ (by norm_num), inv_mul_eq_div, le_div_iff₀
          (Real.exp_pos 1)]
        nlinarith [Real.exp_pos 1]
    _ = Real.exp (-(s : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- Algebra for the upper degree bound. -/
theorem deg_upper_alg {k θ e r η y : ℝ} (hk : 2 ≤ k) (hθ : 0 ≤ θ) (hkθ : k * θ ≤ 1 / 4)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (hy : y = (k - 1) * θ * (1 - e) - (k - 1) * ((k - 1) * θ) * r) (hy0 : 0 ≤ y) :
    (1 + e) * (1 - y + y ^ 2) + θ * η ≤
      (1 - (k - 1) * θ) * (1 + (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (r + θ) + 2 * θ * η)) := by
  set x := (k - 1) * θ with hx
  have hx0 : 0 ≤ x := by rw [hx]; nlinarith
  have hxk : x ≤ k * θ := by rw [hx]; nlinarith
  have hyx : y ≤ x := by rw [hy]; nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k - 1) hx0) hr]
  have hy2 : y ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hy0 hyx 2
  have hx2 : x ^ 2 ≤ k ^ 2 * θ ^ 2 := by
    have := pow_le_pow_left₀ hx0 hxk 2; nlinarith
  have hxr : (k - 1) * x * r ≤ k ^ 2 * θ * r := by
    rw [hx]; have : (k - 1) * ((k - 1) * θ) ≤ k ^ 2 * θ := by nlinarith
    nlinarith
  have hxe : x * e ≤ k * θ * e := by nlinarith
  have hA : 1 - y + y ^ 2 ≤ 1 - x + x * e + (k - 1) * x * r + x ^ 2 := by
    rw [hy]; nlinarith
  have hA0 : 0 ≤ x * e + (k - 1) * x * r + x ^ 2 := by
    have : 0 ≤ (k - 1) * x * r := by
      have : 0 ≤ k - 1 := by linarith
      positivity
    positivity
  have hx12 : x ≤ 1 / 4 := le_trans hxk hkθ
  have hB : 0 ≤ 1 - y + y ^ 2 := by nlinarith
  calc (1 + e) * (1 - y + y ^ 2) + θ * η
      ≤ (1 + e) * (1 - x + x * e + (k - 1) * x * r + x ^ 2) + θ * η := by gcongr
    _ ≤ (1 + e) * (1 - x) + 2 * (x * e + (k - 1) * x * r + x ^ 2) + θ * η := by nlinarith
    _ ≤ (1 + e) * (1 - x) + 2 * (k * θ * e + k ^ 2 * θ * r + k ^ 2 * θ ^ 2) + θ * η := by
        linarith
    _ ≤ (1 - x) * (1 + (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (r + θ) + 2 * θ * η)) := by
        have h1 : 0 ≤ 4 * k * θ * e + 4 * k ^ 2 * θ * (r + θ) + 2 * θ * η := by positivity
        nlinarith

/-- Algebra for the lower degree bound. -/
theorem deg_lower_alg {k θ e r η : ℝ} (hk : 2 ≤ k) (hθ : 0 ≤ θ) (hkθ : k * θ ≤ 1 / 4)
    (he0 : 0 ≤ e) (hr : 0 ≤ r) (hη : 0 ≤ η) :
    (1 - (k - 1) * θ) * (1 - (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (r + θ) + 2 * θ * η)) ≤
      (1 - e) * (1 - (k - 1) * θ * (1 + e)) - θ * η := by
  set x := (k - 1) * θ with hx
  have hx0 : 0 ≤ x := by rw [hx]; nlinarith
  have hxk : x ≤ k * θ := by rw [hx]; nlinarith
  have hx12 : x ≤ 1 / 4 := le_trans hxk hkθ
  have h1 : 0 ≤ 4 * k ^ 2 * θ * (r + θ) := by positivity
  have h2 : x * e ≤ k * θ * e := by nlinarith
  have h3 : 0 ≤ (1 - x) * (4 * k ^ 2 * θ * (r + θ)) := by
    have : 0 ≤ 1 - x := by linarith
    positivity
  nlinarith [mul_nonneg hθ hη, mul_nonneg hx0 he0, mul_nonneg (mul_nonneg hx0 he0) he0,
    mul_nonneg (mul_nonneg hθ he0) hx0, mul_nonneg (mul_nonneg hθ hη) hx0]

/-! ### Neighbourhood sizes -/

theorem card_nbhd_erase_le {E : Finset (Finset α)} {V : Finset α} {k : ℕ} {Dmax : ℝ}
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ u ∈ V, ((star E u).card : ℝ) ≤ Dmax) {v : α} {e : Finset α} (he : e ∈ star E v) :
    ((nbhd E (e.erase v)).card : ℝ) ≤ (k - 1) * Dmax := by
  obtain ⟨heE, hve⟩ := mem_star.1 he
  have hsub : e.erase v ⊆ V := (erase_subset v e).trans (hEV e heE)
  refine (card_nbhd_le hsub hdeg).trans (le_of_eq ?_)
  rw [card_erase_of_mem hve, hk e heE]
  have : 1 ≤ k := by
    have := hk e heE; have : 0 < e.card := card_pos.2 ⟨v, hve⟩; omega
  push_cast [Nat.cast_sub this]; ring

theorem card_nbhd_erase_ge {E : Finset (Finset α)} {V : Finset α} {k : ℕ} {Dmin C : ℝ}
    (hC : 0 ≤ C) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ u ∈ V, Dmin ≤ ((star E u).card : ℝ))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C) {v : α} {e : Finset α}
    (he : e ∈ star E v) :
    (k - 1) * Dmin - (k - 1) * ((k - 1) * C) ≤ ((nbhd E (e.erase v)).card : ℝ) := by
  obtain ⟨heE, hve⟩ := mem_star.1 he
  have hsub : e.erase v ⊆ V := (erase_subset v e).trans (hEV e heE)
  have hcard : ((e.erase v).card : ℝ) = k - 1 := by
    rw [card_erase_of_mem hve, hk e heE]
    have : 1 ≤ k := by
      have := hk e heE; have : 0 < e.card := card_pos.2 ⟨v, hve⟩; omega
    push_cast [Nat.cast_sub this]; ring
  have hB := card_biUnion_ge (e.erase v) (star E)
  have hB' : (∑ i ∈ e.erase v, ((star E i).card : ℝ)) -
      ∑ i ∈ e.erase v, ∑ j ∈ (e.erase v).erase i, ((star E i ∩ star E j).card : ℝ) ≤
      ((nbhd E (e.erase v)).card : ℝ) := by
    unfold nbhd; exact_mod_cast hB
  have h1 : (k - 1) * Dmin ≤ ∑ i ∈ e.erase v, ((star E i).card : ℝ) := by
    rw [← hcard, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun u hu => hdeg u (hsub hu)
  have h2 : ∑ i ∈ e.erase v, ∑ j ∈ (e.erase v).erase i, ((star E i ∩ star E j).card : ℝ) ≤
      (k - 1) * ((k - 1) * C) := by
    have hC0 : ∀ i ∈ e.erase v, ∑ j ∈ (e.erase v).erase i, ((star E i ∩ star E j).card : ℝ) ≤
        (k - 1) * C := by
      intro i hi
      have : ∀ j ∈ (e.erase v).erase i, ((star E i ∩ star E j).card : ℝ) ≤ C := by
        intro j hj
        have hij : i ≠ j := fun h => (ne_of_mem_erase hj) h.symm
        have : star E i ∩ star E j = E.filter (fun e => i ∈ e ∧ j ∈ e) := by
          ext g; simp [star, mem_filter]; tauto
        rw [this]
        exact hcod i j hij
      refine (sum_le_sum this).trans ?_
      rw [sum_const, nsmul_eq_mul, card_erase_of_mem hi]
      have : 1 ≤ (e.erase v).card := card_pos.2 ⟨i, hi⟩
      push_cast [Nat.cast_sub this]; rw [hcard]; nlinarith
    refine (sum_le_sum hC0).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul, hcard]
  linarith

/-! ### Expectations -/

theorem Ex_fdeg_le {E : Finset (Finset α)} {V : Finset α} {k : ℕ} {D e C θ : ℝ}
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C) (hC : 0 ≤ C) (hD : 0 < D) (hθ0 : 0 ≤ θ)
    (hθD : θ ≤ D) {y : ℝ} (hy : y = (k - 1) * θ * (1 - e) - (k - 1) * ((k - 1) * θ) * (C / D))
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {v : α} (hv : v ∈ V) :
    Ex (θ / D) E (fdeg E v) ≤ D * (1 + e) * (1 - y + y ^ 2) := by
  rw [Ex_fdeg]
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0 hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  have hterm : ∀ g ∈ star E v, (1 - θ / D) ^ (nbhd E (g.erase v)).card ≤ 1 - y + y ^ 2 := by
    intro g hg
    refine (one_sub_pow_le_exp hp1 _).trans ((Real.exp_le_exp.2 ?_).trans
      (exp_neg_le_quad hy0 hy1))
    have := card_nbhd_erase_ge hC hk hEV (fun u hu => (hdeg u hu).1) hcod hg
    rw [neg_le_neg_iff, hy]
    have h2 : θ / D * ((k - 1) * (D * (1 - e)) - (k - 1) * ((k - 1) * C)) ≤
        θ / D * ((nbhd E (g.erase v)).card : ℝ) := mul_le_mul_of_nonneg_left this hp0
    have h3 : θ / D * ((k - 1) * (D * (1 - e)) - (k - 1) * ((k - 1) * C)) =
        (k - 1) * θ * (1 - e) - (k - 1) * ((k - 1) * θ) * (C / D) := by
      field_simp
    linarith
  have hB : 0 ≤ 1 - y + y ^ 2 := by nlinarith
  calc ∑ g ∈ star E v, (1 - θ / D) ^ (nbhd E (g.erase v)).card
      ≤ ∑ g ∈ star E v, (1 - y + y ^ 2) := sum_le_sum hterm
    _ = (star E v).card * (1 - y + y ^ 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ D * (1 + e) * (1 - y + y ^ 2) := by gcongr; exact (hdeg v hv).2

theorem Ex_fdeg_ge {E : Finset (Finset α)} {V : Finset α} {k : ℕ} {D e θ : ℝ}
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hD : 0 < D) (hθ0 : 0 ≤ θ) (hθD : θ ≤ D)
    (hsmall : (k - 1) * θ * (1 + e) ≤ 1) {v : α} (hv : v ∈ V) :
    D * (1 - e) * (1 - (k - 1) * θ * (1 + e)) ≤ Ex (θ / D) E (fdeg E v) := by
  rw [Ex_fdeg]
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0 hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  have hterm : ∀ g ∈ star E v, 1 - (k - 1) * θ * (1 + e) ≤
      (1 - θ / D) ^ (nbhd E (g.erase v)).card := by
    intro g hg
    refine le_trans ?_ (one_sub_mul_le_pow (by linarith) _)
    have := card_nbhd_erase_le hk hEV (fun u hu => (hdeg u hu).2) hg
    have h2 : θ / D * ((nbhd E (g.erase v)).card : ℝ) ≤ θ / D * ((k - 1) * (D * (1 + e))) :=
      mul_le_mul_of_nonneg_left this hp0
    have h3 : θ / D * ((k - 1) * (D * (1 + e))) = (k - 1) * θ * (1 + e) := by field_simp
    linarith
  have hB : 0 ≤ 1 - (k - 1) * θ * (1 + e) := by linarith
  calc D * (1 - e) * (1 - (k - 1) * θ * (1 + e))
      ≤ (star E v).card * (1 - (k - 1) * θ * (1 + e)) := by gcongr; exact (hdeg v hv).1
    _ = ∑ g ∈ star E v, (1 - (k - 1) * θ * (1 + e)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum hterm

theorem Ex_fcov_le {E : Finset (Finset α)} {V X : Finset α} {D e θ : ℝ} (hXV : X ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hD : 0 < D) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθD : θ ≤ D) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Ex (θ / D) E (fcov X) ≤ X.card * (1 - θ * (1 - e) + θ ^ 2) := by
  rw [Ex_fcov]
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0 hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  have hx0 : 0 ≤ θ * (1 - e) := mul_nonneg hθ0 (by linarith)
  have hx1 : θ * (1 - e) ≤ 1 := by nlinarith
  have hterm : ∀ u ∈ X, (1 - θ / D) ^ (star E u).card ≤ 1 - θ * (1 - e) + θ ^ 2 := by
    intro u hu
    refine (one_sub_pow_le_exp hp1 _).trans ((Real.exp_le_exp.2 ?_).trans
      ((exp_neg_le_quad hx0 hx1).trans ?_))
    · have := (hdeg u (hXV hu)).1
      have h2 : θ / D * (D * (1 - e)) ≤ θ / D * ((star E u).card : ℝ) :=
        mul_le_mul_of_nonneg_left this hp0
      have h3 : θ / D * (D * (1 - e)) = θ * (1 - e) := by field_simp
      linarith
    · have h1e : (1 - e) ^ 2 ≤ 1 := by nlinarith
      have : (θ * (1 - e)) ^ 2 ≤ θ ^ 2 := by
        rw [mul_pow]; nlinarith [sq_nonneg θ]
      linarith
  calc ∑ u ∈ X, (1 - θ / D) ^ (star E u).card ≤ ∑ u ∈ X, (1 - θ * (1 - e) + θ ^ 2) :=
        sum_le_sum hterm
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- The degree of a surviving vertex in the next hypergraph is `fdeg`. -/
theorem card_star_nextE {E S : Finset (Finset α)} {v : α} (hv : v ∉ cov S) :
    ((star (nextE E S) v).card : ℝ) = fdeg E v S := by
  unfold fdeg
  congr 2
  ext g
  simp only [star, nextE, mem_filter]
  constructor
  · rintro ⟨⟨hg, hd⟩, hvg⟩
    exact ⟨⟨hg, hvg⟩, disjoint_of_subset_left (erase_subset v g) hd⟩
  · rintro ⟨⟨hg, hvg⟩, hd⟩
    refine ⟨⟨hg, ?_⟩, hvg⟩
    rw [disjoint_left]
    intro u hu hcov
    by_cases huv : u = v
    · exact hv (huv ▸ hcov)
    · exact disjoint_left.1 hd (mem_erase.2 ⟨huv, hu⟩) hcov

end RefinedAbsorption.Nibble
