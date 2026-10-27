module
public import RequestProject.Nibble.RoundBounds

/-!
# One round of the nibble

`nibble_round`: in a `k`-uniform hypergraph whose vertex degrees are `D(1 ± e)` and whose
codegrees are at most `C`, there is a set `S` of edges (chosen at random with probability
`θ / D` each) such that

* every vertex not covered by `S` has degree `D(1 - (k-1)θ)(1 ± e')` in the hypergraph of edges
  avoiding the covered vertices;
* every large test set loses at least a `θ/2` fraction of its vertices;
* only few vertices of each large test set are wasted (covered by a chosen edge that meets
  another chosen edge).
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

theorem Pr_bad_vertex_le' {E : Finset (Finset α)} {V : Finset α} {L : ℕ} {D e θ : ℝ}
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hD : 0 < D) (hθ0 : 0 ≤ θ) (hθD : θ ≤ D) (he : e ≤ 1) :
    Pr (θ / D) E (fun S => ∃ w ∈ V, ∃ F ∈ (star E w).powersetCard L, F ⊆ S) ≤
      V.card * (2 * θ) ^ L := by
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0 hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  refine (Pr_bad_vertex_le hp0 hp1 E V L).trans ?_
  have : ∀ w ∈ V, ((star E w).card.choose L : ℝ) * (θ / D) ^ L ≤ (2 * θ) ^ L := by
    intro w hw
    have h1 : ((star E w).card.choose L : ℝ) ≤ ((star E w).card : ℝ) ^ L / L.factorial :=
      Nat.choose_le_pow_div L _
    have hfac : (1 : ℝ) ≤ L.factorial := Nat.one_le_cast.2 (Nat.factorial_pos L)
    have h2 : ((star E w).card : ℝ) ^ L / L.factorial ≤ ((star E w).card : ℝ) ^ L :=
      div_le_self (by positivity) hfac
    have h3 : ((star E w).card : ℝ) * (θ / D) ≤ 2 * θ := by
      have := (hdeg w hw).2
      have h4 : ((star E w).card : ℝ) * θ ≤ D * (1 + e) * θ := mul_le_mul_of_nonneg_right this hθ0
      have h5 : D * θ * e ≤ D * θ * 1 := mul_le_mul_of_nonneg_left he (mul_nonneg hD.le hθ0)
      rw [mul_div_assoc']
      rw [div_le_iff₀ hD]
      linarith
    calc ((star E w).card.choose L : ℝ) * (θ / D) ^ L
        ≤ ((star E w).card : ℝ) ^ L * (θ / D) ^ L := by gcongr; exact h1.trans h2
      _ = (((star E w).card : ℝ) * (θ / D)) ^ L := by rw [mul_pow]
      _ ≤ (2 * θ) ^ L := by gcongr
  refine (sum_le_sum this).trans (le_of_eq ?_)
  rw [sum_const, nsmul_eq_mul]

theorem Pr_fdeg_dev_le {E : Finset (Finset α)} {V : Finset α} {k : ℕ} {D e C θ η : ℝ}
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C) (hk2 : 2 ≤ k)
    (hD : 0 < D) (hC : 0 < C) (hθ0 : 0 ≤ θ) (hθD : θ ≤ D) (he : e ≤ 1) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) {v : α} (hv : v ∈ V) :
    Pr (θ / D) E (fun S => fdeg E v S ≤ Ex (θ / D) E (fdeg E v) - θ * η * D ∨
        Ex (θ / D) E (fdeg E v) + θ * η * D ≤ fdeg E v S) ≤
      2 * Real.exp (-(θ * η ^ 2 * D / (16 * k ^ 2 * C))) := by
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0 hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set c : Finset α → ℝ := fun a => ∑ u ∈ a.erase v, (codeg E u v : ℝ)
  set lam := η / (8 * k ^ 2 * C) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hca : ∀ a ∈ E, lam * c a ≤ 1 := by
    intro a ha
    have h1 : c a ≤ k * C := by
      have : c a ≤ ∑ u ∈ a.erase v, C := by
        refine sum_le_sum fun u hu => hcod u v (ne_of_mem_erase hu)
      refine this.trans ?_
      rw [sum_const, nsmul_eq_mul]
      have : ((a.erase v).card : ℝ) ≤ k := by
        have := (card_le_card (erase_subset v a)).trans (hk a ha).le
        exact_mod_cast this
      nlinarith
    have hc0 : 0 ≤ c a := sum_nonneg fun u _ => Nat.cast_nonneg _
    calc lam * c a ≤ lam * (k * C) := by gcongr
      _ = η / (8 * k) := by rw [hlam]; field_simp
      _ ≤ 1 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        rw [div_le_one (by positivity)]; nlinarith
  have hsum : ∑ a ∈ E, c a ^ 2 ≤ 4 * k ^ 2 * C * D ^ 2 := by
    have := sum_sq_lip_fdeg_le (Dmax := 2 * D) hk hEV
      (fun u hu => (hdeg u hu).2.trans (by nlinarith)) hcod v
    refine this.trans ?_
    have hv' : ((star E v).card : ℝ) ≤ 2 * D := (hdeg v hv).2.trans (by nlinarith)
    have hk1 : (k : ℝ) - 1 ≤ k := by linarith
    have : ((k : ℝ) - 1) * (star E v).card ≤ k * (2 * D) := by
      have : (0 : ℝ) ≤ k - 1 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        linarith
      nlinarith [(Nat.cast_nonneg (star E v).card : (0 : ℝ) ≤ _)]
    calc (k : ℝ) * (2 * D) * C * ((k - 1) * (star E v).card)
        ≤ k * (2 * D) * C * (k * (2 * D)) := by gcongr
      _ = 4 * k ^ 2 * C * D ^ 2 := by ring
  have hexp : -(lam * (θ * η * D)) + lam ^ 2 * (θ / D) * ∑ a ∈ E, c a ^ 2 ≤
      -(θ * η ^ 2 * D / (16 * k ^ 2 * C)) := by
    have h1 : lam ^ 2 * (θ / D) * ∑ a ∈ E, c a ^ 2 ≤ lam ^ 2 * (θ / D) * (4 * k ^ 2 * C * D ^ 2) := by
      gcongr
    have h2 : lam ^ 2 * (θ / D) * (4 * k ^ 2 * C * D ^ 2) = θ * η ^ 2 * D / (16 * k ^ 2 * C) := by
      rw [hlam]; field_simp; ring
    have h3 : lam * (θ * η * D) = 2 * (θ * η ^ 2 * D / (16 * k ^ 2 * C)) := by
      rw [hlam]; field_simp; ring
    linarith
  refine (Pr_or_le hp0 hp1 E _ _).trans ?_
  have hl := Pr_le_le hp0 hp1 E (fdeg E v) c (lip_fdeg E v) (θ * η * D) lam hlam0 hca
  have hu := Pr_ge_le hp0 hp1 E (fdeg E v) c (lip_fdeg E v) (θ * η * D) lam hlam0 hca
  have hm := Real.exp_le_exp.2 hexp
  linarith

theorem Pr_fcov_dev_le {E : Finset (Finset α)} {V X : Finset α} {k : ℕ} {D e θ : ℝ}
    (hk : ∀ F ∈ E, F.card = k) (hXV : X ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hk2 : 2 ≤ k) (hD : 0 < D) (hθ0 : 0 ≤ θ) (hθD : θ ≤ D) (he : e ≤ 1) :
    Pr (θ / D) E (fun S => Ex (θ / D) E (fcov X) + θ * X.card / 8 ≤ fcov X S) ≤
      Real.exp (-(θ * X.card / (512 * k))) := by
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0 hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set lam : ℝ := 1 / (32 * k) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hca : ∀ a ∈ E, lam * ((a ∩ X).card : ℝ) ≤ 1 := by
    intro a ha
    have : ((a ∩ X).card : ℝ) ≤ k := by
      have := (card_le_card (inter_subset_left : a ∩ X ⊆ a)).trans (hk a ha).le
      exact_mod_cast this
    calc lam * ((a ∩ X).card : ℝ) ≤ lam * k := by gcongr
      _ ≤ 1 := by rw [hlam]; field_simp; norm_num
  have hsum : ∑ a ∈ E, ((a ∩ X).card : ℝ) ^ 2 ≤ k * (X.card * (2 * D)) := by
    refine (sum_sq_lip_fcov_le hk X).trans ?_
    gcongr
    calc ∑ u ∈ X, ((star E u).card : ℝ) ≤ ∑ u ∈ X, 2 * D :=
          sum_le_sum fun u hu => (hdeg u (hXV hu)).2.trans (by nlinarith)
      _ = X.card * (2 * D) := by rw [sum_const, nsmul_eq_mul]
  have hexp : -(lam * (θ * X.card / 8)) + lam ^ 2 * (θ / D) * ∑ a ∈ E, ((a ∩ X).card : ℝ) ^ 2 ≤
      -(θ * X.card / (512 * k)) := by
    have h1 : lam ^ 2 * (θ / D) * ∑ a ∈ E, ((a ∩ X).card : ℝ) ^ 2 ≤
        lam ^ 2 * (θ / D) * (k * (X.card * (2 * D))) := by gcongr
    have h2 : lam ^ 2 * (θ / D) * (k * (X.card * (2 * D))) = θ * X.card / (512 * k) := by
      rw [hlam]; field_simp; ring
    have h3 : lam * (θ * X.card / 8) = 2 * (θ * X.card / (512 * k)) := by
      rw [hlam]; field_simp; ring
    linarith
  have hu := Pr_ge_le hp0 hp1 E (fcov X) _ (lip_fcov E X) (θ * X.card / 8) lam hlam0 hca
  exact hu.trans (Real.exp_le_exp.2 hexp)

theorem Pr_wit_T_le {E : Finset (Finset α)} {V X : Finset α} {k : ℕ} {D e θ ζ : ℝ}
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V) (hXV : X ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hD : 0 < D) (hθ0 : 0 ≤ θ) (hθD : θ ≤ D) (he : e ≤ 1) (hζ : 160 * k * θ ^ 2 ≤ ζ) :
    Pr (θ / D) E (fun S => ∃ P ∈ witFam E X ⌈ζ * X.card⌉₊, P.biUnion pairSet ⊆ S) ≤
      Real.exp (-(ζ * X.card)) := by
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0 hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  refine (Pr_wit_le hp0 hp1 E X _).trans ?_
  have hN := card_witPairs_le (Dmax := 2 * D) (by positivity) hk hEV hXV
    (fun u hu => (hdeg u hu).2.trans (by nlinarith))
  have hζ0 : 0 ≤ ζ := le_trans (by positivity) hζ
  have h40 : 40 * ((witPairs E X).card * (θ / D) ^ 2) ≤ (⌈ζ * X.card⌉₊ : ℝ) := by
    have h1 : ((witPairs E X).card : ℝ) * (θ / D) ^ 2 ≤
        X.card * (2 * D) * (k * (2 * D)) * (θ / D) ^ 2 := by gcongr
    have h2 : (X.card : ℝ) * (2 * D) * (k * (2 * D)) * (θ / D) ^ 2 = 4 * k * θ ^ 2 * X.card := by
      field_simp; ring
    have h3 : 160 * k * θ ^ 2 * X.card ≤ ζ * X.card := by gcongr
    have h4 : ζ * X.card ≤ (⌈ζ * X.card⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  refine (choose_mul_pow_le_exp hp0 h40).trans ?_
  exact Real.exp_le_exp.2 (neg_le_neg (Nat.le_ceil _))

theorem filter_not_mem_cov (X : Finset α) (S : Finset (Finset α)) :
    X.filter (fun u => u ∉ cov S) = X \ cov S := by
  ext u; simp [mem_sdiff]

theorem round_deg_of_dev {E S : Finset (Finset α)} {V : Finset α} {k : ℕ}
    {D e C θ η : ℝ} (hk2 : 2 ≤ k) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C)
    (hD1 : 1 ≤ D) (hC : 0 < C) (hCD : k * C ≤ D / 2) (he0 : 0 ≤ e) (he : e ≤ 1 / 4)
    (hθ0 : 0 < θ) (hθ : k * θ ≤ 1 / 4) (hη0 : 0 < η) {v : α} (hv : v ∈ V)
    (hdev : Ex (θ / D) E (fdeg E v) - θ * η * D < fdeg E v S ∧
        fdeg E v S < Ex (θ / D) E (fdeg E v) + θ * η * D) :
    D * (1 - (k - 1) * θ) *
        (1 - (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η)) ≤ fdeg E v S ∧
      fdeg E v S ≤ D * (1 - (k - 1) * θ) *
        (1 + (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η)) := by
  have hD : 0 < D := by linarith
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hθD : θ ≤ D := by nlinarith
  have he1 : e ≤ 1 := by linarith
  set y := (k - 1) * θ * (1 - e) - (k - 1) * ((k - 1) * θ) * (C / D) with hy
  have hk1 : (0 : ℝ) ≤ k - 1 := by linarith
  have hCD' : (k - 1) * (C / D) ≤ 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hD]; nlinarith
  have hx0 : 0 ≤ (k - 1) * θ := mul_nonneg hk1 hθ0.le
  have hy0 : 0 ≤ y := by
    rw [hy]
    have : (k - 1) * ((k - 1) * θ) * (C / D) = (k - 1) * θ * ((k - 1) * (C / D)) := by ring
    rw [this]
    nlinarith
  have hy1 : y ≤ 1 := by
    have : 0 ≤ (k - 1) * ((k - 1) * θ) * (C / D) := by
      have := div_nonneg hC.le hD.le
      positivity
    rw [hy]; nlinarith
  have hEu := Ex_fdeg_le hk hEV hdeg hcod hC.le hD hθ0.le hθD hy hy0 hy1 hv
  have hEl := Ex_fdeg_ge hk hEV hdeg hD hθ0.le hθD (by nlinarith) hv
  have hup := deg_upper_alg hk0 hθ0.le hθ he0 he1 (div_nonneg hC.le hD.le) hη0.le hy hy0
  have hlo := deg_lower_alg hk0 hθ0.le hθ he0 (div_nonneg hC.le hD.le) hη0.le
  constructor
  · have : D * ((1 - (k - 1) * θ) *
        (1 - (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η))) ≤
        D * ((1 - e) * (1 - (k - 1) * θ * (1 + e)) - θ * η) :=
      mul_le_mul_of_nonneg_left hlo hD.le
    linarith [hdev.1, hEl]
  · have : D * ((1 + e) * (1 - y + y ^ 2) + θ * η) ≤ D * ((1 - (k - 1) * θ) *
        (1 + (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η))) :=
      mul_le_mul_of_nonneg_left hup hD.le
    linarith [hdev.2, hEu]

theorem round_cov_of_dev {E S : Finset (Finset α)} {V T : Finset α} {D e θ : ℝ}
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hD1 : 1 ≤ D) (he0 : 0 ≤ e) (he : e ≤ 1 / 4) (hθ0 : 0 < θ) (hθ8 : θ ≤ 1 / 8)
    (hlt : fcov (T ∩ V) S < Ex (θ / D) E (fcov (T ∩ V)) + θ * (T ∩ V).card / 8) :
    (((T ∩ V) \ cov S).card : ℝ) ≤ (1 - θ / 2) * (T ∩ V).card := by
  have hD : 0 < D := by linarith
  have hE := Ex_fcov_le (E := E) (X := T ∩ V) inter_subset_right hdeg hD hθ0.le (by linarith)
    (by linarith) he0 (by linarith)
  have hf : fcov (T ∩ V) S = (((T ∩ V) \ cov S).card : ℝ) := by
    unfold fcov; rw [filter_not_mem_cov]
  rw [hf] at hlt
  have hX0 : (0 : ℝ) ≤ (T ∩ V).card := Nat.cast_nonneg _
  have : (T ∩ V).card * (1 - θ * (1 - e) + θ ^ 2) + θ * (T ∩ V).card / 8 ≤
      (1 - θ / 2) * (T ∩ V).card := by
    have : θ * e + θ ^ 2 + θ / 8 ≤ θ / 2 := by nlinarith
    nlinarith
  linarith

theorem round_waste_of_good {E S : Finset (Finset α)} {V T : Finset α} {k L : ℕ} {ζ : ℝ}
    (hSE : S ⊆ E) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hgood : ∀ w ∈ V, (S.filter (fun g => w ∈ g)).card ≤ L)
    (hno : ¬ ∃ P ∈ witFam E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊, P.biUnion pairSet ⊆ S)
    (hζ0 : 0 ≤ ζ) :
    ((waste S ∩ (T ∩ V)).card : ℝ) ≤ 2 * k * (1 + k * L) * ζ * (T ∩ V).card := by
  have hw := card_waste_inter_le hSE hk hEV hgood hno
  have hs : ((⌈ζ * (T ∩ V).card⌉₊ - 1 : ℕ) : ℝ) ≤ ζ * (T ∩ V).card := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ ζ * (T ∩ V).card by positivity)
    rcases Nat.eq_zero_or_pos ⌈ζ * (T ∩ V).card⌉₊ with h0 | hpos
    · rw [h0]; simp only [Nat.zero_sub, Nat.cast_zero]; positivity
    · rw [Nat.cast_sub hpos]; push_cast; linarith
  have hw' : ((waste S ∩ (T ∩ V)).card : ℝ) ≤
      k * (1 + k * L) * (2 * ((⌈ζ * (T ∩ V).card⌉₊ - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hw
  calc ((waste S ∩ (T ∩ V)).card : ℝ)
      ≤ k * (1 + k * L) * (2 * ((⌈ζ * (T ∩ V).card⌉₊ - 1 : ℕ) : ℝ)) := hw'
    _ ≤ k * (1 + k * L) * (2 * (ζ * (T ∩ V).card)) := by gcongr
    _ = 2 * k * (1 + k * L) * ζ * (T ∩ V).card := by ring

/-- **One round of the nibble.** -/
theorem nibble_round {E : Finset (Finset α)} {V : Finset α} {k L : ℕ}
    {D e C θ η τ ζ : ℝ} (𝒯 : Finset (Finset α))
    (hk2 : 2 ≤ k) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C)
    (hD1 : 1 ≤ D) (hC : 0 < C) (hCD : k * C ≤ D / 2) (he0 : 0 ≤ e) (he : e ≤ 1 / 4)
    (hθ0 : 0 < θ) (hθ : k * θ ≤ 1 / 4) (hη0 : 0 < η) (hη : η ≤ 1)
    (hζ : 160 * k * θ ^ 2 ≤ ζ)
    (hprob : V.card * (2 * θ) ^ L
      + 2 * V.card * Real.exp (-(θ * η ^ 2 * D / (16 * k ^ 2 * C)))
      + 𝒯.card * (Real.exp (-(θ * τ / (512 * k))) + Real.exp (-(ζ * τ))) < 1) :
    ∃ S ⊆ E,
      (∀ v ∈ V \ cov S,
        D * (1 - (k - 1) * θ) *
            (1 - (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η))
          ≤ (star (nextE E S) v).card ∧
        ((star (nextE E S) v).card : ℝ) ≤
          D * (1 - (k - 1) * θ) *
            (1 + (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η))) ∧
      (∀ T ∈ 𝒯, τ ≤ (T ∩ V).card →
        (((T ∩ V) \ cov S).card : ℝ) ≤ (1 - θ / 2) * (T ∩ V).card) ∧
      (∀ T ∈ 𝒯, τ ≤ (T ∩ V).card →
        ((waste S ∩ (T ∩ V)).card : ℝ) ≤ 2 * k * (1 + k * L) * ζ * (T ∩ V).card) := by
  classical
  have hD : 0 < D := by linarith
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hθ8 : θ ≤ 1 / 8 := by nlinarith
  have hθD : θ ≤ D := by linarith
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0.le hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  have he1 : e ≤ 1 := by linarith
  set 𝒯L := 𝒯.filter (fun T => τ ≤ ((T ∩ V).card : ℝ))
  set B1 : Finset (Finset α) → Prop := fun S => ∃ w ∈ V, ∃ F ∈ (star E w).powersetCard L, F ⊆ S
  set B2 : Finset (Finset α) → Prop := fun S => ∃ v ∈ V,
    (fdeg E v S ≤ Ex (θ / D) E (fdeg E v) - θ * η * D ∨ Ex (θ / D) E (fdeg E v) + θ * η * D ≤ fdeg E v S)
  set B3 : Finset (Finset α) → Prop := fun S => ∃ T ∈ 𝒯L,
    Ex (θ / D) E (fcov (T ∩ V)) + θ * (T ∩ V).card / 8 ≤ fcov (T ∩ V) S
  set B4 : Finset (Finset α) → Prop := fun S => ∃ T ∈ 𝒯L,
    ∃ P ∈ witFam E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊, P.biUnion pairSet ⊆ S
  have hP1 : Pr (θ / D) E B1 ≤ V.card * (2 * θ) ^ L := Pr_bad_vertex_le' hdeg hD hθ0.le hθD he1
  have hP2 : Pr (θ / D) E B2 ≤ 2 * V.card * Real.exp (-(θ * η ^ 2 * D / (16 * k ^ 2 * C))) := by
    refine (Pr_exists_le hp0 hp1 E V _).trans ?_
    refine (sum_le_sum fun v hv => Pr_fdeg_dev_le hk hEV hdeg hcod hk2 hD hC hθ0.le hθD he1
      hη0.le hη hv).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul]; ring
  have hP3 : Pr (θ / D) E B3 ≤ 𝒯.card * Real.exp (-(θ * τ / (512 * k))) := by
    refine (Pr_exists_le hp0 hp1 E 𝒯L _).trans ?_
    have : ∀ T ∈ 𝒯L, Pr (θ / D) E (fun S => Ex (θ / D) E (fcov (T ∩ V)) + θ * (T ∩ V).card / 8 ≤
        fcov (T ∩ V) S) ≤ Real.exp (-(θ * τ / (512 * k))) := by
      intro T hT
      refine (Pr_fcov_dev_le hk inter_subset_right hdeg hk2 hD hθ0.le hθD he1).trans ?_
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have := (mem_filter.1 hT).2
      gcongr
    refine (sum_le_sum this).trans ?_
    rw [sum_const, nsmul_eq_mul]
    gcongr
    exact filter_subset _ _
  have hP4 : Pr (θ / D) E B4 ≤ 𝒯.card * Real.exp (-(ζ * τ)) := by
    refine (Pr_exists_le hp0 hp1 E 𝒯L _).trans ?_
    have hζ0 : 0 ≤ ζ := le_trans (by positivity) hζ
    have : ∀ T ∈ 𝒯L, Pr (θ / D) E (fun S => ∃ P ∈ witFam E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊,
        P.biUnion pairSet ⊆ S) ≤ Real.exp (-(ζ * τ)) := by
      intro T hT
      refine (Pr_wit_T_le hk hEV inter_subset_right hdeg hD hθ0.le hθD he1 hζ).trans ?_
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have := (mem_filter.1 hT).2
      gcongr
    refine (sum_le_sum this).trans ?_
    rw [sum_const, nsmul_eq_mul]
    gcongr
    exact filter_subset _ _
  have hbad : Pr (θ / D) E (fun S => B1 S ∨ B2 S ∨ B3 S ∨ B4 S) < 1 := by
    have h1 := Pr_or_le hp0 hp1 E B1 (fun S => B2 S ∨ B3 S ∨ B4 S)
    have h2 := Pr_or_le hp0 hp1 E B2 (fun S => B3 S ∨ B4 S)
    have h3 := Pr_or_le hp0 hp1 E B3 B4
    have : 𝒯.card * Real.exp (-(θ * τ / (512 * k))) + 𝒯.card * Real.exp (-(ζ * τ)) =
        𝒯.card * (Real.exp (-(θ * τ / (512 * k))) + Real.exp (-(ζ * τ))) := by ring
    linarith
  obtain ⟨S, hSE, hS⟩ := exists_not_of_Pr_lt_one E hbad
  have hn1 : ¬ B1 S := fun h => hS (Or.inl h)
  have hn2 : ¬ B2 S := fun h => hS (Or.inr (Or.inl h))
  have hn3 : ¬ B3 S := fun h => hS (Or.inr (Or.inr (Or.inl h)))
  have hn4 : ¬ B4 S := fun h => hS (Or.inr (Or.inr (Or.inr h)))
  refine ⟨S, hSE, fun v hv => ?_, fun T hT hτT => ?_, fun T hT hτT => ?_⟩
  · rw [mem_sdiff] at hv
    rw [card_star_nextE hv.2]
    have hdev : Ex (θ / D) E (fdeg E v) - θ * η * D < fdeg E v S ∧
        fdeg E v S < Ex (θ / D) E (fdeg E v) + θ * η * D := by
      by_contra h
      rw [not_and_or, not_lt, not_lt] at h
      exact hn2 ⟨v, hv.1, h⟩
    exact round_deg_of_dev hk2 hk hEV hdeg hcod hD1 hC hCD he0 he hθ0 hθ hη0 hv.1 hdev
  · have hTL : T ∈ 𝒯L := mem_filter.2 ⟨hT, hτT⟩
    have hlt : fcov (T ∩ V) S < Ex (θ / D) E (fcov (T ∩ V)) + θ * (T ∩ V).card / 8 := by
      by_contra h
      exact hn3 ⟨T, hTL, not_lt.1 h⟩
    exact round_cov_of_dev hdeg hD1 he0 he hθ0 hθ8 hlt
  · have hTL : T ∈ 𝒯L := mem_filter.2 ⟨hT, hτT⟩
    have hgood : ∀ w ∈ V, (S.filter (fun g => w ∈ g)).card ≤ L := by
      intro w hw
      by_contra hcon
      push_neg at hcon
      obtain ⟨F, hF, hFc⟩ := exists_subset_card_eq hcon.le
      refine hn1 ⟨w, hw, F, mem_powersetCard.2 ⟨?_, hFc⟩, hF.trans (filter_subset _ _)⟩
      intro g hg
      have := mem_filter.1 (hF hg)
      exact mem_star.2 ⟨hSE this.1, this.2⟩
    have hno : ¬ ∃ P ∈ witFam E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊, P.biUnion pairSet ⊆ S :=
      fun h => hn4 ⟨T, hTL, h⟩
    exact round_waste_of_good hSE hk hEV hgood hno (le_trans (by positivity) hζ)

end RefinedAbsorption.Nibble
