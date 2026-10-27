module
public import RequestProject.Original2024.RelReserves

/-!
# Lemma 2.1 of the survey (Reserves), as stated

The survey's Lemma 2.1 (`ReservesLemma`): for `q > r ≥ 1` there is `γ ∈ (0,1)` such that for all
large `n` and every `p ∈ [n^{-γ}, 1)` there is `X ⊆ K_n^r` with `Δ(X) ≤ 2pn` such that every
edge `e ∉ X` lies in at least `½ p^{binom(q,r)-1} binom(n, q-r)` copies of `K_q^r` in `X ∪ {e}`.

`X` is the `p`-random subset of `K_n^r`.  The proof uses the finite product-probability toolkit
(`Nibble/FiniteProb.lean`) and the counting lemmas of `Original2024/RelReserves.lean`:

* the degree of every `(r-1)`-set is at most `E + pn ≤ 2pn` except with probability
  `exp(-pn/4)` (`upper_tail_deg`);
* the number of reserve cliques through `e` has mean `binom(n-r, q-r) p^{m-1} ≥ ¾ binom(n,q-r)
  p^{m-1}` (`m = binom(q,r)`), and drops by more than `¼ binom(n, q-r) p^{m-1}` with probability
  at most `exp(-n^{1/2}/(64 m K))` (`lower_tail_frac`), because `p^{2(m-1)} ≥ n^{-1/2}` for
  `γ = 1/(4m)`;
* a union bound over the `≤ n^r` sets.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset RefinedAbsorption.Nibble RefinedAbsorption.Original2024

/-- **Lower tail at a prescribed distance** for functions with bounded differences: if
`c_a ≤ M`, `∑ c_a ≤ T1` and `0 ≤ t ≤ 2 p T1`, then `P(f ≤ E f - t) ≤ exp(-t² / (4 p M T1))`. -/
theorem lower_tail_frac {β : Type*} [DecidableEq β] {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (E : Finset β) (f : Finset β → ℝ) (c : β → ℝ) (hf : LipOn E f c) (M T1 t : ℝ) (hM : 0 < M)
    (hT1 : 0 < T1) (hc0 : ∀ a ∈ E, 0 ≤ c a) (hcM : ∀ a ∈ E, c a ≤ M) (hcT : ∑ a ∈ E, c a ≤ T1)
    (ht0 : 0 ≤ t) (htT : t ≤ 2 * p * T1) :
    Pr p E (fun S => f S ≤ Ex p E f - t) ≤ Real.exp (-(t ^ 2 / (4 * p * M * T1))) := by
  set lam := t / (2 * p * M * T1) with hlam
  have hden : 0 < 2 * p * M * T1 := by positivity
  have hlam0 : 0 ≤ lam := div_nonneg ht0 hden.le
  have hc : ∀ a ∈ E, lam * c a ≤ 1 := by
    intro a ha
    calc lam * c a ≤ lam * M := mul_le_mul_of_nonneg_left (hcM a ha) hlam0
      _ = t / (2 * p * T1) := by rw [hlam]; field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact htT
  have hsq : ∑ a ∈ E, c a ^ 2 ≤ M * T1 := by
    calc ∑ a ∈ E, c a ^ 2 ≤ ∑ a ∈ E, M * c a :=
          sum_le_sum fun a ha => by rw [sq]; exact mul_le_mul_of_nonneg_right (hcM a ha) (hc0 a ha)
      _ = M * ∑ a ∈ E, c a := by rw [mul_sum]
      _ ≤ M * T1 := mul_le_mul_of_nonneg_left hcT hM.le
  refine (Pr_le_le hp0.le hp1 E f c hf t lam hlam0 hc).trans ?_
  apply Real.exp_le_exp.2
  have h2 : lam ^ 2 * p * ∑ a ∈ E, c a ^ 2 ≤ lam ^ 2 * p * (M * T1) := by
    apply mul_le_mul_of_nonneg_left hsq; positivity
  have h3 : -(lam * t) + lam ^ 2 * p * (M * T1) = -(t ^ 2 / (4 * p * M * T1)) := by
    rw [hlam]; field_simp; ring
  linarith

/-- `binom(q, r) ≥ 2` for `1 ≤ r < q`. -/
theorem two_le_choose_of_lt' {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) : 2 ≤ q.choose r := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have h1 := Nat.choose_pos (show r' ≤ q' by omega)
  have h2 := Nat.choose_pos (show r' + 1 ≤ q' by omega)
  omega

/-- The cliques of `K_n^r` through an `r`-set `e`: all `q`-supersets of `e`. -/
theorem card_cliquesThrough_complete {n q r : ℕ} {e : Finset (Fin n)} (he : e.card = r)
    (hrq : r ≤ q) :
    (cliquesThrough q r (completeRGraph (Fin n) r) e).card = (n - r).choose (q - r) := by
  have h : cliquesThrough q r (completeRGraph (Fin n) r) e =
      ((univ : Finset (Fin n)).powersetCard q).filter (fun Q => e ⊆ Q) := by
    ext Q
    simp only [cliquesThrough, cliquesOf, mem_filter, and_congr_left_iff]
    intro _
    constructor
    · exact fun h => h.1
    · intro hQ
      refine ⟨hQ, fun f hf => ?_⟩
      exact mem_powersetCard.2 ⟨subset_univ _, (mem_powersetCard.1 hf).2⟩
  rw [h, card_powersetCard_filter_superset (subset_univ e) (by omega), card_univ,
    Fintype.card_fin, he]

/-- The numerical bound on the exponent of the lower tail. -/
theorem reserve_exponent_ge {n k m : ℕ} (hk1 : 1 ≤ k) (hn : 2 * k ≤ n) (hn1 : 1 ≤ n)
    {p : ℝ} (hp0 : 0 < p) (hm0 : (0 : ℝ) < m)
    (hP : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p ^ (m - 1)) ^ 2) :
    (n : ℝ) ^ (1 / 2 : ℝ) / (64 * m * (2 ^ k * (k.factorial : ℝ)) ^ 2) ≤
      ((1 / 4) * p ^ (m - 1) * (n.choose k)) ^ 2 /
        (4 * p * (n : ℝ) ^ (k - 1) * ((m : ℝ) * (n : ℝ) ^ k / p)) := by
  set K₁ : ℝ := 2 ^ k * (k.factorial : ℝ) with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set B := (n.choose k : ℝ) with hB
  set y := (n : ℝ) ^ (k - 1) with hy
  have hy0 : 0 < y := by positivity
  have hxk : (n : ℝ) ^ k = n * y := by
    rw [hy, ← pow_succ']; congr 1; omega
  have hBlow : (n : ℝ) * y / K₁ ≤ B := by
    rw [← hxk]
    have hB' : ((n : ℝ) / 2) ^ k / k.factorial ≤ (n.choose k : ℝ) := by
      refine le_trans ?_ (Nat.pow_le_choose k n)
      gcongr
      rw [Nat.cast_sub (by omega)]; push_cast
      have : (2 * k : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc (n : ℝ) ^ k / K₁ = ((n : ℝ) / 2) ^ k / k.factorial := by
          rw [hK₁, div_pow]; field_simp
      _ ≤ B := hB'
  have hhalf : (n : ℝ) ^ (-(1 / 2 : ℝ)) * n = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hn0.ne']; norm_num
  have hden : 4 * p * y * ((m : ℝ) * (n * y) / p) = 4 * m * n * y ^ 2 := by
    field_simp
  rw [hxk, hden, div_le_div_iff₀ (by positivity) (by positivity)]
  have hB0 : 0 ≤ (n : ℝ) * y / K₁ := by positivity
  have hBsq : ((n : ℝ) * y / K₁) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hB0 hBlow 2
  have hsq : ((1 / 4) * p ^ (m - 1) * B) ^ 2 = (1 / 16) * (p ^ (m - 1)) ^ 2 * B ^ 2 := by ring
  rw [hsq, ← hhalf]
  have hK : ((n : ℝ) * y / K₁) ^ 2 * K₁ ^ 2 = (n : ℝ) ^ 2 * y ^ 2 := by field_simp
  have step : (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) * y / K₁) ^ 2 ≤ (p ^ (m - 1)) ^ 2 * B ^ 2 :=
    mul_le_mul hP hBsq (by positivity) (by positivity)
  calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * n * (4 * m * n * y ^ 2)
      = 4 * m * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (((n : ℝ) * y / K₁) ^ 2 * K₁ ^ 2)) := by
        rw [hK]; ring
    _ = 4 * m * K₁ ^ 2 * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) * y / K₁) ^ 2) := by ring
    _ ≤ 4 * m * K₁ ^ 2 * ((p ^ (m - 1)) ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left step (by positivity)
    _ = 1 / 16 * (p ^ (m - 1)) ^ 2 * B ^ 2 * (64 * m * K₁ ^ 2) := by ring

set_option maxHeartbeats 1000000 in
/-- **Lemma 2.1 of the survey (Reserves)**, exactly as stated (`ReservesLemma`). -/
theorem reservesLemma : ReservesLemma := by
  classical
  intro q r hr hrq
  set m := q.choose r with hm
  set k := q - r with hk
  have hk1 : 1 ≤ k := by omega
  have hm2 : 2 ≤ m := two_le_choose_of_lt' hr hrq
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  set γ : ℝ := 1 / (4 * m) with hγ
  have hγ0 : 0 < γ := by positivity
  have hγ8 : γ ≤ 1 / 8 := by
    rw [hγ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set K₁ : ℝ := 2 ^ k * (k.factorial : ℝ) with hK₁
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 4 * r * k ≤ n ∧ 2 * k ≤ n ∧ 2 ≤ n ∧
      Real.log 4 + r * Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / 4 ∧
      Real.log 4 + r * Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (64 * m * K₁ ^ 2) := by
    filter_upwards [Filter.eventually_ge_atTop (4 * r * k), Filter.eventually_ge_atTop (2 * k),
      Filter.eventually_ge_atTop 2,
      ev_log_le_rpow_div (s := 1 / 2) (K := 4) (A := Real.log 4) (B := r) (by norm_num)
        (by norm_num) (Nat.cast_nonneg r),
      ev_log_le_rpow_div (s := 1 / 2) (K := 64 * m * K₁ ^ 2) (A := Real.log 4) (B := r)
        (by norm_num) (by positivity) (Nat.cast_nonneg r)] with n h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨γ, hγ0, by linarith, n₀, fun n hn p hpγ hp1' => ?_⟩
  obtain ⟨hn4, hn2k, hn2, hY1, hY2⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hpγ
  have hp1 : p ≤ 1 := hp1'.le
  set G := completeRGraph (Fin n) r with hG
  have hGr : IsRGraph r G := fun _ he => (mem_powersetCard.1 he).2
  set B := (n.choose k : ℝ) with hB
  -- the clique count through an edge
  have hCT : ∀ e ∈ G, (3 / 4 : ℝ) * B ≤ (cliquesThrough q r G e).card := by
    intro e he
    rw [card_cliquesThrough_complete (hGr e he) hrq.le]
    have h1 := choose_sub_choose_le n r k
    have hle : (n - r).choose k ≤ n.choose k := Nat.choose_le_choose _ (by omega)
    have h2 : 4 * (n.choose k - (n - r).choose k) ≤ n.choose k := by
      have : 4 * r * k * (n.choose k - (n - r).choose k) ≤ n * (n.choose k - (n - r).choose k) :=
        Nat.mul_le_mul_right _ hn4
      have h3 : 4 * r * k * (n.choose k - (n - r).choose k) ≤ r * k * n.choose k := this.trans h1
      have hrk : 0 < r * k := Nat.mul_pos (by omega) (by omega)
      have : r * k * (4 * (n.choose k - (n - r).choose k)) ≤ r * k * n.choose k := by
        calc r * k * (4 * (n.choose k - (n - r).choose k))
            = 4 * r * k * (n.choose k - (n - r).choose k) := by ring
          _ ≤ _ := h3
      exact Nat.le_of_mul_le_mul_left this hrk
    have h4 : 3 * n.choose k ≤ 4 * (n - r).choose k := by omega
    have : (3 : ℝ) * B ≤ 4 * ((n - r).choose k : ℝ) := by rw [hB]; exact_mod_cast h4
    linarith
  -- probabilistic estimates
  have hpn : (n : ℝ) ^ (1 / 2 : ℝ) ≤ p * n := by
    have h1 : (n : ℝ) ^ (-γ) * n = (n : ℝ) ^ (1 - γ) := by
      rw [sub_eq_neg_add, Real.rpow_add hn0, Real.rpow_one]
    have h2 : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - γ) :=
      Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
    have h3 : (n : ℝ) ^ (-γ) * n ≤ p * n := mul_le_mul_of_nonneg_right hpγ hn0.le
    linarith
  have hP : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p ^ (m - 1)) ^ 2 := by
    have h1 : ((n : ℝ) ^ (-γ)) ^ (2 * (m - 1)) ≤ p ^ (2 * (m - 1)) :=
      pow_le_pow_left₀ (by positivity) hpγ _
    have h2 : ((n : ℝ) ^ (-γ)) ^ (2 * (m - 1)) = (n : ℝ) ^ (-(γ * ((2 * (m - 1) : ℕ) : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
    have h3 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (n : ℝ) ^ (-(γ * ((2 * (m - 1) : ℕ) : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le hn1'
      have : ((2 * (m - 1) : ℕ) : ℝ) ≤ 2 * m := by
        have : 2 * (m - 1) ≤ 2 * m := by omega
        exact_mod_cast this
      have hγm : γ * (2 * m) = 1 / 2 := by rw [hγ]; field_simp; ring
      nlinarith
    rw [← pow_mul, mul_comm (m - 1) 2]
    linarith
  set 𝒮 := (univ : Finset (Fin n)).powersetCard (r - 1) with h𝒮
  set t₀ := (1 / 4) * p ^ (m - 1) * B with ht₀
  have hPr : Pr p G (fun S => (∃ S₀ ∈ 𝒮, Ex p G (degCount S₀) + p * n ≤ degCount S₀ S) ∨
      (∃ e ∈ G, resCount q r G e S ≤ Ex p G (resCount q r G e) - t₀)) < 1 := by
    refine lt_of_le_of_lt (Pr_or_le hp0.le hp1 G _ _) ?_
    have hD : Pr p G (fun S => ∃ S₀ ∈ 𝒮, Ex p G (degCount S₀) + p * n ≤ degCount S₀ S) ≤
        𝒮.card * Real.exp (-(p * n / 4)) := by
      refine (Pr_exists_le hp0.le hp1 G 𝒮 _).trans ?_
      rw [← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun S₀ hS₀ => ?_
      have hS₀c : S₀.card + 1 = r := by
        rw [(mem_powersetCard.1 hS₀).2]; omega
      refine upper_tail_deg hp0.le hp1 G (degCount S₀) (degLip S₀) (lipOn_degCount G S₀)
        (fun a _ => by unfold degLip; split_ifs <;> norm_num) n ?_ (p * n) le_rfl
      rw [sum_degLip_sq]
      exact_mod_cast deg_le_of_rgraph hGr hS₀c
    have hR : Pr p G (fun S => ∃ e ∈ G, resCount q r G e S ≤ Ex p G (resCount q r G e) - t₀) ≤
        G.card * Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / (64 * m * K₁ ^ 2))) := by
      refine (Pr_exists_le hp0.le hp1 G G _).trans ?_
      rw [← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun e he => ?_
      have her : e.card = r := hGr e he
      have hCTle := card_cliquesThrough_le (q := q) G her
      have hpm1 : p ^ (m - 1) ≤ 1 := pow_le_one₀ hp0.le hp1
      refine (lower_tail_frac hp0 hp1 G (resCount q r G e) (resLip q r G e)
        (lipOn_resCount q r G e) ((n : ℝ) ^ (q - r - 1)) ((m : ℝ) * (n : ℝ) ^ (q - r) / p) t₀
        (by positivity) (by positivity) (fun a _ => by unfold resLip; positivity)
        (fun a ha => resLip_le G her a (hGr a ha)) ?_ (by positivity) ?_).trans ?_
      · refine (sum_resLip_le G e).trans ?_
        rw [le_div_iff₀ hp0]
        calc (m : ℝ) * (cliquesThrough q r G e).card * p ≤ m * (n : ℝ) ^ (q - r) * 1 := by
              gcongr
          _ = m * (n : ℝ) ^ (q - r) := mul_one _
      · have : 2 * p * ((m : ℝ) * (n : ℝ) ^ (q - r) / p) = 2 * m * (n : ℝ) ^ (q - r) := by
          field_simp
        rw [this, ht₀]
        have hBle : B ≤ (n : ℝ) ^ (q - r) := by
          rw [hB]; exact_mod_cast Nat.choose_le_pow n (q - r)
        have hB0 : 0 ≤ B := by positivity
        have : (1 / 4) * p ^ (m - 1) * B ≤ B := by nlinarith
        nlinarith
      · apply Real.exp_le_exp.2
        have := reserve_exponent_ge (k := k) (m := m) hk1 hn2k (by omega) hp0 hm0 hP
        rw [← hB, ← ht₀] at this
        linarith
    have hS : (𝒮.card : ℝ) ≤ (n : ℝ) ^ r := by
      rw [h𝒮, card_powersetCard, card_univ, Fintype.card_fin]
      have := Nat.choose_le_pow n (r - 1)
      have h2 : n ^ (r - 1) ≤ n ^ r := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast this.trans h2
    have hGc : (G.card : ℝ) ≤ (n : ℝ) ^ r := by
      rw [hG, completeRGraph, card_powersetCard, card_univ, Fintype.card_fin]
      exact_mod_cast Nat.choose_le_pow n r
    have he1 : 0 ≤ Real.exp (-(p * n / 4)) := (Real.exp_pos _).le
    have he2 : 0 ≤ Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / (64 * m * K₁ ^ 2))) :=
      (Real.exp_pos _).le
    have t1 := mul_le_mul_of_nonneg_right hS he1
    have t2 := mul_le_mul_of_nonneg_right hGc he2
    have hd1 : 4 * (n : ℝ) ^ r * Real.exp (-(p * n / 4)) ≤ 1 :=
      four_pow_mul_exp_le (by omega) (by linarith)
    have hd2 : 4 * (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / (64 * m * K₁ ^ 2))) ≤ 1 :=
      four_pow_mul_exp_le (by omega) hY2
    linarith
  obtain ⟨X, hXG, hX⟩ := exists_not_of_Pr_lt_one G hPr
  push_neg at hX
  obtain ⟨hXD, hXR⟩ := hX
  refine ⟨X, hXG, fun S₀ hS₀ => ?_, fun e he => ?_⟩
  · have hS₀m : S₀ ∈ 𝒮 := mem_powersetCard.2 ⟨subset_univ _, by omega⟩
    have h1 := hXD S₀ hS₀m
    rw [Ex_degCount] at h1
    have h2 : (deg G S₀ : ℝ) ≤ n := by exact_mod_cast deg_le_of_rgraph hGr hS₀
    have h3 : (deg G S₀ : ℝ) * p ≤ n * p := mul_le_mul_of_nonneg_right h2 hp0.le
    unfold degCount at h1
    linarith
  · have heG : e ∈ G := (mem_sdiff.1 he).1
    have h1 := hXR e heG
    have her : e.card = r := hGr e heG
    rw [Ex_resCount (q := q) p G her] at h1
    have h2 := resCount_le_reserve q r G e X
    have hCTe := hCT e heG
    have hpm : 0 ≤ p ^ (m - 1) := by positivity
    have h3 : (3 / 4 : ℝ) * B * p ^ (m - 1) ≤ (cliquesThrough q r G e).card * p ^ (m - 1) :=
      mul_le_mul_of_nonneg_right hCTe hpm
    rw [ht₀] at h1
    linarith

end RefinedAbsorption
