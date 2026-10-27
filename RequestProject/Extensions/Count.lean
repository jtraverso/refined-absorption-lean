module
public import RequestProject.Extensions.Embedding
public import RequestProject.Extensions.CountCore

/-!
# The number of Steiner systems is `n^{Θ(n^r)}`

For fixed `q > r ≥ 1` and admissible `n`, the number of `(n, q, r)`-Steiner systems on `Fin n`
satisfies
`c · n^r · log n ≤ log #S(n, q, r) ≤ (q + 1) · n^r · log n`
for some `c > 0` and all large admissible `n` (`log_card_steinerSystems_theta`).

*Lower bound.*  Fix a set `U` of `u ≈ n / m` points, with `u ≤ ε n`.  Every partial Steiner
system inside `U` has `(r-1)`-degrees at most `u ≤ ε n`, so by the completion theorem it lies in
some Steiner system; a Steiner system contains at most `2^{binom(u, r)}` partial systems inside
`U`.  Hence `#S ≥ #PS_k(U) / 2^{binom(u, r)} ≥ B^k / 2^{binom(u, r)}`, where the greedy count of
partial systems gives `B = binom(q, r) binom(u - r, q - r) ≥ u - q + 1` and
`k ≈ binom(u, r) / (2 binom(q, r)^2)`.  Taking logarithms gives `≥ c n^r log n`.

*Upper bound.*  A Steiner system is a set of at most `binom(n, r) ≤ n^r` of the `binom(n, q)`
possible blocks.
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset Filter

/-! ### Upper bound -/

/-- **Upper bound.**  For `n ≥ 2` there are at most `(binom(n, q) + 1)^{binom(n, r)}`
`(n, q, r)`-Steiner systems, hence `log #S(n, q, r) ≤ (q + 1) n^r log n`. -/
theorem card_steinerSystems_le {n q r : ℕ} (hrq : r ≤ q) :
    (steinerSystems q r n).card ≤ (n.choose q + 1) ^ (n.choose r) := by
  classical
  set L := n.choose r
  set M := n.choose q
  have hsub : steinerSystems q r n ⊆ (range (L + 1)).biUnion
      (fun j => ((univ : Finset (Fin n)).powersetCard q).powersetCard j) := by
    intro 𝒮 h𝒮
    have h : IsSteinerSystem q r 𝒮 := by simpa [steinerSystems] using h𝒮
    have hc : 𝒮.card ≤ L := by
      have := (IsSteinerSystem.isPartial h).card_le hrq (U := univ) (fun Q _ => subset_univ Q)
      simpa using this
    refine mem_biUnion.2 ⟨𝒮.card, mem_range.2 (by omega), mem_powersetCard.2 ⟨?_, rfl⟩⟩
    intro Q hQ
    exact mem_powersetCard.2 ⟨subset_univ _, h.card_eq Q hQ⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [add_pow]
  refine sum_le_sum fun j hj => ?_
  rw [card_powersetCard, card_powersetCard, card_univ, Fintype.card_fin, one_pow, mul_one]
  have h1 : 1 ≤ L.choose j := Nat.choose_pos (by have := mem_range.1 hj; omega)
  calc M.choose j ≤ M ^ j := Nat.choose_le_pow _ _
    _ ≤ M ^ j * L.choose j := Nat.le_mul_of_pos_right _ h1

theorem log_card_steinerSystems_le {n q r : ℕ} (hrq : r ≤ q) (hn : 2 ≤ n) :
    Real.log (steinerSystems q r n).card ≤ (q + 1) * (n : ℝ) ^ r * Real.log n := by
  have hN := card_steinerSystems_le (n := n) hrq
  set N := (steinerSystems q r n).card
  rcases Nat.eq_zero_or_pos N with h0 | hN0
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    positivity
  have h1 : (N : ℝ) ≤ ((n.choose q + 1 : ℕ) : ℝ) ^ (n.choose r) := by exact_mod_cast hN
  have h2 : ((n.choose q + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (q + 1) := by
    have a : n.choose q ≤ n ^ q := Nat.choose_le_pow _ _
    have b : n ^ q + 1 ≤ n ^ (q + 1) := by
      rw [pow_succ]; have : 1 ≤ n ^ q := Nat.one_le_pow _ _ (by omega); nlinarith
    exact_mod_cast (by omega : n.choose q + 1 ≤ n ^ (q + 1))
  have h3 : ((n.choose r : ℕ) : ℝ) ≤ (n : ℝ) ^ r := by exact_mod_cast Nat.choose_le_pow _ _
  calc Real.log N ≤ Real.log (((n.choose q + 1 : ℕ) : ℝ) ^ (n.choose r)) :=
        Real.log_le_log (by exact_mod_cast hN0) h1
    _ = (n.choose r : ℝ) * Real.log ((n.choose q + 1 : ℕ) : ℝ) := by rw [Real.log_pow]
    _ ≤ (n : ℝ) ^ r * Real.log ((n : ℝ) ^ (q + 1)) := by
        apply mul_le_mul h3 (Real.log_le_log (by positivity) h2)
        · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n.choose q + 1))
        · positivity
    _ = (q + 1) * (n : ℝ) ^ r * Real.log n := by rw [Real.log_pow]; push_cast; ring

/-! ### Lower bound -/

/-- A pure inequality used in the final estimate. -/
theorem final_estimate {X L A k c : ℝ} (hc : 1 ≤ c) (hk : L / (2 * c ^ 2) - 1 ≤ k)
    (hA : 0 ≤ A) (hX : k * A - L * Real.log 2 ≤ X) (hA8 : 8 * c ^ 2 * Real.log 2 ≤ A)
    (hL8 : 8 * c ^ 2 ≤ L) : L * A / (4 * c ^ 2) ≤ X := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hL0 : 0 ≤ L := le_trans (by positivity) hL8
  have h1 : (L / (2 * c ^ 2) - 1) * A ≤ k * A := mul_le_mul_of_nonneg_right hk hA
  have h2 : L * Real.log 2 ≤ L * A / (8 * c ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h3 : A ≤ L * A / (8 * c ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have e1 : (L / (2 * c ^ 2) - 1) * A = L * A / (2 * c ^ 2) - A := by field_simp
  have e2 : L * A / (4 * c ^ 2) =
      L * A / (2 * c ^ 2) - L * A / (8 * c ^ 2) - L * A / (8 * c ^ 2) := by
    field_simp; ring
  linarith

/-- **The combinatorial core of the lower bound.**  If every partial Steiner system with `k`
blocks inside the `u`-set `U` extends to a Steiner system, and `2 k B ≤ binom(u, q)` with
`B = binom(q, r) binom(u - r, q - r)`, then `B^k ≤ #S(n, q, r) · 2^{binom(u, r)}`. -/
theorem pow_le_card_steiner {n q r k : ℕ} (hrq : r ≤ q) (U : Finset (Fin n))
    (hext : ∀ P ∈ psFamily q r k U, ∃ 𝒮 : Finset (Finset (Fin n)),
      P ⊆ 𝒮 ∧ IsSteinerSystem q r 𝒮)
    (hk : 2 * k * (q.choose r * (U.card - r).choose (q - r)) ≤ U.card.choose q) :
    (q.choose r * (U.card - r).choose (q - r)) ^ k ≤
      (steinerSystems q r n).card * 2 ^ (U.card.choose r) :=
  (card_psFamily_ge hrq U k hk).trans (card_psFamily_le_steiner hrq U hext)

set_option maxHeartbeats 1000000 in
/-- The lower bound at a fixed `n`, under explicit largeness assumptions. -/
theorem lower_bound_at {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {ε : ℝ} {n : ℕ}
    (hcomp : ∀ P : Finset (Finset (Fin n)),
      IsPartialSteinerSystem q r P → MaxDegLE r (coveredEdges r P) (ε * n) →
      ∃ 𝒮 : Finset (Finset (Fin n)), P ⊆ 𝒮 ∧ IsSteinerSystem q r 𝒮)
    {m : ℕ} (hm : 1 ≤ m) (hmε : (1 : ℝ) / m ≤ ε)
    (hn1 : 2 * m * q ≤ n) (hn2 : (2 * m * (q - r).factorial) ^ 2 ≤ n)
    (hn3 : 16 * (q.choose r : ℝ) ^ 2 * Real.log 2 ≤ Real.log n)
    (hn4 : 8 * (q.choose r) ^ 2 * r.factorial * (2 * m) ≤ n) :
    1 / ((2 * m : ℝ) ^ r * r.factorial * 8 * (q.choose r : ℝ) ^ 2) * (n : ℝ) ^ r * Real.log n
      ≤ Real.log (steinerSystems q r n).card := by
  classical
  set cq := q.choose r with hcqdef
  set j := q - r with hjdef
  have hcq : 1 ≤ cq := Nat.choose_pos hrq.le
  have hj1 : 1 ≤ j := by omega
  set u := n / m with hudef
  have hun : u ≤ n := Nat.div_le_self n m
  have hmu : n < m * u + m := by
    have h1 := Nat.div_add_mod n m
    have h2 := Nat.mod_lt n (by omega : 0 < m)
    rw [← hudef] at h1
    omega
  have huq : q ≤ u := by
    by_contra h
    push_neg at h
    have : m * u + m ≤ m * q := by nlinarith
    nlinarith
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le huq
  have hnu : n ≤ 2 * m * (u - q + 1) := by
    have e : u - q + 1 = t + 1 := by omega
    rw [e]
    rw [ht] at hmu
    have hq : q < t + 1 := by
      by_contra h
      push_neg at h
      have : m * (q + t) + m ≤ 2 * m * q := by nlinarith
      omega
    nlinarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnpos : 0 < n := by
    have : 0 < 2 * m * q := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  -- the set `U`
  set U : Finset (Fin n) := (univ : Finset (Fin u)).map (Fin.castLEEmb hun) with hUdef
  have hUc : U.card = u := by simp [hUdef]
  have hεu : (u : ℝ) ≤ ε * n := by
    have h1 : (u : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
    have h2 : (n : ℝ) / m = n * (1 / m) := by ring
    rw [h2] at h1
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set L := u.choose r with hLdef
  set Bu := (u - r).choose j with hBudef
  set k := L / (2 * cq ^ 2) with hkdef
  have hext : ∀ P ∈ psFamily q r k U, ∃ 𝒮 : Finset (Finset (Fin n)),
      P ⊆ 𝒮 ∧ IsSteinerSystem q r 𝒮 := by
    intro P hP
    simp only [psFamily, mem_filter, mem_powersetCard] at hP
    refine hcomp P hP.2 fun S hS => ?_
    have h1 : deg (coveredEdges r P) S ≤ U.card := by
      refine deg_le_card_of_edges_subset (fun e he => ?_) hS
      obtain ⟨Q, hQ, he⟩ := mem_biUnion.1 he
      exact ⟨(mem_powersetCard.1 he).1.trans (mem_powersetCard.1 (hP.1.1 hQ)).1,
        (mem_powersetCard.1 he).2⟩
    rw [hUc] at h1
    exact le_trans (by exact_mod_cast h1) hεu
  have hk : 2 * k * (cq * Bu) ≤ u.choose q := by
    have hid : u.choose q * cq = L * Bu := Nat.choose_mul (n := u) (k := q) (s := r) hrq.le
    have h1 : k * (2 * cq ^ 2) ≤ L := Nat.div_mul_le_self L (2 * cq ^ 2)
    have h2 : 2 * k * (cq * Bu) * cq ≤ u.choose q * cq := by
      rw [hid]
      calc 2 * k * (cq * Bu) * cq = k * (2 * cq ^ 2) * Bu := by ring
        _ ≤ L * Bu := Nat.mul_le_mul_right _ h1
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  have hmain := pow_le_card_steiner (k := k) hrq.le U hext (by rw [hUc]; exact hk)
  rw [hUc] at hmain
  set S := (steinerSystems q r n).card with hSdef
  have hBu1 : 1 ≤ Bu := Nat.choose_pos (by omega)
  have hS1 : 1 ≤ S := by
    have h1 : 1 ≤ (cq * Bu) ^ k := Nat.one_le_pow _ _ (by positivity)
    have h2 := h1.trans hmain
    by_contra h
    push_neg at h
    interval_cases S
    simp at h2
  -- logarithms
  have hlogmain : (k : ℝ) * Real.log (cq * Bu : ℕ) - L * Real.log 2 ≤ Real.log S := by
    have h1 : ((cq * Bu : ℕ) : ℝ) ^ k ≤ (S : ℝ) * (2 : ℝ) ^ L := by exact_mod_cast hmain
    have hpos : (0 : ℝ) < ((cq * Bu : ℕ) : ℝ) := by exact_mod_cast (by positivity : 0 < cq * Bu)
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
    linarith
  set A := Real.log ((cq * Bu : ℕ) : ℝ) with hAdef
  -- lower bound on `B`
  have hx1 : (n : ℝ) / (2 * m) ≤ ((u - q + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have : ((n : ℕ) : ℝ) ≤ ((2 * m * (u - q + 1) : ℕ) : ℝ) := by exact_mod_cast hnu
    push_cast at this ⊢
    linarith
  have hBlo : (n : ℝ) / (2 * m * j.factorial) ≤ ((cq * Bu : ℕ) : ℝ) := by
    have hp := Nat.pow_le_choose (α := ℝ) j (u - r)
    rw [show u - r + 1 - j = u - q + 1 by omega] at hp
    have hxge : (1 : ℝ) ≤ ((u - q + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ u - q + 1)
    have hxj : ((u - q + 1 : ℕ) : ℝ) ≤ ((u - q + 1 : ℕ) : ℝ) ^ j := le_self_pow₀ hxge (by omega)
    have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have h1 : (n : ℝ) / (2 * m * j.factorial) ≤ (Bu : ℝ) := by
      rw [show (n : ℝ) / (2 * m * j.factorial) = (n : ℝ) / (2 * m) / j.factorial by
        field_simp]
      refine le_trans ?_ hp
      exact div_le_div_of_nonneg_right (hx1.trans hxj) hfac.le
    have h2 : (Bu : ℝ) ≤ ((cq * Bu : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left Bu (by omega)
    linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hnpos)
  have hA : Real.log n / 2 ≤ A := by
    have hK : (0 : ℝ) < 2 * m * j.factorial := by
      have : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
      positivity
    have h1 : Real.log ((n : ℝ) / (2 * m * j.factorial)) ≤ A :=
      Real.log_le_log (by positivity) hBlo
    rw [Real.log_div (by positivity) hK.ne'] at h1
    have h2 : 2 * Real.log (2 * m * j.factorial : ℝ) ≤ Real.log n := by
      rw [show (2 : ℝ) * Real.log (2 * m * j.factorial : ℝ) =
          Real.log ((2 * m * j.factorial : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
      refine Real.log_le_log (by positivity) ?_
      exact_mod_cast hn2
    linarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hA8 : 8 * (cq : ℝ) ^ 2 * Real.log 2 ≤ A := by linarith
  -- lower bound on `L`
  have hy1 : (1 : ℝ) ≤ (n : ℝ) / (2 * m) := by
    rw [le_div_iff₀ (by positivity)]
    have : ((2 * m : ℕ) : ℝ) ≤ n := by
      exact_mod_cast le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hn4
    push_cast at this
    linarith
  have hLlo : ((n : ℝ) / (2 * m)) ^ r / r.factorial ≤ L := by
    have hp := Nat.pow_le_choose (α := ℝ) r u
    refine le_trans ?_ hp
    refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ r) (by positivity)
    refine hx1.trans ?_
    exact_mod_cast (by omega : u - q + 1 ≤ u + 1 - r)
  clear_value A S k Bu L U u j cq
  have hL8 : 8 * (cq : ℝ) ^ 2 ≤ L := by
    have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    have h1 : (n : ℝ) / (2 * m) ≤ ((n : ℝ) / (2 * m)) ^ r := le_self_pow₀ hy1 (by omega)
    have h2 : 8 * (cq : ℝ) ^ 2 * r.factorial ≤ (n : ℝ) / (2 * m) := by
      rw [le_div_iff₀ (by positivity)]
      have : ((8 * cq ^ 2 * r.factorial * (2 * m) : ℕ) : ℝ) ≤ n := by exact_mod_cast hn4
      push_cast at this
      linarith
    have h3 : 8 * (cq : ℝ) ^ 2 ≤ ((n : ℝ) / (2 * m)) ^ r / r.factorial := by
      rw [le_div_iff₀ hfac]; linarith
    linarith
  have hklo : (L : ℝ) / (2 * (cq : ℝ) ^ 2) - 1 ≤ k := by
    have h1 := Nat.div_add_mod L (2 * cq ^ 2)
    have h2 := Nat.mod_lt L (show 0 < 2 * cq ^ 2 by positivity)
    rw [← hkdef] at h1
    have h3 : L < 2 * cq ^ 2 * (k + 1) := by rw [mul_add, mul_one]; linarith
    have h4 : (L : ℝ) < 2 * (cq : ℝ) ^ 2 * (k + 1) := by exact_mod_cast h3
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    linarith
  have hfin := final_estimate (X := Real.log S) (c := (cq : ℝ))
    (by exact_mod_cast hcq) hklo hA0 hlogmain hA8 hL8
  refine le_trans ?_ hfin
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hc0 : (0 : ℝ) < (cq : ℝ) ^ 2 := by
    have : (0 : ℝ) < cq := by exact_mod_cast hcq
    positivity
  calc 1 / ((2 * m : ℝ) ^ r * r.factorial * 8 * (cq : ℝ) ^ 2) * (n : ℝ) ^ r * Real.log n
      = (((n : ℝ) / (2 * m)) ^ r / r.factorial) * (Real.log n / 2) / (4 * (cq : ℝ) ^ 2) := by
        rw [div_pow]; field_simp; ring
    _ ≤ (L : ℝ) * A / (4 * (cq : ℝ) ^ 2) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hLlo hA (by positivity) (by positivity)

/-- **Lower bound.**  For `q > r ≥ 1` there are `c > 0` and `n₀` such that for every admissible
`n ≥ n₀`, `log #S(n, q, r) ≥ c · n^r · log n`; i.e. there are at least `n^{c n^r}`
`(n, q, r)`-Steiner systems. -/
theorem log_card_steinerSystems_ge {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      c * (n : ℝ) ^ r * Real.log n ≤ Real.log (steinerSystems q r n).card := by
  obtain ⟨ε, hε, n₀, hcomp⟩ := partialSteiner_completion (q := q) hr hrq
  set m : ℕ := ⌈1 / ε⌉₊ + 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hmε : (1 : ℝ) / m ≤ ε := by
    have h1 : 1 / ε ≤ (m : ℝ) := by
      have := Nat.le_ceil (1 / ε)
      rw [hmdef]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at h1
    linarith
  refine ⟨1 / ((2 * m : ℝ) ^ r * r.factorial * 8 * (q.choose r : ℝ) ^ 2), ?_, ?_⟩
  · have : 0 < (q.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hrq.le
    positivity
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev := (eventually_ge_atTop n₀).and ((eventually_ge_atTop (2 * m * q)).and
    ((eventually_ge_atTop ((2 * m * (q - r).factorial) ^ 2)).and
    ((hlog.eventually_ge_atTop (16 * (q.choose r : ℝ) ^ 2 * Real.log 2)).and
    (eventually_ge_atTop (8 * (q.choose r) ^ 2 * r.factorial * (2 * m))))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn hdiv => ?_⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := hN n hn
  exact lower_bound_at hr hrq (hcomp n h0 hdiv) hm hmε h1 h2 h3 h4

/-- **The number of Steiner systems is `n^{Θ(n^r)}`.** -/
theorem log_card_steinerSystems_theta {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      c * (n : ℝ) ^ r * Real.log n ≤ Real.log (steinerSystems q r n).card ∧
      Real.log (steinerSystems q r n).card ≤ (q + 1) * (n : ℝ) ^ r * Real.log n := by
  obtain ⟨c, hc, n₀, h⟩ := log_card_steinerSystems_ge hr hrq
  exact ⟨c, hc, max n₀ 2, fun n hn hdiv =>
    ⟨h n (le_of_max_le_left hn) hdiv, log_card_steinerSystems_le hrq.le (le_of_max_le_right hn)⟩⟩

end RefinedAbsorption.Extensions
