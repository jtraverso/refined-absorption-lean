module
public import RefinedAbsorption.Reserves

/-!
# Reserves for every `r`-set

The digit-sum reserve graph of `RequestProject/Reserves.lean` has many reserve cliques through
*every* `r`-set `e`, not only through the `r`-sets outside the reserve graph.  This stronger form
(`strongReservesLemma`) is needed for designs with `λ > 1`, where edges of the reserves also have
to be covered by the nibble.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-- **Strong reserves.**  For `q > r ≥ 1` and every `α > 0` there is `δ > 0` such that for all
large `n` there is `X ⊆ K_n^r` with `Δ_{r-1}(X) ≤ n^{1-δ}` such that every `r`-set `e` lies in at
least `n^{q-r-α}` copies of `K_q^r` in `X ∪ {e}` containing `e`. -/
def StrongReservesLemma : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ X ⊆ completeRGraph (Fin n) r, MaxDegLE r X ((n : ℝ) ^ (1 - δ)) ∧
      ∀ e ∈ completeRGraph (Fin n) r,
        (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card

/-- **Strong reserves lemma**, proved by the explicit digit-sum construction. -/
theorem strongReservesLemma : StrongReservesLemma := by
  intro q r hr hrq α hα
  set k := q - r with hk
  set M := (q - 1).choose (r - 1) with hM
  set t := M + ⌈2 * k * M / α⌉₊ + 1 with ht
  set a := t - M with ha
  have hMt : M < t := by omega
  have ht0 : (0 : ℝ) < t := by positivity
  have hkMt : (k * M : ℝ) / t ≤ α / 2 := by
    rw [div_le_iff₀ ht0]
    have h1 : 2 * k * M / α ≤ (⌈2 * k * M / α⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * k * M / α⌉₊ : ℝ) ≤ t := by
      rw [ht]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) M]
    have h3 : 2 * k * M ≤ t * α := by
      have := h1.trans h2
      rwa [div_le_iff₀ hα] at this
    linarith
  refine ⟨1 / (2 * t), by positivity, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n ∧ 2 * (2 * q + 1) ≤ (n : ℝ) ^ (1 / (t : ℝ)) ∧
      4 * t ≤ (n : ℝ) ^ (1 / (2 * t : ℝ)) ∧
      2 ^ ((a + 1) * k) * (k.factorial : ℝ) ≤ (n : ℝ) ^ (α / 2) :=
    (Filter.eventually_ge_atTop 1).and <| (ev_le_rpow _ (by positivity)).and <|
      (ev_le_rpow _ (by positivity)).and (ev_le_rpow _ (by positivity))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hn1, hx, hdeg, hcnt⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set y := (n : ℝ) ^ (1 / (2 * t : ℝ)) with hy
  set x := (n : ℝ) ^ (1 / (t : ℝ)) with hxdef
  have hxy : x = y ^ 2 := by
    rw [hxdef, hy, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; field_simp; norm_num
  have hxt : x ^ t = n := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, one_div_mul_cancel ht0.ne',
      Real.rpow_one]
  have hx0 : 0 ≤ x := by positivity
  set s := ⌊x⌋₊ with hsdef
  have hs_le : (s : ℝ) ≤ x := Nat.floor_le hx0
  have hs_ge : x / 2 ≤ s := by
    have := Nat.lt_floor_add_one x
    linarith
  have hs1 : 1 ≤ s := by
    have : (1 : ℝ) ≤ s := by linarith
    exact_mod_cast this
  have hst : s ^ t ≤ n := by
    have : (s : ℝ) ^ t ≤ n := hxt ▸ pow_le_pow_left₀ (Nat.cast_nonneg s) hs_le t
    exact_mod_cast this
  refine ⟨digitReserve n r t s, filter_subset _ _, ?_, ?_⟩
  · -- the degree bound
    intro S hS
    have h1 := deg_digitReserve_mul_le n r t s hs1 hst S hS
    have h1' : (deg (digitReserve n r t s) S : ℝ) * s ≤ 2 * t * n := by exact_mod_cast h1
    have hy0 : 0 < y := by positivity
    have hd0 : (0 : ℝ) ≤ deg (digitReserve n r t s) S := Nat.cast_nonneg _
    rw [Real.rpow_sub hn0, Real.rpow_one, ← hy, le_div_iff₀ hy0]
    have h2 : (deg (digitReserve n r t s) S : ℝ) * (y ^ 2 / 2) ≤ 2 * t * n := by
      rw [← hxy]; nlinarith
    have h3 : (deg (digitReserve n r t s) S : ℝ) * y * y ≤ n * y := by nlinarith
    nlinarith
  · -- the number of reserve cliques
    intro e he
    have hec : e.card = r := (mem_powersetCard.1 he).2
    have hqk : q = r + k := by omega
    have hcard := card_goodSets_ge n q r t s hr hs1 hst (hM ▸ hMt.le) e hec k (by omega)
    rw [← hqk, ← reserveCliques_eq_goodSets, ← hM, ← ha] at hcard
    have hLr : (s : ℝ) ^ a - q ≤ (s ^ a - q : ℕ) := by
      have : s ^ a ≤ (s ^ a - q) + q := by omega
      have : ((s ^ a : ℕ) : ℝ) ≤ ((s ^ a - q : ℕ) : ℝ) + q := by exact_mod_cast this
      push_cast at this; linarith
    have hx2 : 1 ≤ x / 2 := by linarith
    have hpa : x / 2 ≤ (x / 2) ^ a := le_self_pow₀ hx2 (by omega)
    have hsa : (x / 2) ^ a ≤ (s : ℝ) ^ a := pow_le_pow_left₀ (by positivity) hs_ge a
    have hz : x ^ a / 2 ^ (a + 1) = (x / 2) ^ a / 2 := by
      rw [div_pow, pow_succ]; field_simp
    exact reserve_count_real hrq hk ha hMt ht0 hkMt hn1 hxdef hx0 hcnt hcard
      (by rw [hz]; linarith)

end RefinedAbsorption
