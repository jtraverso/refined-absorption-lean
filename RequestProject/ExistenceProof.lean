module
public import RequestProject.Statements

/-!
# The refined absorption proof of the Existence Conjecture (Section 2)

We formalize the deduction of the Existence Conjecture (for Steiner systems, `λ = 1`) from the
four ingredients used in Section 2 of the paper:

1. **Reserves** (Lemma 2.1, `ReservesLemma`): a sparse random-like `r`-graph `X ⊆ K_n^r`;
2. **Refined efficient omni-absorber** (Theorem 1.10, `RefinedEfficientOmniAbsorber`) for `X`;
3. **Boost** (Lemma 2.2, `BoostLemma`) applied to `J = K_n^r \ (A ∪ X)`;
4. **Nibble with reserves** (Corollary 2.4) applied to `J` with reserves `X`;

followed by the absorption step (`absorption_step`).

All the combinatorial and asymptotic bookkeeping (degree estimates, choice of the parameters
`p = n^{-δ}`, comparison of the normalisations, divisibility of `K_n^r`) is proved here.

**On the statement of Corollary 2.4.**  As stated in the survey, Lemma 2.2 controls the clique
degrees relative to `binom(n-r, q-r)` with error `n^{-1/3}`, while Corollary 2.4 requires them
relative to `binom(n, q-r)` with the *same* error `n^{-1/3}`; this does not follow literally.
We therefore use the version `NibbleWithReservesGen` of Corollary 2.4 with an arbitrary
polynomial error `n^{-β}` (as in the nibble, Theorem 1.3); the survey's statement is its special
case `β = 1/3` (`NibbleWithReservesGen.nibbleWithReserves`).  We use it with `β = 1/4`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-! ### The statements -/

/-- **Corollary 2.4 (Nibble with reserves), with general polynomial error.**  For `q > r ≥ 1`,
`ρ ∈ (0,1]` and `β ∈ (0,1)` there is `α ∈ (0,1)` such that for all large `n`: let `G ⊆ K_n^r`
and `H ⊆ K_q^r(G)` be such that every edge of `G` is in `(ρ ± n^{-β}) binom(n, q-r)` cliques
of `H`.  If `X ⊆ K_n^r \ G` is such that every `e ∈ G` is in at least `n^{q-r-α}` copies of
`K_q^r` in `X ∪ {e}`, then there is a `K_q^r`-packing of `G ∪ X` covering all edges of `G`. -/
def NibbleWithReservesGen : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ β : ℝ, 0 < β → β < 1 →
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G ⊆ completeRGraph (Fin n) r, ∀ H ⊆ cliquesOf q r G,
      (∀ e ∈ G, |(cliqueMult H e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-β) * (n.choose (q - r))) →
      ∀ X ⊆ completeRGraph (Fin n) r \ G,
        (∀ e ∈ G, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card) →
          ∃ P, IsPacking q r (G ∪ X) P ∧ G ⊆ coveredEdges r P

/-- **Weak reserves.**  For `q > r ≥ 1` and every `α > 0` there is `δ > 0` such that for all
large `n` there is `X ⊆ K_n^r` with `Δ_{r-1}(X) ≤ n^{1-δ}` such that every edge `e ∉ X` lies in
at least `n^{q-r-α}` copies of `K_q^r` in `X ∪ {e}`.  This is all that the proof of the
Existence Conjecture uses from Lemma 2.1 (see `ReservesLemma.weak`). -/
def WeakReservesLemma : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ X ⊆ completeRGraph (Fin n) r, MaxDegLE r X ((n : ℝ) ^ (1 - δ)) ∧
      ∀ e ∈ completeRGraph (Fin n) r \ X,
        (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card

/-- The survey's Corollary 2.4 is the case `β = 1/3` of `NibbleWithReservesGen`. -/
theorem NibbleWithReservesGen.nibbleWithReserves (h : NibbleWithReservesGen) :
    NibbleWithReserves := fun q r hr hrq ρ hρ hρ1 =>
  h q r hr hrq ρ hρ hρ1 (1 / 3) (by norm_num) (by norm_num)

/-- **The Existence Conjecture for Steiner systems** (`λ = 1`): for `q > r ≥ 2` and `n` large
enough satisfying the divisibility conditions, an `(n, q, r)`-Steiner system exists. -/
def SteinerExistenceConjecture : Prop :=
  ∀ q r : ℕ, 2 ≤ r → r < q → ∃ n₀, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
    ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮

/-- The Existence Conjecture contains its Steiner system case. -/
theorem ExistenceConjecture.steiner (h : ExistenceConjecture) : SteinerExistenceConjecture :=
  fun q r hr hrq => h q r 1 hr hrq le_rfl

/-! ### Divisibility of `K_n^r` -/

theorem deg_completeRGraph {n r : ℕ} {S : Finset (Fin n)} (hS : S.card ≤ r) :
    deg (completeRGraph (Fin n) r) S = (n - S.card).choose (r - S.card) := by
  rw [deg, completeRGraph, card_powersetCard_filter_superset (subset_univ _) hS, card_univ,
    Fintype.card_fin]

/-- `K_n^r` is `K_q^r`-divisible iff the design divisibility conditions with `λ = 1` hold. -/
theorem isDivisible_completeRGraph_iff {n q r : ℕ} :
    IsDivisible q r (completeRGraph (Fin n) r) ↔ DesignDivisibility n q r 1 := by
  constructor
  · intro h i hi
    rw [one_mul]
    by_cases hin : i ≤ n
    · obtain ⟨S, -, hS⟩ :=
        exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hin)
      have := h S (by omega)
      rwa [deg_completeRGraph (by omega), hS] at this
    · rw [show n - i = 0 by omega, Nat.choose_eq_zero_of_lt (show 0 < r - i by omega)]
      exact dvd_zero _
  · intro h S hS
    rw [deg_completeRGraph hS.le]
    simpa using h S.card hS

/-! ### Elementary estimates -/

/-- `n · (binom(n,k) - binom(n-r,k)) ≤ r · k · binom(n,k)`. -/
theorem choose_sub_choose_le (n r k : ℕ) :
    n * (n.choose k - (n - r).choose k) ≤ r * k * n.choose k := by
  induction r with
  | zero => simp
  | succ j ih =>
    rcases k with _ | k
    · simp
    rcases Nat.lt_or_ge j n with hj | hj
    · have hpas : (n - j).choose (k + 1) =
          (n - (j + 1)).choose (k + 1) + (n - (j + 1)).choose k := by
        rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.choose_succ_succ', add_comm]
      have hmono : (n - (j + 1)).choose k ≤ (n - 1).choose k :=
        Nat.choose_le_choose _ (by omega)
      have hkey : n * (n - 1).choose k = (k + 1) * n.choose (k + 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [Nat.add_one_mul_choose_eq]; ring
      have hle : (n - j).choose (k + 1) ≤ n.choose (k + 1) := Nat.choose_le_choose _ (by omega)
      have h1 : n.choose (k + 1) - (n - (j + 1)).choose (k + 1) ≤
          (n.choose (k + 1) - (n - j).choose (k + 1)) + (n - 1).choose k := by omega
      calc n * (n.choose (k + 1) - (n - (j + 1)).choose (k + 1))
          ≤ n * ((n.choose (k + 1) - (n - j).choose (k + 1)) + (n - 1).choose k) :=
            Nat.mul_le_mul_left _ h1
        _ = n * (n.choose (k + 1) - (n - j).choose (k + 1)) + n * (n - 1).choose k := by ring
        _ ≤ j * (k + 1) * n.choose (k + 1) + (k + 1) * n.choose (k + 1) := by
            rw [hkey]; exact Nat.add_le_add_right ih _
        _ = (j + 1) * (k + 1) * n.choose (k + 1) := by ring
    · rw [show n - (j + 1) = 0 by omega]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      rw [Nat.choose_zero_succ, Nat.sub_zero]
      calc n * n.choose (k + 1) ≤ (j + 1) * n.choose (k + 1) :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ (j + 1) * (k + 1) * n.choose (k + 1) := Nat.mul_le_mul_right _ (by nlinarith)

theorem ev_rpow_neg_le {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-s) ≤ c :=
  ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds hc)

theorem ev_le_rpow {s : ℝ} (c : ℝ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in Filter.atTop, c ≤ (n : ℝ) ^ s :=
  ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop c)

theorem ev_log_div_rpow_le {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log n / (n : ℝ) ^ s ≤ c :=
  (((isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds hc)

/-- `n^{1-δ} ≤ n / C` for large `n` (the hypothesis `D ≤ n / C` of Theorem 1.10). -/
theorem ev_degree_le_div (C : ℕ) (hC : 1 ≤ C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (1 - δ) ≤ n / C := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  filter_upwards [Filter.eventually_ge_atTop 1,
    ev_rpow_neg_le hδ (show 0 < 1 / (C : ℝ) by positivity)] with n hn1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [le_div_iff₀ hC', sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
  have : (n : ℝ) ^ (-δ) * C ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hn; linarith
  nlinarith

/-- With `p = n^{-δ}`: `2pn ≤ n^{1-δ/2}` for large `n`. -/
theorem ev_two_p_n_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, 2 * (n : ℝ) ^ (-δ) * n ≤ (n : ℝ) ^ (1 - δ / 2) := by
  filter_upwards [Filter.eventually_ge_atTop 1, ev_le_rpow 2 (show 0 < δ / 2 by positivity)]
    with n hn1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e : (n : ℝ) ^ (1 - δ / 2) = (n : ℝ) ^ (δ / 2) * ((n : ℝ) ^ (-δ) * n) := by
    rw [← Real.rpow_add_one hn0.ne', ← Real.rpow_add hn0]; ring_nf
  rw [e]
  have : 0 ≤ (n : ℝ) ^ (-δ) * n := by positivity
  nlinarith

/-- The degrees of the reserves (at most `n^{1-δ}`) and of the omni-absorber are `o(n)`. -/
theorem ev_absorber_degree_small (r C : ℕ) (hr : 2 ≤ r) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, (r : ℝ) + (n : ℝ) ^ (1 - δ)
        + C * max ((n : ℝ) ^ (1 - δ)) ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n)
        ≤ ε * n := by
  have hr' : (0 : ℝ) < 1 / (r : ℝ) := by positivity
  filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop ⌈3 * r / ε⌉₊,
    ev_rpow_neg_le hδ (show 0 < ε / (3 * (1 + C)) by positivity),
    ev_log_div_rpow_le hr' (show 0 < ε / (3 * (C + 1)) by positivity)] with n hn1 hn2 hn3 hn4
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : (r : ℝ) ≤ ε / 3 * n := by
    have := Nat.le_of_ceil_le hn2
    rw [div_le_iff₀ hε] at this
    linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  set t := Real.log n / (n : ℝ) ^ (1 / (r : ℝ)) with ht
  have hpow : (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n = n * t := by
    rw [ht, Real.rpow_sub hn0, Real.rpow_one]; field_simp
  have hpow' : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
    rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one, mul_comm]
  have hp0 : 0 ≤ (n : ℝ) ^ (-δ) := by positivity
  have hq0 : 0 ≤ t := by positivity
  rw [hpow, hpow']
  have hmax : max ((n : ℝ) ^ (-δ) * n) (n * t) ≤ (n : ℝ) ^ (-δ) * n + n * t :=
    max_le (by nlinarith) (by nlinarith)
  have hC : (0 : ℝ) ≤ C := by positivity
  have e1 : (1 + C) * ((n : ℝ) ^ (-δ) * n) ≤ ε / 3 * n := by
    have := mul_le_mul_of_nonneg_right hn3 hn0.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  have e2' : (C : ℝ) * t ≤ ε / 3 := by
    calc (C : ℝ) * t ≤ (C + 1) * t := by nlinarith
      _ ≤ (C + 1) * (ε / (3 * (C + 1))) := mul_le_mul_of_nonneg_left hn4 (by positivity)
      _ = ε / 3 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hmax hC, mul_le_mul_of_nonneg_left e2' hn0.le]

/-- With `p = n^{-δ}` and `δ (binom(q,r) - 1) ≤ α/2`, the number of reserve cliques
`½ p^{binom(q,r)-1} binom(n, q-r)` guaranteed by Lemma 2.1 is at least `n^{q-r-α}`. -/
theorem ev_reserve_cliques_large (q r : ℕ) (hrq : r < q) (α δ : ℝ) (hα : 0 < α)
    (hδα : δ * ((q.choose r : ℝ) - 1) ≤ α / 2) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ ((q : ℝ) - r - α)
        ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ (-δ)) ^ (q.choose r - 1) * (n.choose (q - r)) := by
  set k := q - r with hk
  have hkq : (q : ℝ) - r = k := by rw [hk, Nat.cast_sub hrq.le]
  have hm : 1 ≤ q.choose r := Nat.choose_pos hrq.le
  filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop (2 * k),
    ev_le_rpow (2 ^ (k + 1) * (k.factorial : ℝ)) (show 0 < α / 2 by positivity)]
    with n hn1 hn2 hn3
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  set a := (n : ℝ) ^ (-(δ * ((q.choose r : ℝ) - 1))) with ha
  have hapow : ((n : ℝ) ^ (-δ)) ^ (q.choose r - 1) = a := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, Nat.cast_sub hm]; ring_nf
  have hx : (n : ℝ) ^ (-α) ≤ a * (n : ℝ) ^ (-(α / 2)) := by
    rw [ha, ← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hb : (n : ℝ) ^ (-(α / 2)) * (n : ℝ) ^ (α / 2) = 1 := by
    rw [← Real.rpow_add hn0]; simp
  have hF : (0 : ℝ) < 2 ^ (k + 1) * (k.factorial : ℝ) := by positivity
  have hxF : (n : ℝ) ^ (-α) * (2 ^ (k + 1) * (k.factorial : ℝ)) ≤ a := by
    calc (n : ℝ) ^ (-α) * (2 ^ (k + 1) * (k.factorial : ℝ))
        ≤ a * (n : ℝ) ^ (-(α / 2)) * (n : ℝ) ^ (α / 2) :=
          mul_le_mul hx hn3 hF.le (by positivity)
      _ = a := by rw [mul_assoc, hb, mul_one]
  have hB : ((n : ℝ) / 2) ^ k / k.factorial ≤ (n.choose k : ℝ) := by
    refine le_trans ?_ (Nat.pow_le_choose k n)
    gcongr
    rw [Nat.cast_sub (by omega)]; push_cast
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  rw [hapow, hkq, Real.rpow_sub hn0, Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  calc (n : ℝ) ^ k * (n : ℝ) ^ (-α)
      ≤ (n : ℝ) ^ k * (a / (2 ^ (k + 1) * (k.factorial : ℝ))) := by
        gcongr
        rw [le_div_iff₀ hF]; exact hxF
    _ = 1 / 2 * a * (((n : ℝ) / 2) ^ k / k.factorial) := by
        rw [div_pow]; field_simp; ring
    _ ≤ 1 / 2 * a * (n.choose k : ℝ) := by gcongr

/-- `n^{-1/3} + c/(2n) ≤ n^{-1/4}` for large `n`. -/
theorem ev_error_conversion (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (-(1 / 3 : ℝ)) + c / (2 * n) ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    ev_rpow_neg_le (show (0 : ℝ) < 1 / 12 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num),
    ev_rpow_neg_le (show (0 : ℝ) < 3 / 4 by norm_num) (show (0 : ℝ) < 1 / (|c| + 1) by positivity)]
    with n hn1 h1 h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e1 : (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 12 : ℝ)) := by
    rw [← Real.rpow_add hn0]; norm_num
  have e2 : c / (2 * n) =
      (1 / 2) * c * (n : ℝ) ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [mul_assoc _ ((n : ℝ) ^ (-(3 / 4 : ℝ))), ← Real.rpow_add hn0]; norm_num
    rw [Real.rpow_neg_one]; field_simp
  have h2' : c * (n : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 := by
    have hp : 0 ≤ (n : ℝ) ^ (-(3 / 4 : ℝ)) := by positivity
    calc c * (n : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (|c| + 1) * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
          nlinarith [le_abs_self c]
      _ ≤ (|c| + 1) * (1 / (|c| + 1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := by field_simp
  have hq : 0 ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hq, mul_le_mul_of_nonneg_right h2' hq]

/-- The parameter estimates needed in the proof, valid for all large `n`. -/
theorem eventually_parameter_bounds (q r C : ℕ) (hr : 2 ≤ r) (hC : 1 ≤ C)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, 1 < n ∧
      (n : ℝ) ^ (1 - δ) ≤ n / C ∧
      (r : ℝ) + (n : ℝ) ^ (1 - δ)
        + C * max ((n : ℝ) ^ (1 - δ)) ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n)
        ≤ ε * n ∧
      (n : ℝ) ^ (-(1 / 3 : ℝ)) + ((r * (q - r) : ℕ) : ℝ) / (2 * n)
        ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
  (Filter.eventually_gt_atTop 1).and <| (ev_degree_le_div C hC δ hδ).and <|
    (ev_absorber_degree_small r C hr ε δ hε hδ).and (ev_error_conversion _)

/-- Converting the clique degrees given by the boost lemma (normalised by `binom(n-r, k)`, error
`n^{-1/3}`) to the normalisation `binom(n, k)` (error `n^{-1/4}`). -/
theorem clique_deg_conversion {n r k : ℕ} {x : ℝ} (hn : 0 < n)
    (h : |x - (1 / 2) * ((n - r).choose k)| ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n - r).choose k))
    (hconv : (n : ℝ) ^ (-(1 / 3 : ℝ)) + ((r * k : ℕ) : ℝ) / (2 * n) ≤ (n : ℝ) ^ (-(1 / 4 : ℝ))) :
    |x - (1 / 2) * (n.choose k)| ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n.choose k) := by
  have hle : (n - r).choose k ≤ n.choose k := Nat.choose_le_choose _ (by omega)
  have hkey' : (n : ℝ) * ((n.choose k : ℝ) - (n - r).choose k) ≤ (r * k : ℕ) * n.choose k := by
    rw [← Nat.cast_sub hle]; exact_mod_cast choose_sub_choose_le n r k
  have hle' : ((n - r).choose k : ℝ) ≤ n.choose k := by exact_mod_cast hle
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  have h2 : ((n.choose k : ℝ) - (n - r).choose k) ≤ ((r * k : ℕ) : ℝ) / n * n.choose k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hn']; linarith
  have h3 : |x - (1 / 2) * (n.choose k)| ≤
      |x - (1 / 2) * ((n - r).choose k)| + (1 / 2) * ((n.choose k : ℝ) - (n - r).choose k) := by
    have := abs_sub_le x ((1 / 2) * ((n - r).choose k : ℝ)) ((1 / 2) * (n.choose k))
    rw [abs_of_nonpos (a := (1 / 2) * ((n - r).choose k : ℝ) - (1 / 2) * (n.choose k))
      (by linarith)] at this
    linarith
  calc |x - (1 / 2) * (n.choose k)| ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) * n.choose k +
        ((r * k : ℕ) : ℝ) / (2 * n) * n.choose k := by
        have : ((r * k : ℕ) : ℝ) / (2 * n) = (1 / 2) * (((r * k : ℕ) : ℝ) / n) := by
          field_simp
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left hle' hpos]
    _ = ((n : ℝ) ^ (-(1 / 3 : ℝ)) + ((r * k : ℕ) : ℝ) / (2 * n)) * n.choose k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconv (by positivity)

/-! ### The proof -/

/-- **Lemma 2.1 implies the weak reserves lemma** (take `p = n^{-δ}` with `δ` small in terms of
`α` and `γ`). -/
theorem ReservesLemma.weak (h : ReservesLemma) : WeakReservesLemma := by
  intro q r hr hrq α hα
  obtain ⟨γ, hγ, -, n₁, hRes'⟩ := h q r hr hrq
  have hm : (1 : ℝ) ≤ (q.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hrq.le
  set δ : ℝ := min γ (α / (2 * (q.choose r : ℝ))) with hδdef
  have hδ : 0 < δ := lt_min hγ (by positivity)
  have hδα : δ * ((q.choose r : ℝ) - 1) ≤ α / 2 := by
    calc δ * ((q.choose r : ℝ) - 1) ≤ α / (2 * (q.choose r : ℝ)) * (q.choose r : ℝ) := by
          apply mul_le_mul (min_le_right _ _) (by linarith) (by linarith) (by positivity)
      _ = α / 2 := by field_simp
  refine ⟨δ / 2, by positivity, ?_⟩
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1 ((Filter.eventually_gt_atTop 1).and <|
    (ev_two_p_n_le δ hδ).and (ev_reserve_cliques_large q r hrq α δ hα hδα))
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  obtain ⟨hn1, h2pn, hres⟩ := hn₂ n (by omega)
  have hn0 : (1 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨X, hXK, hXdeg, hXres⟩ := hRes' n (by omega) ((n : ℝ) ^ (-δ))
    (Real.rpow_le_rpow_of_exponent_le hn0.le (neg_le_neg (min_le_left _ _)))
    (Real.rpow_lt_one_of_one_lt_of_neg hn0 (by linarith))
  exact ⟨X, hXK, fun S hS => (hXdeg S hS).trans h2pn, fun e he => hres.trans (hXres e he)⟩

/-- **The Existence Conjecture via refined absorption** (Section 2), from the weak form of the
reserves lemma.  Reserves (`WeakReservesLemma`), the refined efficient omni-absorber theorem,
the boost lemma and the nibble with reserves together imply the existence of
`(n, q, r)`-Steiner systems for all large `n` satisfying the divisibility conditions. -/
theorem steinerExistence_of_weakReserves (hRes : WeakReservesLemma)
    (hOmni : RefinedEfficientOmniAbsorber) (hBoost : BoostLemma)
    (hNib : NibbleWithReservesGen) : SteinerExistenceConjecture := by
  intro q r hr hrq
  have hr1 : 1 ≤ r := by omega
  obtain ⟨C, hC1, hOmni'⟩ := hOmni q r hr1 hrq
  obtain ⟨ε, hε, -, n₂, hBoost'⟩ := hBoost q r hr1 hrq
  obtain ⟨α, hα, -, n₃, hNib'⟩ :=
    hNib q r hr1 hrq (1 / 2) (by norm_num) (by norm_num) (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨δ, hδ, n₁, hRes'⟩ := hRes q r hr1 hrq α hα
  obtain ⟨n₄, hn₄⟩ := Filter.eventually_atTop.1
    (eventually_parameter_bounds q r C hr hC1 ε δ hε hδ)
  refine ⟨max (max n₁ n₂) (max n₃ n₄), fun n hn hdiv => ?_⟩
  obtain ⟨hn1, hD, hdeg, hconv⟩ := hn₄ n (by omega)
  set K := completeRGraph (Fin n) r with hKdef
  -- Step 1: reserves
  obtain ⟨X, hXK, hXdeg, hXres⟩ := hRes' n (by omega)
  have hXr : IsRGraph r X := fun e he => (mem_powersetCard.1 (hXK he)).2
  -- Step 2: refined efficient omni-absorber for the reserves
  obtain ⟨A, F, QA, hA, -, hAdeg⟩ := hOmni' n X ((n : ℝ) ^ (1 - δ)) hXr hXdeg hD
  have hAr : IsRGraph r A := hA.isDecomposition_self.rgraph
  have hAK : A ⊆ K := fun e he => mem_powersetCard.2 ⟨subset_univ _, hAr e he⟩
  -- Step 3: boost on the rest
  set J := K \ (A ∪ X) with hJdef
  have hJK : J ⊆ K := sdiff_subset
  have hJdeg : MinDegGE r J ((1 - ε) * n) := by
    intro S hS
    have h1 : deg K S ≤ deg J S + deg A S + deg X S := by
      unfold deg
      calc (K.filter (fun e => S ⊆ e)).card
          ≤ ((J.filter (fun e => S ⊆ e)) ∪ (A.filter (fun e => S ⊆ e)) ∪
              (X.filter (fun e => S ⊆ e))).card := by
            apply card_le_card
            intro e he
            rw [mem_filter] at he
            by_cases heA : e ∈ A
            · simp [heA, he.2]
            · by_cases heX : e ∈ X
              · simp [heX, he.2]
              · simp [hJdef, he.1, he.2, heA, heX]
        _ ≤ _ := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have h2 : deg K S = n - (r - 1) := by
      rw [hKdef, deg_completeRGraph (by omega), show r - S.card = 1 by omega,
        Nat.choose_one_right, show S.card = r - 1 by omega]
    have h3 : n ≤ (n - (r - 1)) + r := by omega
    have h3' : (n : ℝ) ≤ ((n - (r - 1) : ℕ) : ℝ) + r := by exact_mod_cast h3
    have h1' : ((deg K S : ℕ) : ℝ) ≤ deg J S + deg A S + deg X S := by exact_mod_cast h1
    rw [h2] at h1'
    have hAd := hAdeg S hS
    have hXd := hXdeg S hS
    nlinarith
  obtain ⟨H, hHJ, hHreg⟩ := hBoost' n (by omega) J hJK hJdeg
  -- Step 4: nibble with reserves
  have hXJ : X ⊆ K \ J := by
    intro e he
    rw [mem_sdiff]
    exact ⟨hXK he, fun h => (mem_sdiff.1 h).2 (mem_union_right _ he)⟩
  have hreg : ∀ e ∈ J, |(cliqueMult H e : ℝ) - (1 / 2) * (n.choose (q - r))|
      ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n.choose (q - r)) :=
    fun e he => clique_deg_conversion (by omega) (hHreg e he) hconv
  have hresJ : ∀ e ∈ J, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card := by
    intro e he
    have heX : e ∈ K \ X := by
      rw [mem_sdiff]
      exact ⟨hJK he, fun h => (mem_sdiff.1 he).2 (mem_union_right _ h)⟩
    exact hXres e heX
  obtain ⟨P, hP, hcov⟩ := hNib' n (by omega) J hJK H hHJ hreg X hXJ hresJ
  -- Step 5: absorb the leftover
  have hJX : J ∪ X = K \ A := by
    ext e
    simp only [hJdef, mem_union, mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h1, fun h => h2 (Or.inl h)⟩
      · exact ⟨hXK h, fun h' => disjoint_left.1 hA.disjoint h h'⟩
    · rintro ⟨h1, h2⟩
      by_cases hX : e ∈ X
      · exact Or.inr hX
      · exact Or.inl ⟨h1, by tauto⟩
  have hKdiv : IsDivisible q r K := isDivisible_completeRGraph_iff.2 hdiv
  rw [hJX] at hP
  obtain ⟨𝒬, h𝒬⟩ := absorption_step hrq.le hKdiv hAK hA hP hcov
  exact ⟨𝒬, isSteinerSystem_iff_isDecomposition.2 (by simpa using h𝒬)⟩

/-- **The Existence Conjecture via refined absorption** (Section 2), exactly as in the paper:
the reserves lemma (Lemma 2.1), the refined efficient omni-absorber theorem (Theorem 1.10), the
boost lemma (Lemma 2.2) and the nibble with reserves (Corollary 2.4, with general polynomial
error) imply the existence of `(n, q, r)`-Steiner systems for all large `n` satisfying the
divisibility conditions. -/
theorem steinerExistence_of_refinedAbsorption (hRes : ReservesLemma)
    (hOmni : RefinedEfficientOmniAbsorber) (hBoost : BoostLemma)
    (hNib : NibbleWithReservesGen) : SteinerExistenceConjecture :=
  steinerExistence_of_weakReserves hRes.weak hOmni hBoost hNib

end RefinedAbsorption
