module
public import RefinedAbsorption.Dense.Native
public import RefinedAbsorption.Nibble.Bridge
public import RefinedAbsorption.Reserves
public import RefinedAbsorption.Boost

/-!
# Steiner systems from strong multi-refiners with an `o(n)` budget

The proof of the Existence Conjecture in Section 2 only uses that the omni-absorber of the
reserves has `(r-1)`-degrees at most `ε n` (where `ε` comes from the boost lemma); its
refinedness and the precise budget `C · max(D, n^{1-1/r} log n)` of Theorem 1.10 are not used.

* `WeakOmniAbsorberFor q r`: for `δ, ε > 0` and all large `n`, every `X ⊆ K_n^r` with
  `Δ_{r-1}(X) ≤ n^{1-δ}` has a `K_q^r`-omni-absorber `A` with `Δ_{r-1}(A) ≤ ε n`.
* `weakOmniAbsorberFor_of_native`: it follows from `NativeWeakStrongMultiRefiners q r` (with the
  placement of fake edges and absorbers already proved in `Placement/Assembly.lean`).
* `steinerExistenceFor_of_weakOmni`: the Section 2 argument for fixed `q, r`.
* **`steinerExistenceFor_two`**: for every `q ≥ 3` and all large `n` with the divisibility
  conditions, an `(n, q, 2)`-Steiner system exists.  No hypotheses.
* **`steinerExistence_of_nativeWeak`**: the Existence Conjecture for Steiner systems, from
  `NativeWeakStrongMultiRefiners q r` for `r ≥ 3` only.
-/

@[expose] public section

namespace RefinedAbsorption.Dense

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

/-- **Omni-absorbers with `o(n)` degrees** for fixed `q, r`. -/
def WeakOmniAbsorberFor (q r : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)),
    IsRGraph r X → MaxDegLE r X ((n : ℝ) ^ (1 - δ)) →
      ∃ A F : Finset (Finset (Fin n)), ∃ QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n)),
        IsOmniAbsorber q r X A F QA ∧ MaxDegLE r A (ε * n)

/-- **Steiner systems for fixed `q, r`**: for all large `n` satisfying the divisibility
conditions, an `(n, q, r)`-Steiner system exists. -/
def SteinerExistenceFor (q r : ℕ) : Prop :=
  ∃ n₀, ∀ n ≥ n₀, DesignDivisibility n q r 1 → ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮

theorem steinerExistence_iff_forall :
    SteinerExistenceConjecture ↔ ∀ q r : ℕ, 2 ≤ r → r < q → SteinerExistenceFor q r :=
  Iff.rfl

/-- `K · (n^{1-δ} + 1) ≤ c · n` for large `n`. -/
theorem ev_mul_rpow_add_one_le (K : ℝ) (hK : 0 ≤ K) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, K * ((n : ℝ) ^ (1 - δ) + 1) ≤ c * n := by
  filter_upwards [Filter.eventually_ge_atTop ⌈2 * K / c⌉₊, Filter.eventually_ge_atTop 1,
    ev_rpow_neg_le hδ (show 0 < c / (2 * (K + 1)) by positivity)] with n hn hn1 hrp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
    rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one, mul_comm]
  have h1 : K * ((n : ℝ) ^ (-δ) * n) ≤ c / 2 * n := by
    have : K * (n : ℝ) ^ (-δ) ≤ c / 2 := by
      calc K * (n : ℝ) ^ (-δ) ≤ (K + 1) * (n : ℝ) ^ (-δ) := by
            nlinarith [Real.rpow_nonneg hn0.le (-δ)]
        _ ≤ (K + 1) * (c / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hrp (by positivity)
        _ = c / 2 := by field_simp
    nlinarith
  have h2 : K ≤ c / 2 * n := by
    have := Nat.le_of_ceil_le hn
    rw [div_le_iff₀ hc] at this
    nlinarith
  rw [hpow]; nlinarith

set_option maxHeartbeats 1000000 in
/-- **Omni-absorbers with `o(n)` degrees from strong multi-refiners with `o(n)` budget.** -/
theorem weakOmniAbsorberFor_of_native {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hnat : NativeWeakStrongMultiRefiners q r) : WeakOmniAbsorberFor q r := by
  intro δ hδ ε hε
  obtain ⟨C, B, hC, hN⟩ := hnat
  obtain ⟨Cf, hCf, hasm⟩ := refinerAbsorbers_of_strongMultiRefiner hr hrq C hC
  set c : ℝ := min ε 1 with hcdef
  have hc0 : 0 < c := lt_min hε one_pos
  set t : ℕ := ⌈2 * (Cf * B : ℝ) / c⌉₊ with ht
  obtain ⟨Ct, n₀, hN'⟩ := hN t
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    (ev_mul_rpow_add_one_le ((Cf : ℝ) * Ct) (by positivity) (half_pos hc0) hδ)
  refine ⟨max (max n₀ n₁) 1, fun n hn X hX hXD => ?_⟩
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  set D : ℕ := ⌊(n : ℝ) ^ (1 - δ)⌋₊ + 1 with hD
  have hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ D := by
    intro S hS
    have h := hXD S (by omega)
    have : deg X S ≤ ⌊(n : ℝ) ^ (1 - δ)⌋₊ := Nat.le_floor h
    omega
  obtain ⟨E, _, ends, K, Xl, R, 𝒲, Bd, hXl, hBd, hS⟩ := hN' n hn0 X D hX (by omega) hdeg
  -- the budget in real numbers
  have hDR : (D : ℝ) ≤ (n : ℝ) ^ (1 - δ) + 1 := by
    rw [hD]; push_cast
    have := Nat.floor_le (Real.rpow_nonneg hnR.le (1 - δ))
    linarith
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have htc : 2 * (Cf * B : ℝ) / c ≤ 2 ^ t := by
    calc 2 * (Cf * B : ℝ) / c ≤ t := Nat.le_ceil _
      _ ≤ 2 ^ t := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hBdR : (Bd : ℝ) ≤ Ct * D + B * n / 2 ^ t := by
    have : ((2 ^ t * Bd : ℕ) : ℝ) ≤ ((2 ^ t * Ct * D + B * n : ℕ) : ℝ) := by exact_mod_cast hBd
    push_cast at this
    have e : (2 : ℝ) ^ t * (B * n / 2 ^ t) = B * n := by field_simp
    have h' : (2 : ℝ) ^ t * Bd ≤ 2 ^ t * (Ct * D + B * n / 2 ^ t) := by
      rw [mul_add, e]; nlinarith
    exact le_of_mul_le_mul_left h' h2t
  have hfirst : (Cf : ℝ) * (Ct * D) ≤ c / 2 * n := by
    have := hn₁ n hn1
    calc (Cf : ℝ) * (Ct * D) = (Cf * Ct) * D := by ring
      _ ≤ (Cf * Ct) * ((n : ℝ) ^ (1 - δ) + 1) :=
          mul_le_mul_of_nonneg_left hDR (by positivity)
      _ ≤ c / 2 * n := this
  have hsecond : (Cf : ℝ) * (B * n / 2 ^ t) ≤ c / 2 * n := by
    rw [mul_div_assoc', div_le_iff₀ h2t]
    have h1 : 2 * (Cf * B : ℝ) ≤ c * 2 ^ t := by
      rw [div_le_iff₀ hc0] at htc; linarith
    nlinarith
  have hCfBd : (Cf : ℝ) * Bd ≤ c * n := by
    calc (Cf : ℝ) * Bd ≤ Cf * (Ct * D + B * n / 2 ^ t) :=
          mul_le_mul_of_nonneg_left hBdR (by positivity)
      _ = Cf * (Ct * D) + Cf * (B * n / 2 ^ t) := by ring
      _ ≤ c / 2 * n + c / 2 * n := add_le_add hfirst hsecond
      _ = c * n := by ring
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcε : c ≤ ε := min_le_left _ _
  have hCfBdn : Cf * Bd ≤ n := by
    have : (Cf : ℝ) * Bd ≤ n := hCfBd.trans (by nlinarith)
    exact_mod_cast this
  obtain ⟨R', 𝒲', A, Qon, Qoff, hR', hA, hdegA⟩ := hasm n ends K Xl R 𝒲 Bd hS hCfBdn hnpos
  rw [hXl] at hR' hA
  obtain ⟨QA, hQA, -⟩ := omniAbsorber_of_refiner_absorbers hrq.le hCf hR' hA
  refine ⟨_, _, QA, hQA, fun S hS' => ?_⟩
  have h := hdegA S (by omega)
  calc (deg (R' ∪ 𝒲'.sup A) S : ℝ) ≤ ((Cf * Bd : ℕ) : ℝ) := by exact_mod_cast h
    _ = Cf * Bd := by push_cast; ring
    _ ≤ c * n := hCfBd
    _ ≤ ε * n := by nlinarith

set_option maxHeartbeats 1000000 in
/-- **The Section 2 argument for fixed `q, r`**, from omni-absorbers with `o(n)` degrees. -/
theorem steinerExistenceFor_of_weakOmni {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hRes : WeakReservesLemma) (hOmni : WeakOmniAbsorberFor q r) (hBoost : BoostLemma)
    (hNib : NibbleWithReservesGen) : SteinerExistenceFor q r := by
  have hr1 : 1 ≤ r := by omega
  obtain ⟨ε, hε, -, n₂, hBoost'⟩ := hBoost q r hr1 hrq
  obtain ⟨α, hα, -, n₃, hNib'⟩ :=
    hNib q r hr1 hrq (1 / 2) (by norm_num) (by norm_num) (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨δ, hδ, n₁, hRes'⟩ := hRes q r hr1 hrq α hα
  obtain ⟨n₅, hOmni'⟩ := hOmni δ hδ (ε / 2) (half_pos hε)
  obtain ⟨n₄, hn₄⟩ := Filter.eventually_atTop.1
    (eventually_parameter_bounds q r 1 hr le_rfl (ε / 2) δ (half_pos hε) hδ)
  refine ⟨max (max n₁ n₂) (max n₃ (max n₄ n₅)), fun n hn hdiv => ?_⟩
  obtain ⟨hn1, -, hdeg, hconv⟩ := hn₄ n (by omega)
  set K := completeRGraph (Fin n) r with hKdef
  obtain ⟨X, hXK, hXdeg, hXres⟩ := hRes' n (by omega)
  have hXr : IsRGraph r X := fun e he => (mem_powersetCard.1 (hXK he)).2
  obtain ⟨A, F, QA, hA, hAdeg⟩ := hOmni' n (by omega) X hXr hXdeg
  have hAr : IsRGraph r A := hA.isDecomposition_self.rgraph
  have hAK : A ⊆ K := fun e he => mem_powersetCard.2 ⟨subset_univ _, hAr e he⟩
  set J := K \ (A ∪ X) with hJdef
  have hJK : J ⊆ K := sdiff_subset
  have hmax0 : (0 : ℝ) ≤ max ((n : ℝ) ^ (1 - δ)) ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) :=
    le_max_of_le_left (by positivity)
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
    push_cast at hdeg
    nlinarith
  obtain ⟨H, hHJ, hHreg⟩ := hBoost' n (by omega) J hJK hJdeg
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

/-- **Steiner systems `S(2, q, n)` exist for all large admissible `n`** (Wilson's theorem for
Steiner systems), via refined absorption.  No hypotheses. -/
theorem steinerExistenceFor_two {q : ℕ} (hq : 2 < q) : SteinerExistenceFor q 2 :=
  steinerExistenceFor_of_weakOmni le_rfl hq weakReservesLemma
    (weakOmniAbsorberFor_of_native le_rfl hq (nativeWeakStrongMultiRefiners_two hq))
    boostLemma nibbleWithReservesGen_proved

/-- **The Existence Conjecture for Steiner systems**, conditional only on strong multi-refiners
with an `o(n)` budget for uniformities `r ≥ 3` (the case `r = 2` is proved). -/
theorem steinerExistence_of_nativeWeak
    (h : ∀ q r : ℕ, 3 ≤ r → r < q → NativeWeakStrongMultiRefiners q r) :
    SteinerExistenceConjecture := by
  intro q r hr hrq
  rcases Nat.eq_or_lt_of_le hr with rfl | hr3
  · exact steinerExistenceFor_two hrq
  · exact steinerExistenceFor_of_weakOmni hr hrq weakReservesLemma
      (weakOmniAbsorberFor_of_native hr hrq (h q r hr3 hrq)) boostLemma
      nibbleWithReservesGen_proved

/-- **Steiner systems for `r ≥ 3` from the intermediate link levels.**  For `3 ≤ r < q`, if
placed link refiners exist at the levels `1 ≤ i < r - 1`, then `S(r, q, n)` Steiner systems exist
for all large admissible `n`. -/
theorem steinerExistenceFor_of_levels {q r : ℕ} (hr : 3 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevel q r i) : SteinerExistenceFor q r :=
  steinerExistenceFor_of_weakOmni (by omega) hrq weakReservesLemma
    (weakOmniAbsorberFor_of_native (by omega) hrq
      (nativeWeakStrongMultiRefiners_of_levels (by omega) hrq hL)) boostLemma
    nibbleWithReservesGen_proved

/-- **Steiner systems for `r ≥ 3` from the intermediate link levels, with an additive term.**
As `steinerExistenceFor_of_levels`, but the link refiners may carry a monotone sublinear additive
term `a |Z|` (`PlacedLinkLevelA`). -/
theorem steinerExistenceFor_of_levelsA {q r : ℕ} {a : ℕ → ℕ} (hr : 3 ≤ r) (hrq : r < q)
    (hale : ∀ m, a m ≤ m) (hamono : Monotone a)
    (hsub : ∀ k : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, k * a m ≤ m)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelA q r i a) : SteinerExistenceFor q r :=
  steinerExistenceFor_of_weakOmni (by omega) hrq weakReservesLemma
    (weakOmniAbsorberFor_of_native (by omega) hrq
      (nativeWeakStrongMultiRefiners_of_levelsA (by omega) hrq hale hamono hsub hL)) boostLemma
    nibbleWithReservesGen_proved

/-- **Steiner triple-type systems `S(3, q, n)`** exist for all large admissible `n`, provided
placed link refiners exist at the single intermediate level `i = 1`. -/
theorem steinerExistenceFor_three {q : ℕ} (hq : 3 < q) (hL : PlacedLinkLevel q 3 1) :
    SteinerExistenceFor q 3 :=
  steinerExistenceFor_of_levels le_rfl hq (fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact hL)

/-- **The Existence Conjecture for Steiner systems**, conditional only on placed link refiners at
the intermediate levels `1 ≤ i < r - 1` for `r ≥ 3`.  (For `r = 2` there is no such level and the
statement is `steinerExistenceFor_two`.) -/
theorem steinerExistence_of_levels
    (h : ∀ q r i : ℕ, 3 ≤ r → r < q → 1 ≤ i → i < r - 1 → PlacedLinkLevel q r i) :
    SteinerExistenceConjecture := by
  intro q r hr hrq
  rcases Nat.eq_or_lt_of_le hr with rfl | hr3
  · exact steinerExistenceFor_two hrq
  · exact steinerExistenceFor_of_levels hr3 hrq (fun i hi hir => h q r i hr3 hrq hi hir)

end RefinedAbsorption.Dense
