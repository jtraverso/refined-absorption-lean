module
public import RefinedAbsorption.Reserves
public import RefinedAbsorption.Boost

/-!
# The Existence Conjecture from the two remaining ingredients

With the reserves lemma (`weakReservesLemma`, `Reserves.lean`) and the boost lemma
(`boostLemma`, `Boost.lean`) proved, the refined absorption proof of the Existence Conjecture
for Steiner systems only assumes the refined efficient omni-absorber theorem (Theorem 1.10) and
the nibble with reserves (Corollary 2.4).

Moreover, since the boost we construct has *constant* error (`exists_boost_const_error`), the
mismatch between the normalisations of Lemma 2.2 and Corollary 2.4 disappears: Corollary 2.4
exactly as stated in the survey (`NibbleWithReserves`, error `n^{-1/3}`) suffices
(`steinerExistence_of_omniAbsorber_nibbleWithReserves`).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-- **The Existence Conjecture for Steiner systems via refined absorption**, assuming only
Theorem 1.10 (refined efficient omni-absorbers) and Corollary 2.4 (nibble with reserves, with
general polynomial error). -/
theorem steinerExistence_of_omniAbsorber_nibble (hOmni : RefinedEfficientOmniAbsorber)
    (hNib : NibbleWithReservesGen) : SteinerExistenceConjecture :=
  steinerExistence_of_omniAbsorber_boost_nibble hOmni boostLemma hNib

/-- Converting a constant error around `binom(n-r, k)/2` to an error `n^{-1/3} binom(n, k)`
around `binom(n, k)/2`, for large `n`. -/
theorem ev_const_error_conversion (r k t : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ x : ℝ, |x - 1 / 2 * ((n - r).choose k : ℝ)| ≤ t →
      |x - 1 / 2 * (n.choose k : ℝ)| ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) * n.choose k := by
  set c : ℝ := 2 * t * k.factorial + r * k / 2 with hc
  have hc0 : 0 ≤ c := by positivity
  filter_upwards [Filter.eventually_ge_atTop (2 * k),
    ev_rpow_neg_le (show (0 : ℝ) < 2 / 3 by norm_num) (show (0 : ℝ) < 1 / (c + 1) by positivity)]
    with n hn h23 x hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : (n - r).choose k ≤ n.choose k := Nat.choose_le_choose _ (by omega)
  have hle' : ((n - r).choose k : ℝ) ≤ n.choose k := by exact_mod_cast hle
  have hkey : (n : ℝ) * ((n.choose k : ℝ) - (n - r).choose k) ≤ (r * k : ℕ) * n.choose k := by
    rw [← Nat.cast_sub hle]; exact_mod_cast choose_sub_choose_le n r k
  -- `binom(n, k) ≥ n / (2 k!)`
  have hM : (n : ℝ) / 2 / k.factorial ≤ n.choose k := by
    have h := choose_sub_ge (n := n) (r := 0) (k := k) (by omega)
    rw [Nat.sub_zero] at h
    refine le_trans ?_ h
    have hn2 : (1 : ℝ) ≤ n / 2 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (show 2 ≤ n by omega)
    gcongr
    calc (n : ℝ) / 2 = (n / 2) ^ 1 := (pow_one _).symm
      _ ≤ (n / 2) ^ k := pow_le_pow_right₀ hn2 hk
  have hfk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have ht : (t : ℝ) ≤ 2 * t * k.factorial / n * n.choose k := by
    rw [div_div] at hM
    have e : 2 * (t : ℝ) * k.factorial / n * (n / (2 * k.factorial)) = t := by field_simp
    calc (t : ℝ) = _ := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)
  have hdiff : (n.choose k : ℝ) - (n - r).choose k ≤ (r * k : ℝ) / n * n.choose k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hn0]; push_cast at hkey; linarith
  have h3 : |x - 1 / 2 * (n.choose k : ℝ)| ≤
      |x - 1 / 2 * ((n - r).choose k : ℝ)| + 1 / 2 * ((n.choose k : ℝ) - (n - r).choose k) := by
    have := abs_sub_le x (1 / 2 * ((n - r).choose k : ℝ)) (1 / 2 * (n.choose k))
    rw [abs_of_nonpos (a := 1 / 2 * ((n - r).choose k : ℝ) - 1 / 2 * (n.choose k))
      (by linarith)] at this
    linarith
  have hcn : c / n ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have e : c / n = c * (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hn0]; norm_num
      rw [Real.rpow_neg_one]; field_simp
    rw [e]
    have h1 : c * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := by
      calc c * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤ (c + 1) * (1 / (c + 1)) := by
            apply mul_le_mul (by linarith) h23 (by positivity) (by positivity)
        _ = 1 := by field_simp
    have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
    nlinarith
  have hMpos : (0 : ℝ) ≤ n.choose k := by positivity
  calc |x - 1 / 2 * (n.choose k : ℝ)|
      ≤ 2 * t * k.factorial / n * n.choose k + 1 / 2 * ((r * k : ℝ) / n * n.choose k) := by
        linarith
    _ = c / n * n.choose k := by rw [hc]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcn hMpos

/-- **The Existence Conjecture for Steiner systems via refined absorption, from the survey's
statements of the two remaining ingredients**: Theorem 1.10 (refined efficient omni-absorbers)
and Corollary 2.4 exactly as stated in the survey (nibble with reserves, error `n^{-1/3}`) imply
that for `q > r ≥ 2` and all large `n` satisfying the divisibility conditions, an
`(n, q, r)`-Steiner system exists.  The reserves (Lemma 2.1, in the form used) and the boost
(Lemma 2.2, with constant error) are proved in this project. -/
theorem steinerExistence_of_omniAbsorber_nibbleWithReserves
    (hOmni : RefinedEfficientOmniAbsorber) (hNib : NibbleWithReserves) :
    SteinerExistenceConjecture := by
  intro q r hr hrq
  have hr1 : 1 ≤ r := by omega
  obtain ⟨C, hC1, hOmni'⟩ := hOmni q r hr1 hrq
  obtain ⟨ε, hε, -, hBoost'⟩ := exists_boost_const_error hr1 hrq
  obtain ⟨α, hα, -, n₃, hNib'⟩ := hNib q r hr1 hrq (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨δ, hδ, n₁, hRes'⟩ := weakReservesLemma q r hr1 hrq α hα
  obtain ⟨n₄, hn₄⟩ := Filter.eventually_atTop.1
    ((eventually_parameter_bounds q r C hr hC1 ε δ hε hδ).and
      (ev_const_error_conversion r (q - r) (q.choose r) (by omega)))
  refine ⟨max (max n₁ (2 * (q + r))) (max n₃ n₄), fun n hn hdiv => ?_⟩
  obtain ⟨⟨hn1, hD, hdeg, -⟩, hconv⟩ := hn₄ n (by omega)
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
      ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) * (n.choose (q - r)) :=
    fun e he => hconv _ (hHreg e he)
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

end RefinedAbsorption
