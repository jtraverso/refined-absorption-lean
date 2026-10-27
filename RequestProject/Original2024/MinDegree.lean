module
public import RequestProject.Original2024.HostOne
public import RequestProject.Original2024.RelReserves
public import RequestProject.Boost
public import RequestProject.Nibble.Bridge

/-!
# Theorem 6.1 of the original article: the minimum degree version (`λ = 1`)

Every `K_q^r`-divisible `r`-graph `G` on `n ≥ n₀` vertices with `δ_{r-1}(G) ≥ (1 - ε) n` has a
`K_q^r`-decomposition.

The proof for `r ≥ 2` follows Section 6 of the article, relative to `G`:
1. reserves `X ⊆ G` (`relWeakReserves`, a random subset of `G`);
2. a refined efficient omni-absorber `A ⊆ G` for `X` (Theorem 1.7 in the host `G`,
   `theorem_1_7_two_le`);
3. the boost lemma on `J = G \ (A ∪ X)` (`boostLemma`, which is already stated for an arbitrary
   dense `J`);
4. the nibble with reserves (`nibbleWithReservesGen_proved`), covering `J` with a packing of
   `J ∪ X = G \ A`;
5. absorption of the leftover `L ⊆ X` (`absorption_step`).

For `r = 1` the statement is elementary (`theorem_6_1_one`).
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.ChainRefiner

/-- An omni-absorber in the sense of Definition 1.5 is an omni-absorber in the survey's sense. -/
theorem IsOmniAbsorberOn.toSurvey {α : Type*} [DecidableEq α] {q r : ℕ} {U : Finset α}
    {X A F : Finset (Finset α)} {QA : Finset (Finset α) → Finset (Finset α)}
    (h : IsOmniAbsorberOn q r U X A F QA) : IsOmniAbsorber q r X A F QA :=
  ⟨fun e he => (h.graphX e he).1, h.disjoint, h.subset_family, h.decomp⟩

/-- **Theorem 6.1, `r ≥ 2`.** -/
theorem theorem_6_1_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) : Theorem_6_1_for q r := by
  have hr1 : 1 ≤ r := by omega
  obtain ⟨C, hC1, ε₇, hε₇, hOmni⟩ := theorem_1_7_two_le (q := q) hr hrq
  obtain ⟨εB, hεB, -, n₂, hBoost⟩ := boostLemma q r hr1 hrq
  obtain ⟨α, hα, -, n₃, hNib⟩ := nibbleWithReservesGen_proved q r hr1 hrq (1 / 2) (by norm_num)
    (by norm_num) (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨εR, hεR, δ, hδ, n₁, hRes⟩ := relWeakReserves hr1 hrq α hα
  obtain ⟨n₄, hn₄⟩ := Filter.eventually_atTop.1
    (eventually_parameter_bounds q r C hr hC1 (εB / 2) δ (by positivity) hδ)
  set ε := min (εB / 2) (min ε₇ εR) with hεdef
  have hε0 : 0 < ε := lt_min (by positivity) (lt_min hε₇ hεR)
  refine ⟨ε, hε0, max (max n₁ n₂) (max n₃ n₄), fun n hn G hG hδG hdiv => ?_⟩
  obtain ⟨hn1, hD, hdeg, hconv⟩ := hn₄ n (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmono : ∀ ε' : ℝ, ε ≤ ε' → MinDegGE r G ((1 - ε') * n) := fun ε' h S hS =>
    le_trans (by nlinarith) (hδG S hS)
  set K := completeRGraph (Fin n) r with hKdef
  have hGK : G ⊆ K := fun e he => mem_powersetCard.2 ⟨subset_univ _, hG e he⟩
  -- Step 1: reserves inside `G`
  obtain ⟨X, hXG, hXdeg, hXres⟩ := hRes n (by omega) G hG
    (hmono εR ((min_le_right _ _).trans (min_le_right _ _)))
  -- Step 2: omni-absorber inside `G`
  obtain ⟨A, F, QA, hA, hAG, -, hAdeg⟩ := hOmni n G X ((n : ℝ) ^ (1 - δ)) hG
    (hmono ε₇ ((min_le_right _ _).trans (min_le_left _ _))) hXG hXdeg hD
  have hA' := hA.toSurvey
  -- Step 3: boost on `J = G \ (A ∪ X)`
  set J := G \ (A ∪ X) with hJdef
  have hJK : J ⊆ K := sdiff_subset.trans hGK
  have hJdeg : MinDegGE r J ((1 - εB) * n) := by
    intro S hS
    have h1 : deg G S ≤ deg J S + deg A S + deg X S := by
      unfold deg
      calc (G.filter (fun e => S ⊆ e)).card
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
    have h1' : ((deg G S : ℕ) : ℝ) ≤ deg J S + deg A S + deg X S := by exact_mod_cast h1
    have hGd := hδG S hS
    have hAd := hAdeg S hS
    have hXd := hXdeg S hS
    have hεB : ε ≤ εB / 2 := min_le_left _ _
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    unfold budget at hAd
    nlinarith
  obtain ⟨H, hHJ, hHreg⟩ := hBoost n (by omega) J hJK hJdeg
  -- Step 4: nibble with reserves
  have hXJ : X ⊆ K \ J := by
    intro e he
    rw [mem_sdiff]
    exact ⟨hGK (hXG he), fun h => (mem_sdiff.1 h).2 (mem_union_right _ he)⟩
  have hreg : ∀ e ∈ J, |(cliqueMult H e : ℝ) - (1 / 2) * (n.choose (q - r))|
      ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n.choose (q - r)) :=
    fun e he => clique_deg_conversion (by omega) (hHreg e he) hconv
  have hresJ : ∀ e ∈ J, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card :=
    fun e he => hXres e (mem_sdiff.1 he).1
  obtain ⟨P, hP, hcov⟩ := hNib n (by omega) J hJK H hHJ hreg X hXJ hresJ
  -- Step 5: absorb the leftover
  have hJX : J ∪ X = G \ A := by
    ext e
    simp only [hJdef, mem_union, mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h1, fun h => h2 (Or.inl h)⟩
      · exact ⟨hXG h, fun h' => disjoint_left.1 hA.disjoint h h'⟩
    · rintro ⟨h1, h2⟩
      by_cases hX : e ∈ X
      · exact Or.inr hX
      · exact Or.inl ⟨h1, by tauto⟩
  rw [hJX] at hP
  exact absorption_step hrq.le hdiv hAG hA' hP hcov

/-- A set of singletons whose size is a multiple of `q` has a `K_q^1`-decomposition. -/
theorem hasDecomposition_sing_of_dvd {V : Type*} [DecidableEq V] {q : ℕ} (hq : 1 ≤ q) :
    ∀ (S : Finset V), q ∣ S.card → HasDecomposition q 1 (sing S) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hdvd
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · exact hasDecomposition_sing (Or.inl h0)
    · have hqS : q ≤ S.card := Nat.le_of_dvd hpos hdvd
      obtain ⟨T, hTS, hTc⟩ := exists_subset_card_eq hqS
      have hlt : S \ T ⊂ S := by
        refine sdiff_ssubset hTS ?_
        rw [← card_pos, hTc]; omega
      have hdvd' : q ∣ (S \ T).card := by
        rw [card_sdiff_of_subset hTS, hTc]
        exact Nat.dvd_sub hdvd (dvd_refl q)
      obtain ⟨𝒬₁, h₁⟩ := ih _ hlt hdvd'
      obtain ⟨𝒬₂, h₂⟩ := hasDecomposition_sing (V := V) (q := q) (S := T) (Or.inr hTc)
      have hdisj : Disjoint (sing (S \ T)) (sing T) := by
        rw [disjoint_left]
        intro e he he'
        obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
        rw [singleton_mem_sing] at he'
        exact (mem_sdiff.1 ha).2 he'
      have hU : sing (S \ T) ∪ sing T = sing S := by
        rw [← sing_union, sdiff_union_of_subset hTS]
      exact ⟨_, hU ▸ h₁.union hq hdisj h₂⟩

/-- **Theorem 6.1, `r = 1`.** -/
theorem theorem_6_1_one {q : ℕ} (hq : 2 ≤ q) : Theorem_6_1_for q 1 := by
  refine ⟨1, one_pos, 0, fun n _ G hG _ hdiv => ?_⟩
  have hGeq : G = sing (G.biUnion id) := eq_sing_biUnion hG
  have hdvd : q ∣ (G.biUnion id).card := by
    have := hdiv ∅ (by simp)
    simp only [card_empty, Nat.sub_zero, Nat.choose_one_right, deg_empty] at this
    rwa [hGeq, card_sing] at this
  rw [hGeq]
  exact hasDecomposition_sing_of_dvd (by omega) _ hdvd

/-- **Theorem 6.1** for all `q > r ≥ 1`. -/
theorem theorem_6_1 : Theorem_6_1 := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_6_1_one (by omega)
  · exact theorem_6_1_two_le h hrq

end RefinedAbsorption.Original2024
