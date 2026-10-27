module
public import RequestProject.Pending.SafeHost
public import RequestProject.Pending.SafeNibble
public import RequestProject.Original2024.MinDegree

/-!
# Theorem 6.3 of arXiv:2402.17855v1, uniformity `r ≥ 2`

`theorem_6_3_two_le`: the proof of Theorem 6.1 (`Original2024.theorem_6_1_two_le`) modified in the
two places indicated in Section 6.3 of the article, relative to the given packing `Q₁`:
1. the omni-absorber is built from root-light absorbers placed safely (`safeTheorem17`), so that
   all cliques of its decomposition family meet every block of `Q₁` in at most `r` vertices;
2. the nibble and the reserve covering avoid the dangerous cliques `dangerFam q r Q₁`
   (`safeNibbleWithReserves`), which are few by `cliqueMult_dangerFam_le`.
The final decomposition is `QA L ∪ P` (absorption, `absorption_step_explicit`).
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Original2024

/-- **Absorption step with an explicit decomposition**: the decomposition produced by
`absorption_step` is `QA L ∪ P` for some divisible `L ⊆ X`. -/
theorem absorption_step_explicit {V : Type*} [DecidableEq V] [Fintype V] {q r : ℕ} (hrq : r ≤ q)
    {G X A F P : Finset (Finset V)} {QA : Finset (Finset V) → Finset (Finset V)}
    (hG : IsDivisible q r G) (hAG : A ⊆ G) (hA : IsOmniAbsorber q r X A F QA)
    (hP : IsPacking q r (G \ A) P) (hcov : G \ (A ∪ X) ⊆ coveredEdges r P) :
    ∃ L ⊆ X, IsDivisible q r L ∧ IsDecomposition q r G (QA L ∪ P) := by
  set cov := coveredEdges r P
  set L := (G \ A) \ cov with hLdef
  have hcovGA : cov ⊆ G \ A := hP.coveredEdges_subset
  have hLX : L ⊆ X := by
    intro e he
    simp only [hLdef, mem_sdiff] at he
    by_contra hX
    exact he.2 (hcov (mem_sdiff.2 ⟨he.1.1, by simp [he.1.2, hX]⟩))
  have hAL : Disjoint A L := by
    rw [disjoint_left]; intro e heA heL
    exact (mem_sdiff.1 (mem_sdiff.1 heL).1).2 heA
  have hALcov : Disjoint (A ∪ L) cov := by
    rw [disjoint_left]; intro e he hc
    rcases mem_union.1 he with he | he
    · exact (mem_sdiff.1 (hcovGA hc)).2 he
    · exact (mem_sdiff.1 he).2 hc
  have hGeq : G = (A ∪ L) ∪ cov := by
    ext e
    constructor
    · intro he
      by_cases heA : e ∈ A
      · simp [heA]
      · by_cases hc : e ∈ cov
        · simp [hc]
        · simp [hLdef, he, heA, hc]
    · intro he
      rcases mem_union.1 he with he | he
      · rcases mem_union.1 he with he | he
        · exact hAG he
        · exact (mem_sdiff.1 (mem_sdiff.1 he).1).1
      · exact (mem_sdiff.1 (hcovGA he)).1
  have hPdec := hP.isDecomposition_coveredEdges
  have hAdiv : IsDivisible q r A := hA.isDecomposition_self.isDivisible
  have hLdiv : IsDivisible q r L := by
    have h1 : IsDivisible q r (A ∪ L) := by
      rw [hGeq] at hG
      exact hG.of_union hALcov hPdec.isDivisible
    rw [union_comm] at h1
    exact h1.of_union hAL.symm hAdiv
  refine ⟨L, hLX, hLdiv, ?_⟩
  rw [hGeq]
  exact (hA.decomp L hLX hLdiv).union hrq hALcov hPdec

/-- **Theorem 6.3, `r ≥ 2`.** -/
theorem theorem_6_3_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    ∃ (n₀ : ℕ) (ε : ℝ), 0 < ε ∧ ∀ n ≥ n₀,
      ∀ G : Finset (Finset (Fin n)), IsRGraph r G → IsDivisible q r G →
        MinDegGE r G ((1 - ε) * n) → ∀ Q₁ : Finset (Finset (Fin n)), IsPacking q r G Q₁ →
          ∃ Q₂ : Finset (Finset (Fin n)), IsDecomposition q r G Q₂ ∧
            ∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ r := by
  have hr1 : 1 ≤ r := by omega
  obtain ⟨C, hC1, ε₇, hε₇, hOmni⟩ := safeTheorem17 (q := q) hr hrq
  obtain ⟨εB, hεB, -, n₂, hBoost⟩ := boostLemma q r hr1 hrq
  obtain ⟨α, hα, -, n₃, hNib⟩ := safeNibbleWithReserves q r hr1 hrq (1 / 2) (by norm_num)
    (by norm_num) (1 / 4) (by norm_num) (by norm_num) ((2 ^ r * q : ℕ) : ℝ)
  obtain ⟨εR, hεR, δ, hδ, n₁, hRes⟩ := relWeakReserves hr1 hrq α hα
  obtain ⟨n₄, hn₄⟩ := Filter.eventually_atTop.1
    (eventually_parameter_bounds q r C hr hC1 (εB / 2) δ (by positivity) hδ)
  set ε := min (εB / 2) (min ε₇ εR) with hεdef
  have hε0 : 0 < ε := lt_min (by positivity) (lt_min hε₇ hεR)
  refine ⟨max (max (max n₁ n₂) (max n₃ n₄)) (C * q), ε, hε0,
    fun n hn G hG hdiv hδG Q₁ hQ₁ => ?_⟩
  have hn' : max (max n₁ n₂) (max n₃ n₄) ≤ n := le_trans (le_max_left _ _) hn
  have hCq : C * q ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hn1, hD, hdeg, hconv⟩ := hn₄ n (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmono : ∀ ε' : ℝ, ε ≤ ε' → MinDegGE r G ((1 - ε') * n) := fun ε' h S hS =>
    le_trans (by nlinarith) (hδG S hS)
  set K := completeRGraph (Fin n) r with hKdef
  have hGK : G ⊆ K := fun e he => mem_powersetCard.2 ⟨subset_univ _, hG e he⟩
  -- Step 1: reserves inside `G`
  obtain ⟨X, hXG, hXdeg, hXres⟩ := hRes n (by omega) G hG
    (hmono εR ((min_le_right _ _).trans (min_le_right _ _)))
  -- Step 2: a safe omni-absorber inside `G`
  obtain ⟨A, F, QA, hA, hAG, hAdeg, hFsafe⟩ := hOmni n G X ((n : ℝ) ^ (1 - δ)) Q₁ hG
    (hmono ε₇ ((min_le_right _ _).trans (min_le_left _ _))) hXG hXdeg hD hQ₁.card_eq
    hQ₁.mult_le hCq
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
  -- Step 4: the nibble with reserves avoiding the dangerous cliques
  have hXJ : X ⊆ K \ J := by
    intro e he
    rw [mem_sdiff]
    exact ⟨hGK (hXG he), fun h => (mem_sdiff.1 h).2 (mem_union_right _ he)⟩
  have hreg : ∀ e ∈ J, |(cliqueMult H e : ℝ) - (1 / 2) * (n.choose (q - r))|
      ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n.choose (q - r)) :=
    fun e he => clique_deg_conversion (by omega) (hHreg e he) hconv
  have hresJ : ∀ e ∈ J, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card :=
    fun e he => hXres e (mem_sdiff.1 he).1
  have hΦ : ∀ e : Finset (Fin n), e.card = r →
      (cliqueMult (dangerFam q r Q₁) e : ℝ) ≤ ((2 ^ r * q : ℕ) : ℝ) * (n : ℝ) ^ (q - r - 1) := by
    intro e he
    have := cliqueMult_dangerFam_le hrq hQ₁.card_eq hQ₁.mult_le he
    exact_mod_cast this
  obtain ⟨P, hP, hcov, hPΦ⟩ := hNib n (by omega) J hJK H hHJ hreg X hXJ hresJ
    (dangerFam q r Q₁) hΦ
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
  obtain ⟨L, hLX, hLdiv, hdec⟩ := absorption_step_explicit hrq.le hdiv hAG hA' hP hcov
  refine ⟨QA L ∪ P, hdec, fun P₁ hP₁ P₂ hP₂ => ?_⟩
  rw [inter_comm]
  rcases mem_union.1 hP₂ with h | h
  · exact hFsafe P₂ (hA'.subset_family L hLX hLdiv h) P₁ hP₁
  · exact inter_le_of_not_mem_dangerFam (hP.card_eq P₂ h) (disjoint_left.1 hPΦ h) P₁ hP₁

end RefinedAbsorption.Pending
