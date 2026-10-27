module
public import RefinedAbsorption.Original2024.Corollaries
public import RefinedAbsorption.Extensions.Partial

/-!
# Completion of sparse partial Steiner systems

A *partial Steiner system* with parameters `(q, r)` is a family of `q`-sets such that every
`r`-set lies in at most one of them.  This file proves that, for `n` large and admissible, every
partial Steiner system on `n` points which is *sparse* (every `(r-1)`-set lies in at most `ε n`
of its covered `r`-sets) can be completed to a full Steiner system `S(n, q, r)` containing it.

The proof combines the minimum degree version of the Existence Conjecture (Theorem 6.1 of the
original article, `theorem_6_1`) with a divisibility computation: the covered `r`-graph `H` of
the partial system is decomposed by the partial system itself, hence is `K_q^r`-divisible, so
`K_n^r \ H` is `K_q^r`-divisible as well and has a decomposition; adding back the blocks of the
partial system gives the Steiner system.
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset RefinedAbsorption.Original2024

variable {V : Type*} [DecidableEq V]

/-- A partial Steiner system is a `K_q^r`-decomposition of the `r`-graph it covers. -/
theorem IsPartialSteinerSystem.isDecomposition {q r : ℕ} {P : Finset (Finset V)}
    (hP : IsPartialSteinerSystem q r P) : IsDecomposition q r (coveredEdges r P) P := by
  refine ⟨fun e he => ?_, hP.1, fun e he => ?_⟩
  · obtain ⟨Q, -, hQ⟩ := mem_biUnion.1 he
    exact (mem_powersetCard.1 hQ).2
  · have h1 := hP.2 e he
    by_cases hcov : e ∈ coveredEdges r P
    · rw [if_pos hcov]
      obtain ⟨Q, hQP, hQ⟩ := mem_biUnion.1 hcov
      have : 0 < cliqueMult P e :=
        card_pos.2 ⟨Q, mem_filter.2 ⟨hQP, (mem_powersetCard.1 hQ).1⟩⟩
      omega
    · rw [if_neg hcov]
      refine card_eq_zero.2 (filter_eq_empty_iff.2 fun Q hQP heQ => hcov ?_)
      exact mem_biUnion.2 ⟨Q, hQP, mem_powersetCard.2 ⟨heQ, he⟩⟩

/-- If `H ⊆ G` and both are `K_q^r`-divisible, so is `G \ H`. -/
theorem isDivisible_sdiff {q r : ℕ} {G H : Finset (Finset V)} (hHG : H ⊆ G)
    (hG : IsDivisible q r G) (hH : IsDivisible q r H) : IsDivisible q r (G \ H) := by
  intro S hS
  rw [RefinedAbsorption.Original2024.deg_sdiff_of_subset hHG]
  exact Nat.dvd_sub (hG S hS) (hH S hS)

/-- The covered `r`-graph of a family of `q`-sets on `Fin n` is a subgraph of `K_n^r`. -/
theorem coveredEdges_subset_complete {n r : ℕ} (P : Finset (Finset (Fin n))) :
    coveredEdges r P ⊆ completeRGraph (Fin n) r := by
  intro e he
  obtain ⟨Q, -, hQ⟩ := mem_biUnion.1 he
  exact mem_powersetCard.2 ⟨subset_univ _, (mem_powersetCard.1 hQ).2⟩

/-- **Completion of sparse partial Steiner systems.**  For `q > r ≥ 1` there are `ε > 0` and
`n₀` such that for every `n ≥ n₀` satisfying the divisibility conditions, every partial Steiner
system `P` on `n` points whose covered `r`-graph has maximum `(r-1)`-degree at most `ε n` is
contained in an `(n, q, r)`-Steiner system. -/
theorem partialSteiner_completion {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ P : Finset (Finset (Fin n)), IsPartialSteinerSystem q r P →
        MaxDegLE r (coveredEdges r P) (ε * n) →
        ∃ 𝒮 : Finset (Finset (Fin n)), P ⊆ 𝒮 ∧ IsSteinerSystem q r 𝒮 := by
  obtain ⟨ε, hε, n₀, h⟩ := decomposition_complete_minus_sparse (q := q) hr hrq
  refine ⟨ε, hε, n₀, fun n hn hdiv P hP hdeg => ?_⟩
  set H := coveredEdges r P
  set K := completeRGraph (Fin n) r
  have hHK : H ⊆ K := coveredEdges_subset_complete P
  have hPdec := hP.isDecomposition
  have hKdiv : IsDivisible q r K := isDivisible_completeRGraph_iff.2 hdiv
  obtain ⟨𝒬, h𝒬⟩ := h n hn H hHK hdeg (isDivisible_sdiff hHK hKdiv hPdec.isDivisible)
  have hunion := IsDecomposition.union hrq.le disjoint_sdiff hPdec h𝒬
  rw [union_sdiff_of_subset hHK] at hunion
  exact ⟨P ∪ 𝒬, subset_union_left, isSteinerSystem_iff_isDecomposition.2 hunion⟩

end RefinedAbsorption.Extensions
