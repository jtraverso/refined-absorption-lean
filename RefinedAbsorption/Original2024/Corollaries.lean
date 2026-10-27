module
public import RefinedAbsorption.Original2024.FlatOne
public import RefinedAbsorption.Multigraph.Existence

/-!
# Corollaries of the original article (Delcourt–Postle 2024)

M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*,
arXiv:2402.17855v1.

Consequences of the article's own results:

* `theorem_1_1_steiner`: the Existence Conjecture for Steiner systems (`λ = 1`), derived directly
  from the minimum degree version (Theorem 6.1) applied to `K_n^r`.
* `theorem_1_1`: the Existence Conjecture (Keevash's theorem) for every `λ ≥ 1`, by refined
  absorption (`existenceConjecture_proved`).
* `theorem_3_7_local`: Theorem 3.7 in local flat form (with clique pieces), all `2 ≤ k < q`.
* `decomposition_complete_minus_sparse`: `K_n^r` minus any `K_q^r`-divisibility-preserving
  sparse `r`-graph (`Δ_{r-1}(H) ≤ ε n`) has a `K_q^r`-decomposition (from Theorem 6.1).
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset

/-- The degree of `S` in `G \ H` for `H ⊆ G`. -/
theorem deg_sdiff_of_subset {V : Type*} [DecidableEq V] {G H : Finset (Finset V)} (hHG : H ⊆ G)
    (S : Finset V) : deg (G \ H) S = deg G S - deg H S := by
  unfold deg
  have e : (G \ H).filter (fun e => S ⊆ e) = G.filter (fun e => S ⊆ e) \ H.filter (fun e => S ⊆ e) := by
    ext x; simp only [mem_filter, mem_sdiff]; tauto
  rw [e, card_sdiff_of_subset (filter_subset_filter _ hHG)]

/-- `K_n^r` is an `r`-graph. -/
theorem isRGraph_completeRGraph (n r : ℕ) : IsRGraph r (completeRGraph (Fin n) r) :=
  fun _ he => (mem_powersetCard.1 he).2

/-- **Corollary of Theorem 6.1: complete graphs minus sparse graphs.**  For `q > r ≥ 1` there are
`ε > 0` and `n₀` such that for `n ≥ n₀`, if `H ⊆ K_n^r` has `Δ_{r-1}(H) ≤ ε n` and `K_n^r \ H` is
`K_q^r`-divisible, then `K_n^r \ H` has a `K_q^r`-decomposition. -/
theorem decomposition_complete_minus_sparse {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ H : Finset (Finset (Fin n)),
      H ⊆ completeRGraph (Fin n) r → MaxDegLE r H (ε * n) →
      IsDivisible q r (completeRGraph (Fin n) r \ H) →
      HasDecomposition q r (completeRGraph (Fin n) r \ H) := by
  obtain ⟨ε, hε, n₀, h⟩ := theorem_6_1 q r hr hrq
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt ((r : ℝ) / (ε / 2))
  refine ⟨ε / 2, by positivity, max n₀ n₁, fun n hn H hHK hHD hdiv => ?_⟩
  refine h n (le_of_max_le_left hn) _ (fun e he => isRGraph_completeRGraph n r e (mem_sdiff.1 he).1)
    (fun S hS => ?_) hdiv
  rw [deg_sdiff_of_subset hHK, deg_completeRGraph (by omega)]
  have hdH : (deg H S : ℝ) ≤ ε / 2 * n := hHD S hS
  have hHle : deg H S ≤ (n - S.card).choose (r - S.card) := by
    rw [← deg_completeRGraph (by omega)]
    exact card_le_card (filter_subset_filter _ hHK)
  have hrS : r - S.card = 1 := by omega
  rw [hrS, Nat.choose_one_right] at hHle ⊢
  rw [Nat.cast_sub hHle]
  have hn1 : (n₁ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hrn : (r : ℝ) < ε / 2 * n := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε / 2)).1 (lt_of_lt_of_le hn₁ hn1)
    linarith
  have hSn : S.card ≤ n := by simpa using card_le_univ S
  rw [Nat.cast_sub hSn]
  have hSr : (S.card : ℝ) ≤ r := by exact_mod_cast (show S.card ≤ r by omega)
  nlinarith

/-- **Theorem 1.1 for Steiner systems**, derived from the minimum degree version (Theorem 6.1)
applied to the complete `r`-graph. -/
theorem theorem_1_1_steiner : SteinerExistenceConjecture := by
  intro q r hr hrq
  obtain ⟨ε, hε, n₀, h⟩ := decomposition_complete_minus_sparse (q := q) (by omega) hrq
  refine ⟨n₀, fun n hn hdiv => ?_⟩
  have hdivK : IsDivisible q r (completeRGraph (Fin n) r) := isDivisible_completeRGraph_iff.2 hdiv
  obtain ⟨𝒮, h𝒮⟩ := h n hn ∅ (empty_subset _)
    (fun S _ => by simp [deg]; positivity) (by rwa [sdiff_empty])
  rw [sdiff_empty] at h𝒮
  exact ⟨𝒮, isSteinerSystem_iff_isDecomposition.2 h𝒮⟩

/-- **Theorem 1.1 (the Existence Conjecture, Keevash's theorem)** for every `λ ≥ 1`, by refined
absorption. -/
theorem theorem_1_1 : ExistenceConjecture := existenceConjecture_proved

/-- **Theorem 3.7 (refined multi-omni-absorber theorem, local flat form)** in every uniformity
`2 ≤ k < q`: every `k`-multigraph `L` of bounded multiplicity inside `Y` with `(k-1)`-degrees
`≤ d` has, for every set `P` of new vertices disjoint from `Y` with `|Y| ≤ K|P|` and
`Ch · d ≤ |P|`, a complete `K_q^k`-multi-refiner inside `Y ∪ P` whose new copies all meet `P`
(flatness), with `(k-1)`-degrees `≤ C (d + ⌈|P|^{1-1/k}⌉(⌊log₂|P|⌋+1))`, bounded multiplicities,
clique pieces (Remark 3.9) and at most `k` vertices of `Y` in the span of each piece. -/
theorem theorem_3_7_local : ∀ q k : ℕ, 2 ≤ k → k < q →
    General.FlatOmniK q k (Sharp.sharpCost k) := fun q k hk hkq =>
  General.flatOmniK_of_levels hk hkq fun j hj hjk => General.placedLinkLevelS_all k q j hk hkq hj hjk

end RefinedAbsorption.Original2024
