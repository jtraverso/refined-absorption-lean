module
public import RequestProject.Pending.Theorem63Final
public import RequestProject.Extensions.Completion
public import RequestProject.Extensions.Embedding
public import RequestProject.Extensions.CountCore
public import RequestProject.Extensions.Packing

/-!
# Disjoint mates and the intersection problem for Steiner systems

Built on Theorem 6.3 of arXiv:2402.17855v1 (`Pending.theorem_6_3`: minimum degree existence
avoiding a given packing) and on the existence and completion theorems already proved.

* `steiner_completion_avoiding`: a sparse partial Steiner system `P` can be completed to a
  Steiner system `𝒮` which shares with an arbitrary partial Steiner system `F` only the blocks
  that `P` already shares with it (`𝒮 ∩ F = P ∩ F`); moreover every new block meets every block
  of `F` whose `r`-sets are not covered by `P` in at most `r` points.
* `steiner_orthogonal_mate`: for every partial Steiner system `F` on `n` points there is a Steiner
  system every block of which meets every block of `F` in at most `r` points.
* `steiner_disjoint_mate`: every Steiner system of large admissible order has a disjoint mate.
* `decomposition_disjoint_mate`: the same for `K_q^r`-decompositions of dense divisible graphs.
* `steiner_intersection_prescribed`: for every Steiner system `𝒮₁` and every sparse subfamily
  `P ⊆ 𝒮₁` there is a Steiner system `𝒮₂` with `𝒮₁ ∩ 𝒮₂ = P` exactly.
* `steiner_intersection_exact`: every sparse partial Steiner system is the exact intersection of
  two Steiner systems; `partialSteiner_intersection_embedding`: every finite partial Steiner
  system is (after embedding) the exact intersection of two Steiner systems.
* `steiner_intersection_spectrum`, `steiner_intersection_spectrum_poly`: for every `k ≤ c n^r`
  there are two Steiner systems with exactly `k` common blocks.
* `exists_two_fold_design_split`: `2`-fold designs which split into two Steiner systems and in
  which two distinct blocks share at most `r` points.
* `sts_disjoint_mate_and_spectrum`: the case of Steiner triple systems.
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset RefinedAbsorption.Original2024

/-- Removing a sparse `r`-graph from `K_n^r` keeps the minimum degree close to `n`. -/
theorem minDeg_complete_sdiff {n r : ℕ} {ε : ℝ} (hrn : (r : ℝ) < ε / 2 * n)
    {H : Finset (Finset (Fin n))} (hHK : H ⊆ completeRGraph (Fin n) r)
    (hHD : MaxDegLE r H (ε / 2 * n)) :
    MinDegGE r (completeRGraph (Fin n) r \ H) ((1 - ε) * n) := by
  intro S hS
  rw [deg_sdiff_of_subset hHK, deg_completeRGraph (by omega)]
  have hdH : (deg H S : ℝ) ≤ ε / 2 * n := hHD S hS
  have hHle : deg H S ≤ (n - S.card).choose (r - S.card) := by
    rw [← deg_completeRGraph (by omega)]
    exact card_le_card (filter_subset_filter _ hHK)
  have hrS : r - S.card = 1 := by omega
  rw [hrS, Nat.choose_one_right] at hHle ⊢
  have hSn : S.card ≤ n := by simpa using card_le_univ S
  rw [Nat.cast_sub hSn]
  have hSr : (S.card : ℝ) ≤ r := by exact_mod_cast (show S.card ≤ r by omega)
  nlinarith

/-- The blocks of a partial Steiner system all of whose `r`-sets lie in `G` form a packing. -/
theorem isPacking_filter {q r : ℕ} {V : Type*} [DecidableEq V] {F G : Finset (Finset V)}
    (hF : IsPartialSteinerSystem q r F) :
    IsPacking q r G (F.filter (fun B => cliqueEdges r B ⊆ G)) := by
  refine ⟨fun Q hQ => hF.1 Q (mem_filter.1 hQ).1, fun Q hQ => (mem_filter.1 hQ).2,
    fun e he => le_trans ?_ (hF.2 e he)⟩
  exact card_le_card (filter_subset_filter _ (filter_subset _ _))

/-- **Completion avoiding a partial Steiner system.** -/
theorem steiner_completion_avoiding {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ P F : Finset (Finset (Fin n)), IsPartialSteinerSystem q r P →
        MaxDegLE r (coveredEdges r P) (ε * n) → IsPartialSteinerSystem q r F →
        ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧ P ⊆ 𝒮 ∧ 𝒮 ∩ F = P ∩ F ∧
          ∀ B₁ ∈ F, Disjoint (cliqueEdges r B₁) (coveredEdges r P) →
            ∀ B₂ ∈ 𝒮 \ P, (B₁ ∩ B₂).card ≤ r := by
  obtain ⟨n₃, ε₃, hε₃, h63⟩ := RefinedAbsorption.Pending.theorem_6_3 q r hr hrq
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt ((r : ℝ) / (ε₃ / 2))
  refine ⟨ε₃ / 2, by positivity, max n₃ n₁, fun n hn hdiv P F hP hPdeg hF => ?_⟩
  set H := coveredEdges r P
  set K := completeRGraph (Fin n) r
  have hHK : H ⊆ K := coveredEdges_subset_complete P
  have hPdec := hP.isDecomposition
  have hKdiv : IsDivisible q r K := isDivisible_completeRGraph_iff.2 hdiv
  have hGdiv := isDivisible_sdiff hHK hKdiv hPdec.isDivisible
  have hGr : IsRGraph r (K \ H) := fun e he => isRGraph_completeRGraph n r e (mem_sdiff.1 he).1
  have hrn : (r : ℝ) < ε₃ / 2 * n := by
    have hn1 : (n₁ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε₃ / 2)).1 (lt_of_lt_of_le hn₁ hn1)
    linarith
  have hmin := minDeg_complete_sdiff hrn hHK hPdeg
  obtain ⟨Q₂, hQ₂, hcross⟩ := h63 n (le_of_max_le_left hn) (K \ H) hGr hGdiv hmin
    (F.filter (fun B => cliqueEdges r B ⊆ K \ H)) (isPacking_filter hF)
  have hunion := IsDecomposition.union hrq.le disjoint_sdiff hPdec hQ₂
  rw [union_sdiff_of_subset hHK] at hunion
  have hQ₂F : ∀ B ∈ Q₂, B ∉ F := by
    intro B hB hBF
    have h1 := hcross B (mem_filter.2 ⟨hBF, hQ₂.cliqueEdges_subset hB⟩) B hB
    rw [inter_self, hQ₂.card_eq B hB] at h1
    omega
  refine ⟨P ∪ Q₂, isSteinerSystem_iff_isDecomposition.2 hunion, subset_union_left, ?_, ?_⟩
  · ext B
    simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨hB | hB, hBF⟩
      · exact ⟨hB, hBF⟩
      · exact absurd hBF (hQ₂F B hB)
    · rintro ⟨hB, hBF⟩
      exact ⟨Or.inl hB, hBF⟩
  · intro B₁ hB₁ hdisj B₂ hB₂
    obtain ⟨hB₂u, hB₂P⟩ := mem_sdiff.1 hB₂
    have hB₂Q : B₂ ∈ Q₂ := by
      rcases mem_union.1 hB₂u with h | h
      · exact absurd h hB₂P
      · exact h
    refine hcross B₁ (mem_filter.2 ⟨hB₁, fun e he => mem_sdiff.2 ⟨?_, disjoint_left.1 hdisj he⟩⟩)
      B₂ hB₂Q
    exact mem_powersetCard.2 ⟨subset_univ _, (mem_powersetCard.1 he).2⟩

/-- The empty family has no covered edges, so it is as sparse as possible. -/
theorem maxDegLE_coveredEdges_empty {n r : ℕ} {D : ℝ} (hD : 0 ≤ D) :
    MaxDegLE r (coveredEdges r (∅ : Finset (Finset (Fin n)))) D := by
  intro S _
  simp [coveredEdges, deg, hD]

/-- **Orthogonal mates.**  For `q > r ≥ 1` and every large admissible `n`, for every partial
Steiner system `F` on `n` points there is an `(n, q, r)`-Steiner system `𝒮` every block of which
meets every block of `F` in at most `r` points; in particular `𝒮` and `F` share no block. -/
theorem steiner_orthogonal_mate {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ F : Finset (Finset (Fin n)), IsPartialSteinerSystem q r F →
        ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧ 𝒮 ∩ F = ∅ ∧
          ∀ B₁ ∈ F, ∀ B₂ ∈ 𝒮, (B₁ ∩ B₂).card ≤ r := by
  obtain ⟨ε, hε, n₀, h⟩ := steiner_completion_avoiding hr hrq
  refine ⟨n₀, fun n hn hdiv F hF => ?_⟩
  obtain ⟨𝒮, h𝒮, -, hint, hcross⟩ := h n hn hdiv ∅ F (isPartialSteinerSystem_empty q r)
    (maxDegLE_coveredEdges_empty (by positivity)) hF
  refine ⟨𝒮, h𝒮, by simpa using hint, fun B₁ hB₁ B₂ hB₂ => hcross B₁ hB₁ ?_ B₂ (by simpa using hB₂)⟩
  simp [coveredEdges]

/-- **Disjoint mates.**  For `q > r ≥ 1` and every large admissible `n`, every
`(n, q, r)`-Steiner system `𝒮₁` has a *disjoint mate*: a Steiner system `𝒮₂` with no block in
common with `𝒮₁`; moreover any block of `𝒮₁` and any block of `𝒮₂` share at most `r` points. -/
theorem steiner_disjoint_mate {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮₁ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₁ →
      ∃ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₂ ∧ 𝒮₁ ∩ 𝒮₂ = ∅ ∧
        ∀ B₁ ∈ 𝒮₁, ∀ B₂ ∈ 𝒮₂, (B₁ ∩ B₂).card ≤ r := by
  obtain ⟨n₀, h⟩ := steiner_orthogonal_mate hr hrq
  refine ⟨n₀, fun n hn 𝒮₁ h𝒮₁ => ?_⟩
  have hdiv : DesignDivisibility n q r 1 :=
    isDivisible_completeRGraph_iff.1 (isSteinerSystem_iff_isDecomposition.1 h𝒮₁).isDivisible
  obtain ⟨𝒮₂, h𝒮₂, hint, hcross⟩ := h n hn hdiv 𝒮₁ (IsSteinerSystem.isPartial h𝒮₁)
  exact ⟨𝒮₂, h𝒮₂, by rw [inter_comm, hint], hcross⟩

/-- In a Steiner system `𝒮₁ ⊇ P`, the `r`-sets of a block outside `P` are not covered by `P`. -/
theorem cliqueEdges_disjoint_coveredEdges {n q r : ℕ} {𝒮₁ P : Finset (Finset (Fin n))}
    (h𝒮₁ : IsSteinerSystem q r 𝒮₁) (hP : P ⊆ 𝒮₁) {B : Finset (Fin n)} (hB : B ∈ 𝒮₁)
    (hBP : B ∉ P) : Disjoint (cliqueEdges r B) (coveredEdges r P) := by
  rw [disjoint_left]
  intro T hTB hTP
  obtain ⟨B', hB'P, hTB'⟩ := mem_biUnion.1 hTP
  have hT := (mem_powersetCard.1 hTB)
  have hT' := (mem_powersetCard.1 hTB')
  have hne : B ≠ B' := fun h => hBP (h ▸ hB'P)
  have h2 : ({B, B'} : Finset (Finset (Fin n))) ⊆ 𝒮₁.filter (fun Q => T ⊆ Q) := by
    intro Q hQ
    rcases mem_insert.1 hQ with rfl | hQ
    · exact mem_filter.2 ⟨hB, hT.1⟩
    · rw [mem_singleton.1 hQ]; exact mem_filter.2 ⟨hP hB'P, hT'.1⟩
  have := card_le_card h2
  rw [card_pair hne] at this
  have h1 := h𝒮₁.mult_eq T hT.2
  unfold cliqueMult at h1
  omega

/-- **Prescribed intersection with a given Steiner system.**  For `q > r ≥ 1` there are `ε > 0`
and `n₀` such that for every `n ≥ n₀`, every `(n, q, r)`-Steiner system `𝒮₁` and every subfamily
`P ⊆ 𝒮₁` whose covered `r`-graph has maximum `(r-1)`-degree at most `ε n`, there is a Steiner
system `𝒮₂` whose blocks in common with `𝒮₁` are exactly those of `P`; moreover a block of
`𝒮₁ \ P` and a block of `𝒮₂ \ P` always share at most `r` points. -/
theorem steiner_intersection_prescribed {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮₁ : Finset (Finset (Fin n)),
      IsSteinerSystem q r 𝒮₁ → ∀ P ⊆ 𝒮₁, MaxDegLE r (coveredEdges r P) (ε * n) →
        ∃ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₂ ∧ 𝒮₁ ∩ 𝒮₂ = P ∧
          ∀ B₁ ∈ 𝒮₁ \ P, ∀ B₂ ∈ 𝒮₂ \ P, (B₁ ∩ B₂).card ≤ r := by
  obtain ⟨ε, hε, n₀, h⟩ := steiner_completion_avoiding hr hrq
  refine ⟨ε, hε, n₀, fun n hn 𝒮₁ h𝒮₁ P hP hPdeg => ?_⟩
  have hdiv : DesignDivisibility n q r 1 :=
    isDivisible_completeRGraph_iff.1 (isSteinerSystem_iff_isDecomposition.1 h𝒮₁).isDivisible
  have hpart := IsSteinerSystem.isPartial h𝒮₁
  obtain ⟨𝒮₂, h𝒮₂, -, hint, hcross⟩ := h n hn hdiv P 𝒮₁ (hpart.mono hP) hPdeg hpart
  refine ⟨𝒮₂, h𝒮₂, by rw [inter_comm, hint, inter_eq_left.2 hP], fun B₁ hB₁ B₂ hB₂ => ?_⟩
  obtain ⟨hB₁S, hB₁P⟩ := mem_sdiff.1 hB₁
  exact hcross B₁ hB₁S (cliqueEdges_disjoint_coveredEdges h𝒮₁ hP hB₁S hB₁P) B₂ hB₂

/-- **Two Steiner systems with a prescribed intersection.**  For `q > r ≥ 1` there are `ε > 0`
and `n₀` such that for every admissible `n ≥ n₀` and every partial Steiner system `P` on `n`
points whose covered `r`-graph has maximum `(r-1)`-degree at most `ε n`, there are two
`(n, q, r)`-Steiner systems whose common blocks are exactly the blocks of `P`. -/
theorem steiner_intersection_exact {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ P : Finset (Finset (Fin n)), IsPartialSteinerSystem q r P →
        MaxDegLE r (coveredEdges r P) (ε * n) →
        ∃ 𝒮₁ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
          𝒮₁ ∩ 𝒮₂ = P := by
  obtain ⟨ε, hε, n₀, h⟩ := steiner_completion_avoiding hr hrq
  refine ⟨ε, hε, n₀, fun n hn hdiv P hP hPdeg => ?_⟩
  obtain ⟨𝒮₁, h𝒮₁, hP₁, -, -⟩ := h n hn hdiv P ∅ hP hPdeg (isPartialSteinerSystem_empty q r)
  obtain ⟨𝒮₂, h𝒮₂, -, hint, -⟩ := h n hn hdiv P 𝒮₁ hP hPdeg (IsSteinerSystem.isPartial h𝒮₁)
  exact ⟨𝒮₁, 𝒮₂, h𝒮₁, h𝒮₂, by rw [inter_comm, hint, inter_eq_left.2 hP₁]⟩

/-- Inside any `u`-set `U` there is a partial Steiner system with exactly `k` blocks as soon as
`2 binom(q,r)^2 k ≤ binom(u,r)` (greedy count `card_psFamily_ge`). -/
theorem exists_partialSteiner_card_eq {q r : ℕ} (hrq : r < q) {V : Type*} [DecidableEq V]
    (U : Finset V) (k : ℕ) (hk : 2 * q.choose r ^ 2 * k ≤ U.card.choose r) :
    ∃ P : Finset (Finset V), IsPartialSteinerSystem q r P ∧ P.card = k ∧ ∀ B ∈ P, B ⊆ U := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact ⟨∅, isPartialSteinerSystem_empty q r, rfl, by simp⟩
  have hc : 0 < q.choose r := Nat.choose_pos hrq.le
  have hqu : q ≤ U.card := by
    by_contra hlt
    have h1 : U.card.choose r ≤ q.choose r := Nat.choose_le_choose r (by omega)
    have h2 : q.choose r ≤ q.choose r ^ 2 := by nlinarith
    nlinarith
  set c := q.choose r
  set b := (U.card - r).choose (q - r)
  have hb : 0 < b := Nat.choose_pos (by omega)
  have hid : U.card.choose q * c = U.card.choose r * b := Nat.choose_mul hrq.le
  have hk' : 2 * k * (c * b) ≤ U.card.choose q := by
    refine Nat.le_of_mul_le_mul_left ?_ hc
    calc c * (2 * k * (c * b)) = (2 * c ^ 2 * k) * b := by ring
      _ ≤ U.card.choose r * b := Nat.mul_le_mul_right _ hk
      _ = c * U.card.choose q := by rw [← hid, mul_comm]
  have hcard := card_psFamily_ge hrq.le U k hk'
  have hpos : 0 < (psFamily q r k U).card :=
    lt_of_lt_of_le (pow_pos (Nat.mul_pos hc hb) k) hcard
  obtain ⟨P, hP⟩ := card_pos.1 hpos
  simp only [psFamily, mem_filter, mem_powersetCard] at hP
  obtain ⟨⟨hPU, hPk⟩, hPs⟩ := hP
  exact ⟨P, hPs, hPk, fun B hB => (mem_powersetCard.1 (hPU hB)).1⟩

/-- **Intersection numbers of Steiner systems.**  For `q > r ≥ 1` there are `ε > 0` and `n₀` such
that for every admissible `n ≥ n₀` and every `k` with `2 binom(q,r)^2 k ≤ binom(⌊ε n⌋, r)` there
are two `(n, q, r)`-Steiner systems with exactly `k` blocks in common. -/
theorem steiner_intersection_spectrum {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ k : ℕ, 2 * q.choose r ^ 2 * k ≤ (⌊ε * n⌋₊).choose r →
        ∃ 𝒮₁ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
          (𝒮₁ ∩ 𝒮₂).card = k := by
  obtain ⟨ε, hε, n₀, h⟩ := steiner_intersection_exact hr hrq
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, n₀, fun n hn hdiv k hk => ?_⟩
  have hε₀ : 0 ≤ min ε 1 := (lt_min hε one_pos).le
  have hun : ⌊min ε 1 * n⌋₊ ≤ (univ : Finset (Fin n)).card := by
    rw [card_univ, Fintype.card_fin]
    exact Nat.floor_le_of_le (by
      have := min_le_right ε 1
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith)
  obtain ⟨U, -, hU⟩ := exists_subset_card_eq hun
  obtain ⟨P, hP, hPk, hPU⟩ := exists_partialSteiner_card_eq hrq U k (by rw [hU]; exact hk)
  have hdeg : MaxDegLE r (coveredEdges r P) (ε * n) := by
    intro S hS
    have h1 := deg_le_card_of_edges_subset (H := coveredEdges r P) (U := U) (fun e he => by
      obtain ⟨B, hB, he⟩ := mem_biUnion.1 he
      exact ⟨(mem_powersetCard.1 he).1.trans (hPU B hB), (mem_powersetCard.1 he).2⟩) hS
    rw [hU] at h1
    calc (deg (coveredEdges r P) S : ℝ) ≤ ⌊min ε 1 * n⌋₊ := by exact_mod_cast h1
      _ ≤ min ε 1 * n := Nat.floor_le (by positivity)
      _ ≤ ε * n := by gcongr; exact min_le_left _ _
  obtain ⟨𝒮₁, 𝒮₂, h₁, h₂, hint⟩ := h n hn hdiv P hP hdeg
  exact ⟨𝒮₁, 𝒮₂, h₁, h₂, by rw [hint, hPk]⟩

/-- **Polynomial form of the intersection spectrum.**  For `q > r ≥ 1` there are `c > 0` and `n₀`
such that for every admissible `n ≥ n₀` and every `k ≤ c n^r` there are two
`(n, q, r)`-Steiner systems with exactly `k` blocks in common.  (Every Steiner system has
`binom(n,r)/binom(q,r) = Θ(n^r)` blocks, so this is the right order of magnitude.) -/
theorem steiner_intersection_spectrum_poly {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ k : ℕ, (k : ℝ) ≤ c * (n : ℝ) ^ r →
        ∃ 𝒮₁ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
          (𝒮₁ ∩ 𝒮₂).card = k := by
  obtain ⟨ε, hε, -, n₀, h⟩ := steiner_intersection_spectrum hr hrq
  set C : ℝ := (q.choose r : ℝ)
  have hC : 0 < C := by simp only [C]; exact_mod_cast Nat.choose_pos hrq.le
  have hfact : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (2 * r / ε)
  refine ⟨(ε / 2) ^ r / (r.factorial * (2 * C ^ 2)), by positivity, max n₀ n₁,
    fun n hn hdiv k hk => h n (le_of_max_le_left hn) hdiv k ?_⟩
  have hn1 : (n₁ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2r : 2 * (r : ℝ) ≤ ε * n := by
    have := (div_lt_iff₀ hε).1 (lt_of_lt_of_le hn₁ hn1)
    linarith
  set u := ⌊ε * n⌋₊
  have hu : ε * n < u + 1 := Nat.lt_floor_add_one _
  have hru : r ≤ u + 1 := by
    have : (r : ℝ) < u + 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
    exact_mod_cast this.le
  have hbase : ε * n / 2 ≤ ((u + 1 - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hru]; push_cast; linarith
  have hpow : (ε * n / 2) ^ r ≤ ((u + 1 - r : ℕ) : ℝ) ^ r :=
    pow_le_pow_left₀ (by positivity) hbase r
  have hchoose := Nat.pow_le_choose (α := ℝ) r u
  have key : (2 * q.choose r ^ 2 * k : ℝ) ≤ (u.choose r : ℝ) := by
    calc (2 * q.choose r ^ 2 * k : ℝ) = 2 * C ^ 2 * k := by simp [C]
      _ ≤ 2 * C ^ 2 * ((ε / 2) ^ r / (r.factorial * (2 * C ^ 2)) * (n : ℝ) ^ r) := by gcongr
      _ = (ε * n / 2) ^ r / r.factorial := by
          field_simp; ring
      _ ≤ ((u + 1 - r : ℕ) : ℝ) ^ r / r.factorial := by gcongr
      _ ≤ (u.choose r : ℝ) := hchoose
  exact_mod_cast key

/-- **Disjoint decompositions of dense graphs.**  For `q > r ≥ 1` there are `ε > 0` and `n₀` such
that every `K_q^r`-decomposition `𝒬₁` of a `K_q^r`-divisible `r`-graph `G` on `n ≥ n₀` vertices with
`δ_{r-1}(G) ≥ (1-ε) n` has a disjoint mate: a second decomposition `𝒬₂` of `G` with
`𝒬₁ ∩ 𝒬₂ = ∅`, any two cliques of which (one from each) share at most `r` vertices. -/
theorem decomposition_disjoint_mate {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)), IsRGraph r G →
      MinDegGE r G ((1 - ε) * n) → ∀ 𝒬₁ : Finset (Finset (Fin n)), IsDecomposition q r G 𝒬₁ →
        ∃ 𝒬₂ : Finset (Finset (Fin n)), IsDecomposition q r G 𝒬₂ ∧ 𝒬₁ ∩ 𝒬₂ = ∅ ∧
          ∀ Q₁ ∈ 𝒬₁, ∀ Q₂ ∈ 𝒬₂, (Q₁ ∩ Q₂).card ≤ r := by
  obtain ⟨n₀, ε, hε, h63⟩ := RefinedAbsorption.Pending.theorem_6_3 q r hr hrq
  refine ⟨ε, hε, n₀, fun n hn G hG hmin 𝒬₁ h𝒬₁ => ?_⟩
  have hpack : IsPacking q r G 𝒬₁ :=
    ⟨h𝒬₁.card_eq, fun Q hQ => h𝒬₁.cliqueEdges_subset hQ,
      fun e he => by rw [h𝒬₁.mult_eq e he]; split_ifs <;> omega⟩
  obtain ⟨𝒬₂, h𝒬₂, hcross⟩ := h63 n hn G hG h𝒬₁.isDivisible hmin 𝒬₁ hpack
  refine ⟨𝒬₂, h𝒬₂, eq_empty_of_forall_notMem fun Q hQ => ?_, hcross⟩
  obtain ⟨h1, h2⟩ := mem_inter.1 hQ
  have := hcross Q h1 Q h2
  rw [inter_self, h𝒬₂.card_eq Q h2] at this
  omega

/-- **Steiner triple systems.**  Every Steiner triple system of large order `n` has a disjoint
mate, and for every `k ≤ c n^2` there are two Steiner triple systems on `n` points sharing exactly
`k` triples (admissible `n` are those with `n ≡ 1, 3 (mod 6)`, see `kirkman`). -/
theorem sts_disjoint_mate_and_spectrum :
    (∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮₁ : Finset (Finset (Fin n)), IsSteinerSystem 3 2 𝒮₁ →
      ∃ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem 3 2 𝒮₂ ∧ 𝒮₁ ∩ 𝒮₂ = ∅) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n 3 2 1 →
      ∀ k : ℕ, (k : ℝ) ≤ c * (n : ℝ) ^ 2 →
        ∃ 𝒮₁ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem 3 2 𝒮₁ ∧ IsSteinerSystem 3 2 𝒮₂ ∧
          (𝒮₁ ∩ 𝒮₂).card = k) := by
  refine ⟨?_, steiner_intersection_spectrum_poly (by norm_num) (by norm_num)⟩
  obtain ⟨n₀, h⟩ := steiner_disjoint_mate (q := 3) (r := 2) (by norm_num) (by norm_num)
  exact ⟨n₀, fun n hn 𝒮₁ h𝒮₁ => (h n hn 𝒮₁ h𝒮₁).imp fun _ h => ⟨h.1, h.2.1⟩⟩

/-- Two distinct blocks of a partial Steiner system share fewer than `r` points. -/
theorem IsPartialSteinerSystem.inter_card_lt {q r : ℕ} {V : Type*} [DecidableEq V]
    {𝒮 : Finset (Finset V)} (h : IsPartialSteinerSystem q r 𝒮) {B B' : Finset V} (hB : B ∈ 𝒮)
    (hB' : B' ∈ 𝒮) (hne : B ≠ B') : (B ∩ B').card < r := by
  by_contra hlt
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (not_lt.1 hlt)
  have h2 : ({B, B'} : Finset (Finset V)) ⊆ 𝒮.filter (fun Q => T ⊆ Q) := by
    intro Q hQ
    rcases mem_insert.1 hQ with rfl | hQ
    · exact mem_filter.2 ⟨hB, hT.trans inter_subset_left⟩
    · rw [mem_singleton.1 hQ]; exact mem_filter.2 ⟨hB', hT.trans inter_subset_right⟩
  have := card_le_card h2
  rw [card_pair hne] at this
  have h1 := h.2 T hTc
  unfold cliqueMult at h1
  omega

/-- **Simple `2`-fold designs split into two Steiner systems.**  For `q > r ≥ 1` and every large
admissible `n` there is a `2`-fold design (every `r`-set in exactly two blocks) on `n` points
which is the disjoint union of two `(n, q, r)`-Steiner systems and in which any two distinct
blocks share at most `r` points. -/
theorem exists_two_fold_design_split {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∃ 𝒮₁ 𝒮₂ : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
        Disjoint 𝒮₁ 𝒮₂ ∧ IsDesign q r 2 (𝒮₁ ∪ 𝒮₂) ∧
        ∀ B ∈ 𝒮₁ ∪ 𝒮₂, ∀ B' ∈ 𝒮₁ ∪ 𝒮₂, B ≠ B' → (B ∩ B').card ≤ r := by
  obtain ⟨n₀, hex⟩ := steiner_exists hr hrq
  obtain ⟨n₁, hm⟩ := steiner_disjoint_mate hr hrq
  refine ⟨max n₀ n₁, fun n hn hdiv => ?_⟩
  obtain ⟨𝒮₁, h₁⟩ := hex n (le_of_max_le_left hn) hdiv
  obtain ⟨𝒮₂, h₂, hint, hcross⟩ := hm n (le_of_max_le_right hn) 𝒮₁ h₁
  have hdisj : Disjoint 𝒮₁ 𝒮₂ := disjoint_iff_inter_eq_empty.2 hint
  refine ⟨𝒮₁, 𝒮₂, h₁, h₂, hdisj, ⟨fun B hB => ?_, fun T hT => ?_⟩, ?_⟩
  · rcases mem_union.1 hB with hB | hB
    · exact h₁.card_eq B hB
    · exact h₂.card_eq B hB
  · unfold cliqueMult
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
    have e1 := h₁.mult_eq T hT
    have e2 := h₂.mult_eq T hT
    unfold cliqueMult at e1 e2
    omega
  · intro B hB B' hB' hne
    have p₁ := IsSteinerSystem.isPartial h₁
    have p₂ := IsSteinerSystem.isPartial h₂
    rcases mem_union.1 hB with hB | hB <;> rcases mem_union.1 hB' with hB' | hB'
    · exact (p₁.inter_card_lt hB hB' hne).le
    · exact hcross B hB B' hB'
    · rw [inter_comm]; exact hcross B' hB' B hB
    · exact (p₂.inter_card_lt hB hB' hne).le

/-- **Every finite partial Steiner system is the exact intersection of two Steiner systems.**
Let `q > r ≥ 1` and let `P` be a partial Steiner system on a finite set `α`.  For every
sufficiently large admissible `N` there are an injection `f : α ↪ Fin N` and two
`(N, q, r)`-Steiner systems whose common blocks are exactly the images of the blocks of `P`. -/
theorem partialSteiner_intersection_embedding {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {α : Type*}
    [Fintype α] [DecidableEq α] (P : Finset (Finset α)) (hP : IsPartialSteinerSystem q r P) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, DesignDivisibility N q r 1 →
      ∃ (f : α ↪ Fin N) (𝒮₁ 𝒮₂ : Finset (Finset (Fin N))),
        IsSteinerSystem q r 𝒮₁ ∧ IsSteinerSystem q r 𝒮₂ ∧
          𝒮₁ ∩ 𝒮₂ = P.map (mapEmbedding f).toEmbedding := by
  obtain ⟨ε, hε, n₀, hint⟩ := steiner_intersection_exact (q := q) hr hrq
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((Fintype.card α : ℝ) / ε)
  refine ⟨max n₀ (max N₁ (Fintype.card α)), fun N hN hdiv => ?_⟩
  have hαN : Fintype.card α ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  let f : α ↪ Fin N := (Fintype.equivFin α).toEmbedding.trans (Fin.castLEEmb hαN)
  set P' := P.map (mapEmbedding f).toEmbedding
  have hP' : IsPartialSteinerSystem q r P' := hP.map f
  have hdeg : MaxDegLE r (coveredEdges r P') (ε * N) := by
    intro S hS
    have h1 : deg (coveredEdges r P') S ≤ (univ.map f).card := by
      refine deg_le_card_of_edges_subset (fun e he => ?_) hS
      obtain ⟨Q, hQ, he⟩ := mem_biUnion.1 he
      obtain ⟨Q', -, rfl⟩ := mem_map.1 hQ
      refine ⟨(mem_powersetCard.1 he).1.trans ?_, (mem_powersetCard.1 he).2⟩
      intro x hx
      simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact mem_map_of_mem _ (mem_univ a)
    rw [card_map, card_univ] at h1
    have h2 : (Fintype.card α : ℝ) ≤ ε * N := by
      have hN1 : (N₁ : ℝ) ≤ N := by
        exact_mod_cast le_trans (le_max_left _ _) (le_of_max_le_right hN)
      have := (div_lt_iff₀ hε).1 (lt_of_lt_of_le hN₁ hN1)
      linarith
    exact le_trans (by exact_mod_cast h1) h2
  obtain ⟨𝒮₁, 𝒮₂, h₁, h₂, h12⟩ := hint N (le_of_max_le_left hN) hdiv P' hP' hdeg
  exact ⟨f, 𝒮₁, 𝒮₂, h₁, h₂, h12⟩

end RefinedAbsorption.Extensions
