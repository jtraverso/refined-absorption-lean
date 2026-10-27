module
public import RefinedAbsorption.Extensions.PolynomialTools

/-!
# Scheduling a Nash–Williams triangle decomposition in `Δ(G)/2 + o(Δ(G))` rounds

Taking the two external endpoints `PippengerSpencerPolynomial` (`hPSPoly`) and
`NashWilliamsExternal` (`hNW`) as explicit hypotheses (they are **not** proved in this project),
we prove `nash_williams_scheduled_decomposition`: there are `0 < γ < 1` and `n₀` such that every
triangle-divisible graph `G` on `n ≥ n₀` vertices with `3 n ≤ 4 δ(G)` has an (exact) triangle
decomposition `T` whose triangles can be split into `m` rounds of vertex-disjoint triangles with
`Δ(G)/2 ≤ m ≤ Δ(G)/2 + (Δ(G)/2)^{1-γ}`.

The reusable statements for a *given* triangle decomposition are
`two_mul_degree_of_isTriangleDecomposition` (`2 · deg_T(v) = deg_G(v)`) and
`codegree_le_one_of_isTriangleDecomposition`.
-/

@[expose] public section

namespace RefinedAbsorption.External

open Finset PippengerSpencer NashWilliams

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A triangle decomposition is a `3`-uniform hypergraph. -/
theorem isUniform_of_isTriangleDecomposition {G : SimpleGraph V} {T : Finset (Finset V)}
    (hT : IsTriangleDecomposition G T) : IsUniform T 3 :=
  fun t ht => (hT.1 t ht).card_eq

omit [Fintype V] [DecidableEq V] in
/-- Two distinct vertices of a triangle of `G` are adjacent. -/
theorem adj_of_mem_triangle {G : SimpleGraph V} {t : Finset V} (ht : IsTriangle G t)
    {u v : V} (hu : u ∈ t) (hv : v ∈ t) (huv : u ≠ v) : G.Adj u v :=
  ht.isClique (mem_coe.2 hu) (mem_coe.2 hv) huv

omit [Fintype V] in
/-- **Codegrees of a triangle decomposition are at most one.** -/
theorem codegree_le_one_of_isTriangleDecomposition {G : SimpleGraph V} {T : Finset (Finset V)}
    (hT : IsTriangleDecomposition G T) {u v : V} (huv : u ≠ v) : codegree T u v ≤ 1 := by
  rw [codegree, card_le_one]
  intro a ha b hb
  rw [mem_filter] at ha hb
  have hadj := adj_of_mem_triangle (hT.1 a ha.1) ha.2.1 ha.2.2 huv
  exact (hT.2 u v hadj).unique ⟨ha.1, ha.2.1, ha.2.2⟩ ⟨hb.1, hb.2.1, hb.2.2⟩

/-- **Degrees of a triangle decomposition:** every vertex `v` lies in exactly `deg_G(v)/2`
triangles of the decomposition. -/
theorem two_mul_degree_of_isTriangleDecomposition {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Finset (Finset V)} (hT : IsTriangleDecomposition G T) (v : V) :
    2 * degree T v = G.degree v := by
  have hcount : ∀ t ∈ T.filter (fun e => v ∈ e), (t.erase v).card = 2 := by
    intro t ht
    rw [mem_filter] at ht
    rw [card_erase_of_mem ht.2, (hT.1 t ht.1).card_eq]
  have h1 : 2 * degree T v = ∑ t ∈ T.filter (fun e => v ∈ e), (t.erase v).card := by
    rw [sum_congr rfl hcount, sum_const, smul_eq_mul, degree, mul_comm]
  have h2 : ∑ t ∈ T.filter (fun e => v ∈ e), (t.erase v).card
      = ∑ w : V, ∑ t ∈ T.filter (fun e => v ∈ e), (if w ∈ t.erase v then 1 else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  have h3 : ∀ w : V, (∑ t ∈ T.filter (fun e => v ∈ e), (if w ∈ t.erase v then 1 else 0))
      = if G.Adj v w then 1 else 0 := by
    intro w
    rw [← card_filter, filter_filter]
    split_ifs with hadj
    · rw [card_eq_one]
      obtain ⟨t, ⟨htT, hvt, hwt⟩, huniq⟩ := hT.2 v w hadj
      refine ⟨t, ?_⟩
      ext s
      simp only [mem_filter, mem_erase, mem_singleton]
      constructor
      · rintro ⟨hsT, hvs, -, hws⟩
        exact huniq s ⟨hsT, hvs, hws⟩
      · rintro rfl
        exact ⟨htT, hvt, (G.ne_of_adj hadj).symm, hwt⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro s hsT ⟨hvs, hws⟩
      rw [mem_erase] at hws
      exact hadj (adj_of_mem_triangle (hT.1 s hsT) hvs hws.2 (Ne.symm hws.1))
  rw [h1, h2, sum_congr rfl fun w _ => h3 w, ← card_filter,
    ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

/-- **Nash–Williams decompositions can be scheduled in `Δ(G)/2 + o(Δ(G))` rounds**
(conditional on the external endpoints `hPSPoly` and `hNW`).  There are `0 < γ < 1` and `n₀`
such that every triangle-divisible graph `G` on `n ≥ n₀` vertices with `3 n ≤ 4 δ(G)` has a
triangle decomposition `T` (every edge of `G` in exactly one triangle of `T`) and a colouring of
`T` with `m` colours, triangles of equal colour being vertex-disjoint, where
`Δ(G)/2 ≤ m ≤ Δ(G)/2 + (Δ(G)/2)^{1-γ}` and `Δ(G)` is the maximum degree of `G`. -/
theorem nash_williams_scheduled_decomposition (hPSPoly : PippengerSpencerPolynomial)
    (hNW : NashWilliamsExternal) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → IsTriangleDivisible G → 3 * Fintype.card V ≤ 4 * G.minDegree →
      ∃ T : Finset (Finset V), IsTriangleDecomposition G T ∧
        ∃ (m : ℕ) (c : Finset V → Fin m), IsProperEdgeColouring T m c ∧
          (G.maxDegree : ℝ) / 2 ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (G.maxDegree : ℝ) / 2 + ((G.maxDegree : ℝ) / 2) ^ (1 - γ) := by
  obtain ⟨γ₀, hγ₀, D₀, hP⟩ := hPSPoly 3 (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := hNW
  obtain ⟨D₁, hD₁⟩ := eventually_mul_sq_le_exp_rpow hγ₀ 3
  refine ⟨min γ₀ (1 / 2), lt_min hγ₀ (by norm_num), by
    have := min_le_right γ₀ (1 / 2 : ℝ); linarith, N + 3 + ⌈3 * (|D₀| + |D₁|)⌉₊, ?_⟩
  intro V _ _ G _ hn hdiv hmin
  set n := Fintype.card V with hn_def
  have hn3 : 3 ≤ n := by omega
  have hnR : (n : ℝ) ≥ 3 * (|D₀| + |D₁|) + 3 := by
    have h1 : (N + 3 + ⌈3 * (|D₀| + |D₁|)⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    have h2 := Nat.le_ceil (3 * (|D₀| + |D₁|))
    have h3 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  haveI : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨T, hT⟩ := hN V G (by omega) hdiv hmin
  refine ⟨T, hT, ?_⟩
  set D : ℝ := (G.maxDegree : ℝ) / 2 with hD_def
  obtain ⟨v₀, hv₀⟩ := G.exists_maximal_degree_vertex
  -- `D ≥ 3n/8`
  have hminmax : G.minDegree ≤ G.maxDegree := (G.minDegree_le_degree v₀).trans (G.degree_le_maxDegree v₀)
  have hDn : 3 * (n : ℝ) ≤ 8 * D := by
    have : 3 * n ≤ 4 * G.maxDegree := hmin.trans (by omega)
    have : (3 * n : ℝ) ≤ 4 * G.maxDegree := by exact_mod_cast this
    rw [hD_def]; linarith
  have hD1 : 1 ≤ D := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hDD₀ : D₀ ≤ D := by
    have := le_abs_self D₀; have := abs_nonneg D₁; nlinarith
  have hDD₁ : D₁ ≤ D := by
    have := le_abs_self D₁; have := abs_nonneg D₀; nlinarith
  -- degrees and codegrees of `T`
  have hdegT : ∀ v, (degree T v : ℝ) ≤ D := by
    intro v
    have h := two_mul_degree_of_isTriangleDecomposition hT v
    have h' : (2 * degree T v : ℝ) = G.degree v := by exact_mod_cast h
    have : (G.degree v : ℝ) ≤ G.maxDegree := by exact_mod_cast G.degree_le_maxDegree v
    rw [hD_def]; linarith
  have hcodT : ∀ u v, u ≠ v → (codegree T u v : ℝ) ≤ D ^ (1 - (1 / 2 : ℝ)) := by
    intro u v huv
    have h1 : (codegree T u v : ℝ) ≤ 1 := by
      exact_mod_cast codegree_le_one_of_isTriangleDecomposition hT huv
    exact h1.trans (Real.one_le_rpow hD1 (by norm_num))
  -- the number of triangles
  have hcardT : (T.card : ℝ) ≤ Real.exp (D ^ γ₀) := by
    have hsum := uniform_card_mul_eq_sum_degree (isUniform_of_isTriangleDecomposition hT)
    have hsumR : (3 * T.card : ℝ) = ∑ v, (degree T v : ℝ) := by exact_mod_cast hsum
    have hle : ∑ v, (degree T v : ℝ) ≤ ∑ _v : V, D := sum_le_sum fun v _ => hdegT v
    rw [sum_const, card_univ, nsmul_eq_mul, ← hn_def] at hle
    have hD0 : 0 ≤ D := by linarith
    have : (T.card : ℝ) ≤ 3 * D ^ 2 := by nlinarith
    exact this.trans (hD₁ D hDD₁)
  obtain ⟨m, c, hm, hc⟩ := hP V T D hDD₀ (isUniform_of_isTriangleDecomposition hT) hdegT hcodT
    hcardT
  refine ⟨m, c, hc, ?_, ?_⟩
  · have h := two_mul_degree_of_isTriangleDecomposition hT v₀
    have hle := degree_le_of_isProperEdgeColouring hc v₀
    have h' : (2 * degree T v₀ : ℝ) = G.maxDegree := by rw [hv₀]; exact_mod_cast h
    have hle' : (degree T v₀ : ℝ) ≤ m := by exact_mod_cast hle
    linarith
  · exact hm.trans (by linarith [rpow_error_mono hD1 (min_le_left γ₀ (1 / 2))])

end RefinedAbsorption.External
