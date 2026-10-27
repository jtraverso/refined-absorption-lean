module
public import RequestProject.Extensions.Embedding
public import RequestProject.Extensions.CountCore

/-!
# Optimal packings and coverings of `K_n^r` for every `n` (strong Erdős–Hanani)

For fixed `q > r ≥ 1` and **every** large `n` (not only the admissible ones):

* `optimal_packing`: there is a partial Steiner system (a `K_q^r`-packing of `K_n^r`) whose
  uncovered `r`-graph `L` has bounded maximum `(r-1)`-degree, `Δ_{r-1}(L) ≤ K`; hence
  `binom(q,r)·|P| + |L| = binom(n,r)` and `r·|L| ≤ K·binom(n, r-1)`;
* `optimal_covering`: there is a covering of all `r`-sets by `q`-sets with
  `binom(q,r)·|𝒞| ≤ binom(n,r) + K·n^{r-1}`;
* `packing_leftover_lower`, `covering_excess_lower`: if `q - r + 1 ∤ n - r + 1`, every packing
  leaves at least `binom(n, r-1)/r` uncovered `r`-sets, and every covering has total excess at
  least `binom(n, r-1)/r`; so the error order `n^{r-1}` is best possible.

The Erdős–Hanani conjecture, proved by Rödl's nibble, gives packings and coverings with error
`o(n^r)`; here the error is `O(n^{r-1})` with bounded leftover degree.  Proof: take an admissible
`N` with `n < N ≤ n + M` (`designDivisibility_progression`), an `(N, q, r)`-Steiner system, and
keep the blocks inside `n` of the `N` points (packing), or project the extra points (covering).
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset RefinedAbsorption.Original2024

/-- The uncovered `r`-sets of a family `P` of blocks on `Fin n`. -/
def leftover (n r : ℕ) (P : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  completeRGraph (Fin n) r \ coveredEdges r P

/-- `𝒞` is a covering of the `r`-sets of `Fin n` by `q`-sets. -/
def IsCovering (q r : ℕ) {n : ℕ} (𝒞 : Finset (Finset (Fin n))) : Prop :=
  (∀ C ∈ 𝒞, C.card = q) ∧ ∀ T : Finset (Fin n), T.card = r → ∃ C ∈ 𝒞, T ⊆ C

/-- Steiner systems exist for all large admissible `n`, for every `q > r ≥ 1`. -/
theorem steiner_exists {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 := by
  obtain ⟨ε, hε, n₀, h⟩ := decomposition_complete_minus_sparse (q := q) hr hrq
  refine ⟨n₀, fun n hn hdiv => ?_⟩
  have hdivK : IsDivisible q r (completeRGraph (Fin n) r) := isDivisible_completeRGraph_iff.2 hdiv
  obtain ⟨𝒮, h𝒮⟩ := h n hn ∅ (empty_subset _)
    (fun S _ => by simp [deg]; positivity) (by rwa [sdiff_empty])
  rw [sdiff_empty] at h𝒮
  exact ⟨𝒮, isSteinerSystem_iff_isDecomposition.2 h𝒮⟩

theorem admModulus_pos {q r : ℕ} (hrq : r < q) : 0 < admModulus q r := by
  unfold admModulus
  refine Nat.mul_pos (Nat.factorial_pos _) (prod_pos fun i hi => Nat.choose_pos ?_)
  have := mem_range.1 hi; omega

/-- An admissible order in `(n, n + M]`. -/
theorem exists_admissible_near {q r : ℕ} (hrq : r < q) (n : ℕ) (hn : q ≤ n) :
    ∃ N, n < N ∧ N ≤ n + admModulus q r ∧ DesignDivisibility N q r 1 := by
  have hM := admModulus_pos hrq
  set M := admModulus q r
  refine ⟨q + ((n - q) / M + 1) * M, ?_, ?_, designDivisibility_progression hrq _⟩
  · have := Nat.lt_div_mul_add (a := n - q) hM
    rw [add_mul, one_mul]
    generalize (n - q) / M * M = u at *
    omega
  · have := Nat.div_mul_le_self (n - q) M
    rw [add_mul, one_mul]
    generalize (n - q) / M * M = u at *
    omega

/-- The blocks of `𝒮` (on `Fin N`) lying inside the image of `f : Fin n ↪ Fin N`, pulled back. -/
noncomputable def restrictBlocks (q : ℕ) {n N : ℕ} (f : Fin n ↪ Fin N)
    (𝒮 : Finset (Finset (Fin N))) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard q).filter (fun B => B.map f ∈ 𝒮)

theorem restrictBlocks_isPartial {q r n N : ℕ} (f : Fin n ↪ Fin N)
    {𝒮 : Finset (Finset (Fin N))} (h𝒮 : IsSteinerSystem q r 𝒮) :
    IsPartialSteinerSystem q r (restrictBlocks q f 𝒮) := by
  refine ⟨fun B hB => (mem_powersetCard.1 (mem_filter.1 hB).1).2, fun T hT => ?_⟩
  have h1 := h𝒮.mult_eq (T.map f) (by rw [card_map, hT])
  rw [← h1]
  unfold cliqueMult
  refine card_le_card_of_injOn (fun B => B.map f) ?_ ?_
  · intro B hB
    rw [mem_coe, mem_filter] at hB ⊢
    exact ⟨(mem_filter.1 hB.1).2, map_subset_map.2 hB.2⟩
  · intro B _ B' _ h
    exact map_injective f h

theorem restrictBlocks_leftover_deg {q r n N : ℕ} (f : Fin n ↪ Fin N)
    {𝒮 : Finset (Finset (Fin N))} (h𝒮 : IsSteinerSystem q r 𝒮)
    (S : Finset (Fin n)) (hS : S.card + 1 = r) :
    deg (leftover n r (restrictBlocks q f 𝒮)) S ≤ q.choose r * (N - n) := by
  classical
  set P := restrictBlocks q f 𝒮
  set bad := 𝒮.filter (fun B => S.map f ⊆ B ∧ ¬ B ⊆ univ.map f)
  have step2 : ((leftover n r P).filter (fun e => S ⊆ e)).map (mapEmbedding f).toEmbedding ⊆
      bad.biUnion (fun B => B.powersetCard r) := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := mem_map.1 he'
    obtain ⟨heL, hSe⟩ := mem_filter.1 he
    obtain ⟨heK, hecov⟩ := mem_sdiff.1 heL
    have hec : e.card = r := (mem_powersetCard.1 heK).2
    have h1 := h𝒮.mult_eq (e.map f) (by rw [card_map, hec])
    obtain ⟨B, hB⟩ := card_pos.1 (show 0 < cliqueMult 𝒮 (e.map f) by omega)
    obtain ⟨hB𝒮, heB⟩ := mem_filter.1 hB
    simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
    refine mem_biUnion.2 ⟨B, mem_filter.2 ⟨hB𝒮, (map_subset_map.2 hSe).trans heB, ?_⟩,
      mem_powersetCard.2 ⟨heB, by rw [card_map, hec]⟩⟩
    intro hBsub
    obtain ⟨B', -, rfl⟩ := subset_map_iff.1 hBsub
    apply hecov
    refine mem_biUnion.2 ⟨B', ?_, mem_powersetCard.2 ⟨(map_subset_map).1 heB, hec⟩⟩
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, ?_⟩, hB𝒮⟩
    rw [← card_map f]; exact h𝒮.card_eq _ hB𝒮
  have step3 : bad ⊆ (univ \ univ.map f).biUnion
      (fun y => 𝒮.filter (fun B => insert y (S.map f) ⊆ B)) := by
    intro B hB
    obtain ⟨hB𝒮, hSB, hnot⟩ := mem_filter.1 hB
    obtain ⟨y, hyB, hy⟩ := not_subset.1 hnot
    exact mem_biUnion.2 ⟨y, mem_sdiff.2 ⟨mem_univ _, hy⟩,
      mem_filter.2 ⟨hB𝒮, insert_subset hyB hSB⟩⟩
  have hbad : bad.card ≤ N - n := by
    refine (card_le_card step3).trans (card_biUnion_le.trans ?_)
    have : ∑ y ∈ univ \ univ.map f, (𝒮.filter (fun B => insert y (S.map f) ⊆ B)).card
        = ∑ y ∈ univ \ univ.map f, 1 := by
      refine sum_congr rfl fun y hy => ?_
      have hyS : y ∉ S.map f := fun h => (mem_sdiff.1 hy).2
        (map_subset_map.2 (subset_univ S) h)
      exact h𝒮.mult_eq _ (by rw [card_insert_of_notMem hyS, card_map]; omega)
    rw [this, sum_const, smul_eq_mul, mul_one, card_sdiff_of_subset (subset_univ _), card_map,
      card_univ, card_univ, Fintype.card_fin, Fintype.card_fin]
  have h4 := card_le_card step2
  rw [card_map] at h4
  refine h4.trans (card_biUnion_le.trans ?_)
  calc ∑ B ∈ bad, (B.powersetCard r).card = ∑ B ∈ bad, q.choose r := by
        refine sum_congr rfl fun B hB => ?_
        rw [card_powersetCard, h𝒮.card_eq B (mem_filter.1 hB).1]
    _ = q.choose r * bad.card := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ q.choose r * (N - n) := Nat.mul_le_mul_left _ hbad

/-- **Optimal packings.** -/
theorem optimal_packing {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ K n₀ : ℕ, ∀ n ≥ n₀, ∃ P : Finset (Finset (Fin n)), IsPartialSteinerSystem q r P ∧
      ∀ S : Finset (Fin n), S.card + 1 = r → deg (leftover n r P) S ≤ K := by
  obtain ⟨n₁, hex⟩ := steiner_exists hr hrq
  refine ⟨q.choose r * admModulus q r, max n₁ q, fun n hn => ?_⟩
  obtain ⟨N, hnN, hNn, hdiv⟩ := exists_admissible_near hrq n (le_of_max_le_right hn)
  obtain ⟨𝒮, h𝒮⟩ := hex N (by have := le_of_max_le_left hn; omega) hdiv
  let f : Fin n ↪ Fin N := Fin.castLEEmb hnN.le
  refine ⟨restrictBlocks q f 𝒮, restrictBlocks_isPartial f h𝒮, fun S hS => ?_⟩
  exact (restrictBlocks_leftover_deg f h𝒮 S hS).trans
    (Nat.mul_le_mul_left _ (by omega))

/-! ### Counting consequences -/

/-- `∑_{|S| = r-1} ∑_{e ⊇ S, |e| = r} φ(e) = r · ∑_{|e| = r} φ(e)`. -/
theorem sum_sub_super {n r : ℕ} (hr : 1 ≤ r) (φ : Finset (Fin n) → ℕ) :
    ∑ S ∈ (univ : Finset (Fin n)).powersetCard (r - 1),
        ∑ e ∈ ((univ : Finset (Fin n)).powersetCard r).filter (fun e => S ⊆ e), φ e
      = r * ∑ e ∈ (univ : Finset (Fin n)).powersetCard r, φ e := by
  have := sum_weight_double_count r (r - 1) ((univ : Finset (Fin n)).powersetCard r)
    (fun Q hQ => (mem_powersetCard.1 hQ).2) φ ∅ (by simp)
  simp only [empty_subset, filter_true, card_empty, Nat.sub_zero, smul_eq_mul] at this
  rw [this, Nat.choose_symm hr, Nat.choose_one_right]

/-- The number of `r`-sets covered by a partial Steiner system `P` is `binom(q, r) |P|`. -/
theorem IsPartialSteinerSystem.card_coveredEdges {q r : ℕ} {V : Type*} [DecidableEq V]
    [Fintype V] {P : Finset (Finset V)} (hP : IsPartialSteinerSystem q r P) :
    (coveredEdges r P).card = q.choose r * P.card := by
  have := hP.isDecomposition.deg_eq ∅ (by simp)
  simpa [deg, cliqueMult] using this

/-- `binom(q, r) · |P| + |L| = binom(n, r)` for a packing `P` with leftover `L`. -/
theorem packing_count {q r n : ℕ} {P : Finset (Finset (Fin n))}
    (hP : IsPartialSteinerSystem q r P) :
    q.choose r * P.card + (leftover n r P).card = n.choose r := by
  rw [leftover, card_sdiff_of_subset (coveredEdges_subset_complete P), ← hP.card_coveredEdges]
  have h1 := card_le_card (coveredEdges_subset_complete (r := r) P)
  have h2 : (completeRGraph (Fin n) r).card = n.choose r := by simp [completeRGraph]
  omega

/-- `r · |L| = ∑_{|S| = r-1} deg_L(S)` for an `r`-graph `L ⊆ K_n^r`. -/
theorem sum_deg_eq {n r : ℕ} (hr : 1 ≤ r) {L : Finset (Finset (Fin n))}
    (hL : L ⊆ completeRGraph (Fin n) r) :
    ∑ S ∈ (univ : Finset (Fin n)).powersetCard (r - 1), deg L S = r * L.card := by
  have := sum_sub_super hr (fun e => if e ∈ L then 1 else 0)
  simp only [sum_boole, Nat.cast_id] at this
  rw [show ((univ : Finset (Fin n)).powersetCard r).filter (fun e => e ∈ L) = L by
    ext e; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hL h, h⟩⟩] at this
  rw [← this]
  refine sum_congr rfl fun S hS => ?_
  rw [deg]
  congr 1
  ext e
  simp only [mem_filter]
  exact ⟨fun h => ⟨⟨hL h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-- **Optimal packings, counting form (strong Erdős–Hanani).**  For `q > r ≥ 1` there are
`K` and `n₀` such that for **every** `n ≥ n₀` there is a partial Steiner system `P` on `n`
points whose uncovered `r`-graph `L` satisfies `Δ_{r-1}(L) ≤ K`,
`binom(q, r)·|P| + |L| = binom(n, r)` and `r·|L| ≤ K·binom(n, r-1)`. -/
theorem optimal_packing_count {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ K n₀ : ℕ, ∀ n ≥ n₀, ∃ P : Finset (Finset (Fin n)), IsPartialSteinerSystem q r P ∧
      (∀ S : Finset (Fin n), S.card + 1 = r → deg (leftover n r P) S ≤ K) ∧
      q.choose r * P.card + (leftover n r P).card = n.choose r ∧
      r * (leftover n r P).card ≤ K * n.choose (r - 1) := by
  obtain ⟨K, n₀, h⟩ := optimal_packing hr hrq
  refine ⟨K, n₀, fun n hn => ?_⟩
  obtain ⟨P, hP, hdeg⟩ := h n hn
  refine ⟨P, hP, hdeg, packing_count hP, ?_⟩
  rw [← sum_deg_eq hr (L := leftover n r P) (by unfold leftover; exact sdiff_subset)]
  calc ∑ S ∈ (univ : Finset (Fin n)).powersetCard (r - 1), deg (leftover n r P) S
      ≤ ∑ S ∈ (univ : Finset (Fin n)).powersetCard (r - 1), K :=
        sum_le_sum fun S hS => hdeg S (by rw [(mem_powersetCard.1 hS).2]; omega)
    _ = K * n.choose (r - 1) := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-! ### Optimal coverings -/

theorem choose_add_le (n s : ℕ) : ∀ M : ℕ, (n + M).choose (s + 1) ≤
    n.choose (s + 1) + M * (n + M) ^ s
  | 0 => by simp
  | M + 1 => by
    have ih := choose_add_le n s M
    rw [show n + (M + 1) = (n + M) + 1 by ring, Nat.choose_succ_succ']
    have h1 : (n + M).choose s ≤ (n + M) ^ s := Nat.choose_le_pow _ _
    have h2 : (n + M) ^ s ≤ (n + M + 1) ^ s := Nat.pow_le_pow_left (by omega) _
    have h3 : M * (n + M) ^ s ≤ M * (n + M + 1) ^ s := Nat.mul_le_mul_left _ h2
    nlinarith

/-- The total number of blocks of a Steiner system: `binom(q, r) |𝒮| = binom(N, r)`. -/
theorem steiner_card_mul {q r N : ℕ} {𝒮 : Finset (Finset (Fin N))}
    (h𝒮 : IsSteinerSystem q r 𝒮) : q.choose r * 𝒮.card = N.choose r := by
  have := (isSteinerSystem_iff_isDecomposition.1 h𝒮).deg_eq ∅ (by simp)
  rw [deg_completeRGraph (by simp)] at this
  simpa [cliqueMult] using this.symm

/-- A `q`-set containing `X`, if `|X| ≤ q ≤ n`. -/
noncomputable def padTo (q : ℕ) {n : ℕ} (X : Finset (Fin n)) : Finset (Fin n) :=
  if h : X.card ≤ q ∧ q ≤ n then
    Classical.choose (exists_subsuperset_card_eq (subset_univ X) h.1
      (by rw [card_univ, Fintype.card_fin]; exact h.2))
  else X

theorem padTo_spec {q n : ℕ} {X : Finset (Fin n)} (hX : X.card ≤ q) (hqn : q ≤ n) :
    X ⊆ padTo q X ∧ (padTo q X).card = q := by
  unfold padTo
  rw [dif_pos ⟨hX, hqn⟩]
  have := Classical.choose_spec (exists_subsuperset_card_eq (subset_univ X) hX
      (by rw [card_univ, Fintype.card_fin]; exact hqn))
  exact ⟨this.1, this.2.2⟩

/-- **Optimal coverings.**  For `q > r ≥ 1` there are `K` and `n₀` such that for **every**
`n ≥ n₀` the `r`-sets of an `n`-set can be covered by a family `𝒞` of `q`-sets with
`binom(q, r)·|𝒞| ≤ binom(n, r) + K·n^{r-1}`. -/
theorem optimal_covering {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ K n₀ : ℕ, ∀ n ≥ n₀, ∃ 𝒞 : Finset (Finset (Fin n)), IsCovering q r 𝒞 ∧
      q.choose r * 𝒞.card ≤ n.choose r + K * n ^ (r - 1) := by
  classical
  obtain ⟨n₁, hex⟩ := steiner_exists hr hrq
  set M := admModulus q r
  refine ⟨M * 2 ^ (r - 1), max n₁ (max q M), fun n hn => ?_⟩
  have hqn : q ≤ n := le_trans (le_max_left _ _) (le_of_max_le_right hn)
  have hMn : M ≤ n := le_trans (le_max_right _ _) (le_of_max_le_right hn)
  obtain ⟨N, hnN, hNn, hdiv⟩ := exists_admissible_near hrq n hqn
  obtain ⟨𝒮, h𝒮⟩ := hex N (by have := le_of_max_le_left hn; omega) hdiv
  have hn0 : 0 < n := by omega
  let g : Fin N → Fin n := fun i => if h : i.val < n then ⟨i.val, h⟩ else ⟨0, hn0⟩
  let f : Fin n ↪ Fin N := Fin.castLEEmb hnN.le
  have hgf : ∀ a, g (f a) = a := by
    intro a; simp [g, f, a.isLt]
  refine ⟨𝒮.image (fun B => padTo q (B.image g)), ⟨?_, ?_⟩, ?_⟩
  · intro C hC
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hC
    exact (padTo_spec ((card_image_le).trans (h𝒮.card_eq B hB).le) hqn).2
  · intro T hT
    have h1 := h𝒮.mult_eq (T.map f) (by rw [card_map, hT])
    obtain ⟨B, hB⟩ := card_pos.1 (show 0 < cliqueMult 𝒮 (T.map f) by omega)
    obtain ⟨hB𝒮, hTB⟩ := mem_filter.1 hB
    refine ⟨_, mem_image_of_mem _ hB𝒮, ?_⟩
    refine subset_trans ?_ (padTo_spec ((card_image_le).trans (h𝒮.card_eq B hB𝒮).le) hqn).1
    intro a ha
    exact mem_image.2 ⟨f a, hTB (mem_map_of_mem f ha), hgf a⟩
  · have hc := steiner_card_mul h𝒮
    have h1 : (𝒮.image (fun B => padTo q (B.image g))).card ≤ 𝒮.card := card_image_le
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have h2 : N.choose (s + 1) ≤ (n + M).choose (s + 1) := Nat.choose_le_choose _ hNn
    have h3 := choose_add_le n s M
    have h4 : (n + M) ^ s ≤ 2 ^ s * n ^ s := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    simp only [Nat.add_sub_cancel]
    calc q.choose (s + 1) * (𝒮.image (fun B => padTo q (B.image g))).card
        ≤ q.choose (s + 1) * 𝒮.card := Nat.mul_le_mul_left _ h1
      _ = N.choose (s + 1) := hc
      _ ≤ n.choose (s + 1) + M * (n + M) ^ s := h2.trans h3
      _ ≤ n.choose (s + 1) + M * 2 ^ s * n ^ s := by
          rw [mul_assoc]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h4) _

/-! ### Lower bounds: the order `n^{r-1}` is best possible -/

/-- **Every packing leaves `≥ binom(n, r-1)/r` uncovered `r`-sets** when
`q - r + 1 ∤ n - r + 1`: every `(r-1)`-set lies in an uncovered `r`-set. -/
theorem packing_leftover_lower {q r n : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (hrn : r ≤ n)
    (hnd : ¬ (q - r + 1) ∣ (n - r + 1)) {P : Finset (Finset (Fin n))}
    (hP : IsPartialSteinerSystem q r P) :
    (∀ S : Finset (Fin n), S.card + 1 = r → 1 ≤ deg (leftover n r P) S) ∧
      n.choose (r - 1) ≤ r * (leftover n r P).card := by
  have hS1 : ∀ S : Finset (Fin n), S.card + 1 = r → 1 ≤ deg (leftover n r P) S := by
    intro S hS
    have hK := deg_completeRGraph (n := n) (r := r) (S := S) (by omega)
    have hcov := hP.isDecomposition.deg_eq S (by omega)
    have hsub := coveredEdges_subset_complete (r := r) P
    rw [leftover, RefinedAbsorption.Original2024.deg_sdiff_of_subset hsub, hK, hcov,
      show r - S.card = 1 by omega, Nat.choose_one_right, Nat.choose_one_right]
    by_contra h0
    have hle : deg (coveredEdges r P) S ≤ deg (completeRGraph (Fin n) r) S :=
      card_le_card (filter_subset_filter _ hsub)
    rw [hK, hcov, show r - S.card = 1 by omega, Nat.choose_one_right,
      Nat.choose_one_right] at hle
    apply hnd
    refine ⟨cliqueMult P S, ?_⟩
    rw [show q - r + 1 = q - S.card by omega, show n - r + 1 = n - S.card by omega]
    omega
  refine ⟨hS1, ?_⟩
  rw [← sum_deg_eq hr (L := leftover n r P) (by unfold leftover; exact sdiff_subset)]
  calc n.choose (r - 1) = ∑ S ∈ (univ : Finset (Fin n)).powersetCard (r - 1), 1 := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    _ ≤ _ := sum_le_sum fun S hS => hS1 S (by rw [(mem_powersetCard.1 hS).2]; omega)

/-- **Every covering has total excess `≥ binom(n, r-1)/r`** when `q - r + 1 ∤ n - r + 1`:
`r·binom(n, r) + binom(n, r-1) ≤ r·binom(q, r)·|𝒞|`. -/
theorem covering_excess_lower {q r n : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (hrn : r ≤ n)
    (hnd : ¬ (q - r + 1) ∣ (n - r + 1)) {𝒞 : Finset (Finset (Fin n))}
    (h𝒞 : IsCovering q r 𝒞) :
    r * n.choose r + n.choose (r - 1) ≤ r * (q.choose r * 𝒞.card) := by
  set m : Finset (Fin n) → ℕ := fun e => cliqueMult 𝒞 e
  -- total multiplicity
  have htot : ∑ e ∈ (univ : Finset (Fin n)).powersetCard r, m e = q.choose r * 𝒞.card := by
    have := sum_weight_double_count q r 𝒞 h𝒞.1 (fun _ => (1 : ℕ)) ∅ (by simp)
    simp only [empty_subset, card_empty, Nat.sub_zero, sum_const, smul_eq_mul, mul_one] at this
    simpa [m, cliqueMult] using this
  -- local excess at every `(r-1)`-set
  have hloc : ∀ S ∈ (univ : Finset (Fin n)).powersetCard (r - 1),
      ∑ e ∈ ((univ : Finset (Fin n)).powersetCard r).filter (fun e => S ⊆ e), 1 + 1 ≤
      ∑ e ∈ ((univ : Finset (Fin n)).powersetCard r).filter (fun e => S ⊆ e), m e := by
    intro S hS
    have hSc : S.card = r - 1 := (mem_powersetCard.1 hS).2
    have h1 := sum_weight_double_count q r 𝒞 h𝒞.1 (fun _ => (1 : ℕ)) S (by omega)
    simp only [sum_const, smul_eq_mul, mul_one] at h1
    have hcnt := card_powersetCard_filter_superset (subset_univ S) (r := r) (by omega)
    rw [card_univ, Fintype.card_fin] at hcnt
    have hge : ∑ e ∈ ((univ : Finset (Fin n)).powersetCard r).filter (fun e => S ⊆ e), 1 ≤
        ∑ e ∈ ((univ : Finset (Fin n)).powersetCard r).filter (fun e => S ⊆ e), m e := by
      refine sum_le_sum fun e he => ?_
      obtain ⟨C, hC, heC⟩ := h𝒞.2 e (mem_powersetCard.1 (mem_filter.1 he).1).2
      exact card_pos.2 ⟨C, mem_filter.2 ⟨hC, heC⟩⟩
    have hm : ∑ e ∈ ((univ : Finset (Fin n)).powersetCard r).filter (fun e => S ⊆ e), m e
        = (q - S.card).choose (r - S.card) * cliqueMult 𝒞 S := by
      simpa [m, cliqueMult] using h1
    rw [sum_const, smul_eq_mul, mul_one, hcnt] at hge ⊢
    rw [hm] at hge ⊢
    rw [show r - S.card = 1 by omega] at hge ⊢
    simp only [Nat.choose_one_right] at hge ⊢
    rcases Nat.lt_or_ge (n - S.card) ((q - S.card) * cliqueMult 𝒞 S) with h | h
    · omega
    · exfalso
      apply hnd
      refine ⟨cliqueMult 𝒞 S, ?_⟩
      rw [show q - r + 1 = q - S.card by omega, show n - r + 1 = n - S.card by omega]
      omega
  have hA := sum_sub_super hr m
  have hB := sum_sub_super hr (n := n) (fun _ => 1)
  have hsum := sum_le_sum hloc
  rw [sum_add_distrib, hB, hA, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, htot] at hsum
  simpa [sum_const, card_powersetCard] using hsum

end RefinedAbsorption.Extensions
