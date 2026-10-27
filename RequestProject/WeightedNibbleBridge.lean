module
public import RequestProject.OmniFromRefiner

/-!
# The nibble with leftover degree control from weighted pseudorandom matchings

We prove `NibbleLeftoverDegree` from the weighted pseudorandom hypergraph matching theorem of
Ehard, Glock and Joos (their Theorem 1.2), stated here as the proposition
`EGJWeightedMatching` (`nibbleLeftoverDegree_of_egjWeightedMatching`).  The proof applies that
theorem to the auxiliary `binom(q,r)`-uniform hypergraph whose vertices are the `r`-sets and
whose edges are the edge sets of the cliques of `H`, with one test weight per `(r-1)`-set `S`
counting the `r`-sets of an auxiliary edge that contain `S`.  Consequently Corollary 2.4 and the
Existence Conjecture for Steiner systems follow from `EGJWeightedMatching` (together with
`RefinerWithAbsorbers` for the latter).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter

/-! ### Combinatorics of the auxiliary hypergraph -/

/-- For `1 ≤ r < q`, a `q`-set is the union of its `r`-subsets, so `Q ↦ cliqueEdges r Q` is
injective on `q`-sets. -/
theorem cliqueEdges_injOn {V : Type*} [DecidableEq V] {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    Set.InjOn (cliqueEdges r) {Q : Finset V | Q.card = q} := by
  have key : ∀ Q : Finset V, Q.card = q → ∀ x, x ∈ Q ↔ ∃ e ∈ cliqueEdges r Q, x ∈ e := by
    intro Q hQ x
    constructor
    · intro hx
      obtain ⟨u, hxu, huQ, hu⟩ := exists_subsuperset_card_eq (s := {x}) (t := Q) (n := r)
        (by simpa using hx) (by simpa using hr) (by omega)
      exact ⟨u, mem_powersetCard.2 ⟨huQ, hu⟩, hxu (mem_singleton_self x)⟩
    · rintro ⟨e, he, hxe⟩
      exact (mem_powersetCard.1 he).1 hxe
  intro Q₁ h₁ Q₂ h₂ heq
  ext x
  rw [key Q₁ h₁, key Q₂ h₂, heq]

/-- `binom(q, r) ≥ 2` for `1 ≤ r < q`. -/
theorem two_le_choose_of_lt {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) : 2 ≤ q.choose r := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have h1 := Nat.choose_pos (show r' ≤ q' by omega)
  have h2 := Nat.choose_pos (show r' + 1 ≤ q' by omega)
  omega

/-- The number of `q`-subsets of `Fin n` containing a set `T` is at most `n ^ (q - |T|)`. -/
theorem card_supersets_le {n : ℕ} (q : ℕ) (T : Finset (Fin n)) :
    ((univ.powersetCard q).filter (fun Q => T ⊆ Q)).card ≤ n ^ (q - T.card) := by
  calc ((univ.powersetCard q).filter (fun Q => T ⊆ Q)).card
      ≤ (univ.powersetCard (q - T.card) : Finset (Finset (Fin n))).card := by
        refine card_le_card_of_injOn (fun Q => Q \ T) ?_ ?_
        · intro Q hQ
          simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq] at hQ
          rw [mem_coe, mem_powersetCard]; refine ⟨subset_univ _, ?_⟩
          rw [card_sdiff_of_subset hQ.2, hQ.1]
        · intro Q₁ hQ₁ Q₂ hQ₂ heq
          simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq]
            at hQ₁ hQ₂
          have e1 := sdiff_union_of_subset hQ₁.2
          have e2 := sdiff_union_of_subset hQ₂.2
          simp only at heq
          rw [← e1, ← e2, heq]
    _ = n.choose (q - T.card) := by simp
    _ ≤ n ^ (q - T.card) := Nat.choose_le_pow _ _

/-- An `(r-1)`-set lies in at most `n` `r`-subsets of `Fin n`. -/
theorem deg_le_n {n r : ℕ} {G : Finset (Finset (Fin n))} (hG : G ⊆ completeRGraph (Fin n) r)
    {S : Finset (Fin n)} (hS : S.card + 1 = r) : deg G S ≤ n := by
  unfold deg
  calc (G.filter (fun e => S ⊆ e)).card
      ≤ (univ.powersetCard 1 : Finset (Finset (Fin n))).card := by
        refine card_le_card_of_injOn (fun e => e \ S) ?_ ?_
        · intro e he
          simp only [coe_filter, Set.mem_setOf_eq] at he
          have hc := (mem_powersetCard.1 (hG he.1)).2
          rw [mem_coe, mem_powersetCard]; refine ⟨subset_univ _, ?_⟩
          rw [card_sdiff_of_subset he.2]; omega
        · intro e₁ he₁ e₂ he₂ heq
          simp only [coe_filter, Set.mem_setOf_eq] at he₁ he₂
          simp only at heq
          rw [← sdiff_union_of_subset he₁.2, ← sdiff_union_of_subset he₂.2, heq]
    _ = n := by simp

/-- The auxiliary hypergraph of a clique family `H`: its vertices are `r`-sets and its edges are
the edge sets `cliqueEdges r Q` of the cliques `Q ∈ H`. -/
def auxEdges {n : ℕ} (r : ℕ) (H : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin n))) :=
  H.image (cliqueEdges r)

/-- The test weight of an `(r-1)`-set `S`: an auxiliary edge `F` gets weight the number of its
`r`-sets containing `S`. -/
def testWeight {n : ℕ} (S : Finset (Fin n)) (F : Finset (Finset (Fin n))) : ℝ :=
  ((F.filter (fun e => S ⊆ e)).card : ℝ)

section Aux

variable {n q r : ℕ} {G H : Finset (Finset (Fin n))}

theorem card_eq_of_mem_cliquesOf {Q : Finset (Fin n)} (h : Q ∈ cliquesOf q r G) : Q.card = q :=
  (mem_powersetCard.1 (mem_filter.1 h).1).2

theorem cliqueEdges_subset_of_mem_cliquesOf {Q : Finset (Fin n)} (h : Q ∈ cliquesOf q r G) :
    cliqueEdges r Q ⊆ G :=
  (mem_filter.1 h).2

theorem auxEdges_card (hH : H ⊆ cliquesOf q r G) :
    ∀ F ∈ auxEdges r H, F.card = q.choose r := by
  intro F hF
  obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hF
  rw [cliqueEdges, card_powersetCard, card_eq_of_mem_cliquesOf (hH hQ)]

theorem auxEdges_injOn (hr : 1 ≤ r) (hrq : r < q) (hH : H ⊆ cliquesOf q r G) :
    Set.InjOn (cliqueEdges r) (H : Set (Finset (Fin n))) := fun _ h₁ _ h₂ heq =>
  cliqueEdges_injOn hr hrq (card_eq_of_mem_cliquesOf (hH h₁))
    (card_eq_of_mem_cliquesOf (hH h₂)) heq

theorem auxEdges_deg_le (hr : 1 ≤ r) (hrq : r < q) (hH : H ⊆ cliquesOf q r G)
    (e : Finset (Fin n)) :
    ((auxEdges r H).filter (fun F => e ∈ F)).card ≤ if e ∈ G then cliqueMult H e else 0 := by
  unfold auxEdges
  rw [filter_image, card_image_of_injOn
    (fun Q₁ h₁ Q₂ h₂ heq => auxEdges_injOn hr hrq hH (mem_filter.1 h₁).1 (mem_filter.1 h₂).1 heq)]
  split_ifs with he
  · unfold cliqueMult
    refine card_le_card (fun Q hQ => ?_)
    simp only [mem_filter, cliqueEdges, mem_powersetCard] at hQ ⊢
    exact ⟨hQ.1, hQ.2.1⟩
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    intro Q hQ hcon
    exact he (cliqueEdges_subset_of_mem_cliquesOf (hH hQ) hcon)

theorem auxEdges_codeg_le (hn : 1 ≤ n) (hH : H ⊆ cliquesOf q r G) {u v : Finset (Fin n)}
    (huv : u ≠ v) :
    ((auxEdges r H).filter (fun F => u ∈ F ∧ v ∈ F)).card ≤ n ^ (q - r - 1) := by
  unfold auxEdges
  rw [filter_image]
  refine (card_image_le).trans ?_
  by_cases hu : u.card = r
  · by_cases hv : v.card = r
    · have hT : r + 1 ≤ (u ∪ v).card := by
        by_contra hcon
        have h1 : u = u ∪ v := eq_of_subset_of_card_le subset_union_left (by rw [hu]; omega)
        have h2 : v = u ∪ v := eq_of_subset_of_card_le subset_union_right (by rw [hv]; omega)
        exact huv (h1.trans h2.symm)
      calc (H.filter ((fun F => u ∈ F ∧ v ∈ F) ∘ cliqueEdges r)).card
          ≤ ((univ.powersetCard q).filter (fun Q => u ∪ v ⊆ Q)).card := by
            refine card_le_card (fun Q hQ => ?_)
            simp only [mem_filter, Function.comp, cliqueEdges, mem_powersetCard] at hQ
            refine mem_filter.2 ⟨?_, union_subset hQ.2.1.1 hQ.2.2.1⟩
            exact (mem_filter.1 (hH hQ.1)).1
        _ ≤ n ^ (q - (u ∪ v).card) := card_supersets_le q _
        _ ≤ n ^ (q - r - 1) := Nat.pow_le_pow_right hn (by omega)
    · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun Q _ h => hv
        (mem_powersetCard.1 h.2).2)]
      exact Nat.zero_le _
  · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun Q _ h => hu
      (mem_powersetCard.1 h.1).2)]
    exact Nat.zero_le _

theorem testWeight_nonneg (S : Finset (Fin n)) (F : Finset (Finset (Fin n))) :
    0 ≤ testWeight S F := Nat.cast_nonneg _

theorem testWeight_le_card (S : Finset (Fin n)) (F : Finset (Finset (Fin n))) :
    testWeight S F ≤ F.card := by
  unfold testWeight; exact_mod_cast card_filter_le _ _

/-- Double counting: the total test weight of `S` is the sum of the clique multiplicities of the
edges of `G` containing `S`. -/
theorem auxEdges_sum_testWeight (hr : 1 ≤ r) (hrq : r < q) (hG : G ⊆ completeRGraph (Fin n) r)
    (hH : H ⊆ cliquesOf q r G) (S : Finset (Fin n)) :
    ∑ F ∈ auxEdges r H, testWeight S F = ∑ e ∈ G.filter (fun e => S ⊆ e), (cliqueMult H e : ℝ) := by
  unfold auxEdges testWeight
  rw [sum_image (fun Q₁ h₁ Q₂ h₂ heq => auxEdges_injOn hr hrq hH h₁ h₂ heq)]
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  congr 1
  have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun Q e => e ∈ cliqueEdges r Q)
    (s := H) (t := G.filter (fun e => S ⊆ e))
  convert this using 1
  · refine sum_congr rfl (fun Q hQ => ?_)
    congr 1
    unfold bipartiteAbove
    ext e
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨cliqueEdges_subset_of_mem_cliquesOf (hH hQ) h1, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  · refine sum_congr rfl (fun e he => ?_)
    unfold bipartiteBelow cliqueMult
    have hc := (mem_powersetCard.1 (hG (mem_filter.1 he).1)).2
    congr 1
    ext Q
    simp only [mem_filter, cliqueEdges, mem_powersetCard, hc, and_true]

/-- The test weight of a family of pairwise disjoint auxiliary edges is the number of covered
`r`-sets containing `S`. -/
theorem sum_testWeight_of_pairwiseDisjoint {M : Finset (Finset (Finset (Fin n)))}
    (hM : ∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) (S : Finset (Fin n)) :
    ∑ F ∈ M, testWeight S F = deg (M.biUnion id) S := by
  unfold testWeight deg
  rw [← Nat.cast_sum, filter_biUnion, card_biUnion]
  · rfl
  · intro F₁ h₁ F₂ h₂ hne
    exact disjoint_filter_filter (hM F₁ h₁ F₂ h₂ hne)

/-- The cliques of `H` whose edge sets form a matching `M` of the auxiliary hypergraph form a
packing covering exactly the vertices of `M`. -/
theorem packing_of_auxMatching (hr : 1 ≤ r) (hrq : r < q) (hH : H ⊆ cliquesOf q r G)
    {M : Finset (Finset (Finset (Fin n)))} (hMsub : M ⊆ auxEdges r H)
    (hM : ∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) :
    IsPacking q r G (H.filter (fun Q => cliqueEdges r Q ∈ M)) ∧
      coveredEdges r (H.filter (fun Q => cliqueEdges r Q ∈ M)) = M.biUnion id := by
  refine ⟨⟨fun Q hQ => card_eq_of_mem_cliquesOf (hH (mem_filter.1 hQ).1),
    fun Q hQ => cliqueEdges_subset_of_mem_cliquesOf (hH (mem_filter.1 hQ).1),
    fun e he => ?_⟩, ?_⟩
  · unfold cliqueMult
    rw [card_le_one]
    intro Q₁ h₁ Q₂ h₂
    simp only [mem_filter] at h₁ h₂
    by_contra hne
    have hne' : cliqueEdges r Q₁ ≠ cliqueEdges r Q₂ :=
      fun heq => hne (auxEdges_injOn hr hrq hH h₁.1.1 h₂.1.1 heq)
    have hd := hM _ h₁.1.2 _ h₂.1.2 hne'
    exact disjoint_left.1 hd (mem_powersetCard.2 ⟨h₁.2, he⟩) (mem_powersetCard.2 ⟨h₂.2, he⟩)
  · unfold coveredEdges
    ext e
    simp only [mem_biUnion, mem_filter, id]
    constructor
    · rintro ⟨Q, ⟨_, hQM⟩, he⟩; exact ⟨_, hQM, he⟩
    · rintro ⟨F, hF, he⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_image.1 (hMsub hF)
      exact ⟨Q, ⟨hQ, hF⟩, he⟩

theorem deg_sdiff_of_subset {X : Finset (Finset (Fin n))} (hX : X ⊆ G) (S : Finset (Fin n)) :
    (deg (G \ X) S : ℝ) = deg G S - deg X S := by
  unfold deg
  have : (G \ X).filter (fun e => S ⊆ e) = G.filter (fun e => S ⊆ e) \ X.filter (fun e => S ⊆ e) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, fun h => h2 h.1⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, fun h => h2 ⟨h, h3⟩⟩, h3⟩
  rw [this, card_sdiff_of_subset (filter_subset_filter _ hX), Nat.cast_sub
    (card_le_card (filter_subset_filter _ hX))]

end Aux

/-! ### Real-analytic estimates -/

theorem eventually_rpow_le_mul_rpow {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ a ≤ c * x ^ b := by
  have h := (tendsto_rpow_neg_atTop (show 0 < b - a by linarith)).eventually (ge_mem_nhds hc)
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  have : x ^ a = x ^ (-(b - a)) * x ^ b := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

theorem eventually_pow_le_exp_rpow (q : ℕ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    ∀ᶠ x : ℝ in atTop, x ^ q ≤ Real.exp ((A * x) ^ t) := by
  have hc : 0 < A ^ t / (q + 1) := by positivity
  have h := (isLittleO_log_rpow_atTop ht).bound hc
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  have hlog : Real.log x ≤ A ^ t / (q + 1) * x ^ t := (le_abs_self _).trans hx
  calc x ^ q = Real.exp (q * Real.log x) := by
        rw [Real.exp_nat_mul, Real.exp_log hx0]
    _ ≤ Real.exp ((A * x) ^ t) := by
        apply Real.exp_le_exp.2
        rw [Real.mul_rpow hA.le hx0.le]
        have hq : (q : ℝ) * (A ^ t / (q + 1)) ≤ A ^ t := by
          rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.rpow_pos_of_pos hA t]
        have hxt : 0 ≤ x ^ t := Real.rpow_nonneg hx0.le _
        calc (q : ℝ) * Real.log x ≤ q * (A ^ t / (q + 1) * x ^ t) :=
              mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q)
          _ = (q * (A ^ t / (q + 1))) * x ^ t := by ring
          _ ≤ A ^ t * x ^ t := mul_le_mul_of_nonneg_right hq hxt

theorem choose_lower_bound {n s : ℕ} (hn : 2 * s ≤ n) :
    (n : ℝ) ^ s / (2 ^ s * s.factorial) ≤ n.choose s := by
  refine le_trans ?_ (Nat.pow_le_choose (α := ℝ) s n)
  have h : (n : ℝ) / 2 ≤ ((n + 1 - s : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast
    have : (2 * s : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : ((n : ℝ) / 2) ^ s ≤ ((n + 1 - s : ℕ) : ℝ) ^ s := pow_le_pow_left₀ (by positivity) h s
  rw [div_pow] at h2
  rw [div_le_iff₀ (by positivity)] at h2
  nlinarith [Nat.factorial_pos s, show (0:ℝ) < s.factorial by exact_mod_cast Nat.factorial_pos s]

/-- The arithmetic of a large test: from the weighted conclusion and approximate regularity, the
leftover degree is at most `d (e + 2t/ρ + 1/(ρC))`. -/
theorem large_test_bound {d W ωM Δ ρ t C e : ℝ} (hd : 0 ≤ d) (hC : 0 < C) (hρ : 0 < ρ)
    (ht : 0 ≤ t) (hΔlo : (ρ + t) * C ≤ Δ) (hΔhi : Δ ≤ (ρ + t) * C + 1)
    (hWlo : d * ((ρ - t) * C) ≤ W) (hWhi : W ≤ d * ((ρ + t) * C))
    (hω : |ωM - W / Δ| ≤ e * (W / Δ)) (he : 0 ≤ e) :
    d - ωM ≤ d * (e + 2 * t / ρ + 1 / (ρ * C)) := by
  have hρC : 0 < ρ * C := mul_pos hρ hC
  have hΔ : 0 < Δ := lt_of_lt_of_le (by nlinarith) hΔlo
  have h1 := (abs_le.1 hω).1
  have hWΔ : W / Δ ≤ d := by
    rw [div_le_iff₀ hΔ]; nlinarith
  have hWΔlo : d * ((ρ - t) * C) / Δ ≤ W / Δ := div_le_div_of_nonneg_right hWlo hΔ.le
  have h3 : d - d * ((ρ - t) * C) / Δ ≤ d * (2 * t / ρ + 1 / (ρ * C)) := by
    have : d - d * ((ρ - t) * C) / Δ = d * ((Δ - (ρ - t) * C) / Δ) := by field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hd
    have hnum : 0 ≤ Δ - (ρ - t) * C := by nlinarith
    calc (Δ - (ρ - t) * C) / Δ ≤ (2 * t * C + 1) / Δ :=
          div_le_div_of_nonneg_right (by nlinarith) hΔ.le
      _ ≤ (2 * t * C + 1) / (ρ * C) :=
          div_le_div_of_nonneg_left (by positivity) hρC (by nlinarith)
      _ = 2 * t / ρ + 1 / (ρ * C) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hWΔ he]

/-! ### The weighted pseudorandom matching theorem and the bridge -/

/-- **Weighted pseudorandom hypergraph matchings (Ehard–Glock–Joos, Theorem 1.2).**
Let `δ ∈ (0,1)`, `k ≥ 2` and `ε = δ / (50 k²)`.  There is `Δ₀` such that for all `Δ ≥ Δ₀`: if
`E` is a `k`-uniform hypergraph with maximum degree at most `Δ`, maximum codegree at most
`Δ^{1-δ}` and at most `exp(Δ^{ε²})` edges, and `(ω_i)_{i ∈ ι}` is a family of at most
`exp(Δ^{ε²})` nonnegative weight functions on `E`, then there is a matching `M ⊆ E` with
`|ω_i(M) - ω_i(E)/Δ| ≤ Δ^{-ε} ω_i(E)/Δ` for every `i` such that
`ω_i(F) Δ^{1+δ} ≤ ω_i(E)` for all `F ∈ E`.

This is stated here, not proved (it is the hypothesis of the bridge theorem below). -/
def EGJWeightedMatching : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ k : ℕ, 2 ≤ k → ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
    ∀ (α : Type) [Fintype α] [DecidableEq α] (E : Finset (Finset α)),
      (∀ F ∈ E, F.card = k) →
      (∀ v : α, (E.filter (fun F => v ∈ F)).card ≤ Δ) →
      (∀ u v : α, u ≠ v →
        ((E.filter (fun F => u ∈ F ∧ v ∈ F)).card : ℝ) ≤ (Δ : ℝ) ^ (1 - δ)) →
      (E.card : ℝ) ≤ Real.exp ((Δ : ℝ) ^ ((δ / (50 * (k : ℝ) ^ 2)) ^ 2)) →
      ∀ (ι : Type) [Fintype ι] (ω : ι → Finset α → ℝ),
        (∀ i, ∀ F ∈ E, 0 ≤ ω i F) →
        (Fintype.card ι : ℝ) ≤ Real.exp ((Δ : ℝ) ^ ((δ / (50 * (k : ℝ) ^ 2)) ^ 2)) →
        ∃ M ⊆ E, (∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
          ∀ i, (∀ F ∈ E, ω i F * (Δ : ℝ) ^ (1 + δ) ≤ ∑ F ∈ E, ω i F) →
            |∑ F ∈ M, ω i F - (∑ F ∈ E, ω i F) / Δ|
              ≤ (Δ : ℝ) ^ (-(δ / (50 * (k : ℝ) ^ 2))) * ((∑ F ∈ E, ω i F) / Δ)

set_option maxHeartbeats 1000000 in
/-- **Bridge: the weighted pseudorandom matching theorem implies the nibble with leftover degree
control.**  Apply `EGJWeightedMatching` to the auxiliary `binom(q,r)`-uniform hypergraph whose
vertices are the `r`-sets and whose edges are the edge sets of the cliques of `H`, with
`Δ = ⌈(ρ + n^{-β}) binom(n, q-r)⌉`, `δ = min(1/2, 1/(4(q-r)))`, and one test weight
`F ↦ #{e ∈ F : S ⊆ e}` for each `(r-1)`-set `S`.  Tests with `deg_G(S) < n^{1/2}` need no
control; for the others the weight is eligible and the weighted conclusion bounds the leftover
degree by `n^{1-γ}` with `γ = min(β, ε)/2`. -/
theorem nibbleLeftoverDegree_of_egjWeightedMatching (hEGJ : EGJWeightedMatching) :
    NibbleLeftoverDegree := by
  intro q r hr hrq ρ hρ hρ1 β hβ hβ1
  -- parameters
  set s : ℕ := q - r with hs
  have hs1 : 1 ≤ s := by omega
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  set k : ℕ := q.choose r with hk
  have hk2 : 2 ≤ k := two_le_choose_of_lt hr hrq
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  set δ : ℝ := min (1 / 2) (1 / (4 * s)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hsδ : (s : ℝ) * δ ≤ 1 / 4 := by
    have : δ ≤ 1 / (4 * s) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  obtain ⟨Δ₀, hΔ₀⟩ := hEGJ δ hδ0 hδ1 k hk2
  set ε : ℝ := δ / (50 * (k : ℝ) ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  set γ : ℝ := min β ε / 2 with hγ
  have hγ0 : 0 < γ := by positivity
  have hγβ : γ < β := by have := min_le_left β ε; linarith
  have hγε : γ < ε := by have := min_le_right β ε; linarith
  have hγ1 : γ ≤ 1 / 2 := by have := min_le_left β ε; linarith
  set c₁ : ℝ := 1 / (2 ^ s * (s.factorial : ℝ)) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set A : ℝ := ρ * c₁ with hA
  have hA0 : 0 < A := mul_pos hρ hc₁0
  -- eventual real inequalities
  have ev : ∀ᶠ x : ℝ in atTop, (2 * s : ℝ) ≤ x ∧ x ^ (-β) ≤ ρ / 2 ∧ (Δ₀ : ℝ) ≤ A * x ∧
      x ^ ((s : ℝ) - 1) ≤ A ^ (1 - δ) * x ^ ((s : ℝ) * (1 - δ)) ∧
      x ^ q ≤ Real.exp ((A * x) ^ (ε ^ 2)) ∧
      x ^ (1 / 4 : ℝ) ≤ ρ / (18 * k) * x ^ (1 / 2 : ℝ) ∧
      x ^ (-ε) ≤ A ^ ε / 3 * x ^ (-γ) ∧ x ^ (-β) ≤ ρ / 6 * x ^ (-γ) ∧
      x ^ (-1 : ℝ) ≤ A / 3 * x ^ (-γ) := by
    refine (eventually_ge_atTop _).and ((?_ : ∀ᶠ x : ℝ in atTop, x ^ (-β) ≤ ρ / 2).and
      ((tendsto_id.const_mul_atTop hA0).eventually (eventually_ge_atTop _) |>.and
      ((eventually_rpow_le_mul_rpow (by nlinarith) (by positivity)).and
      ((eventually_pow_le_exp_rpow q hA0 (by positivity)).and
      ((eventually_rpow_le_mul_rpow (by norm_num) (by positivity)).and
      ((eventually_rpow_le_mul_rpow (by linarith) (by positivity)).and
      ((eventually_rpow_le_mul_rpow (by linarith) (by positivity)).and
      (eventually_rpow_le_mul_rpow (by linarith) (by positivity)))))))))
    filter_upwards [eventually_rpow_le_mul_rpow (show -β < 0 by linarith)
      (show (0 : ℝ) < ρ / 2 by positivity), eventually_gt_atTop 0] with x hx hx0
    simpa using hx
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually ev)
  refine ⟨γ, hγ0, n₀, fun n hn G hG H hH hdegH => ?_⟩
  obtain ⟨F1, F2, F3, F4, F5, F6, F7a, F7b, F7c⟩ := hn₀ n hn
  -- basic bounds at this `n`
  have hn2s : 2 * s ≤ n := by exact_mod_cast F1
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0R : (0 : ℝ) < n := by linarith
  set C : ℝ := (n.choose s : ℝ) with hC
  have hC1 : 1 ≤ C := by
    rw [hC]; exact_mod_cast Nat.choose_pos (by omega : s ≤ n)
  have hClo : c₁ * (n : ℝ) ^ s ≤ C := by
    have := choose_lower_bound hn2s
    rw [hc₁]; rw [div_eq_mul_inv, mul_comm] at this; simpa [one_div] using this
  have hChi : C ≤ (n : ℝ) ^ s := by rw [hC]; exact_mod_cast Nat.choose_le_pow n s
  set t : ℝ := (n : ℝ) ^ (-β) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0R.le _
  set Δ : ℕ := ⌈(ρ + t) * C⌉₊ with hΔ
  have hΔlo : (ρ + t) * C ≤ Δ := Nat.le_ceil _
  have hΔhi : (Δ : ℝ) ≤ (ρ + t) * C + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hAn_s : A * (n : ℝ) ^ s ≤ ρ * C := by
    rw [hA, mul_assoc]; exact mul_le_mul_of_nonneg_left hClo hρ.le
  have hns : (n : ℝ) ≤ (n : ℝ) ^ s := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ s := pow_le_pow_right₀ hn1R hs1
  have hAn : A * n ≤ ρ * C := le_trans (mul_le_mul_of_nonneg_left hns hA0.le) hAn_s
  have htC : 0 ≤ t * C := mul_nonneg ht0 (by linarith)
  have hρC_Δ : ρ * C ≤ Δ := le_trans (by linarith [add_mul ρ t C]) hΔlo
  have hΔpos : (0 : ℝ) < Δ := lt_of_lt_of_le (by positivity) hρC_Δ
  have hΔ3C : (Δ : ℝ) ≤ 3 * C := by
    have : (ρ + t) * C ≤ (3 / 2) * C :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hΔ₀Δ : Δ₀ ≤ Δ := by exact_mod_cast F3.trans (hAn.trans hρC_Δ)
  -- hypotheses of the weighted matching theorem
  have hdegAux : ∀ v : Finset (Fin n), ((auxEdges r H).filter (fun F => v ∈ F)).card ≤ Δ := by
    intro v
    refine (auxEdges_deg_le hr hrq hH v).trans ?_
    split_ifs with hv
    · have h := (abs_le.1 (hdegH v hv)).2
      have : (cliqueMult H v : ℝ) ≤ Δ := by linarith [add_mul ρ t C]
      exact_mod_cast this
    · exact Nat.zero_le _
  have hcodeg : ∀ u v : Finset (Fin n), u ≠ v →
      (((auxEdges r H).filter (fun F => u ∈ F ∧ v ∈ F)).card : ℝ) ≤ (Δ : ℝ) ^ (1 - δ) := by
    intro u v huv
    have h1 : (((auxEdges r H).filter (fun F => u ∈ F ∧ v ∈ F)).card : ℝ) ≤ (n : ℝ) ^ (s - 1) := by
      exact_mod_cast auxEdges_codeg_le hn1 hH huv
    refine h1.trans ?_
    have h2 : (n : ℝ) ^ (s - 1) = (n : ℝ) ^ ((s : ℝ) - 1) := by
      rw [← Real.rpow_natCast, Nat.cast_sub hs1, Nat.cast_one]
    rw [h2]
    refine F4.trans ?_
    have h3 : A ^ (1 - δ) * (n : ℝ) ^ ((s : ℝ) * (1 - δ)) = (A * (n : ℝ) ^ s) ^ (1 - δ) := by
      rw [Real.mul_rpow hA0.le (by positivity), Real.rpow_natCast_mul hn0R.le]
    rw [h3]
    exact Real.rpow_le_rpow (by positivity) (hAn_s.trans hρC_Δ) (by linarith)
  have hexp : (n : ℝ) ^ q ≤ Real.exp ((Δ : ℝ) ^ (ε ^ 2)) :=
    F5.trans (Real.exp_le_exp.2
      (Real.rpow_le_rpow (by positivity) (hAn.trans hρC_Δ) (by positivity)))
  have hcard : ((auxEdges r H).card : ℝ) ≤ Real.exp ((Δ : ℝ) ^ (ε ^ 2)) := by
    have : (auxEdges r H).card ≤ n ^ q := by
      refine card_image_le.trans ((card_le_card (hH.trans (filter_subset _ _))).trans ?_)
      rw [card_powersetCard, card_univ, Fintype.card_fin]
      exact Nat.choose_le_pow n q
    exact (by exact_mod_cast this : ((auxEdges r H).card : ℝ) ≤ (n : ℝ) ^ q).trans hexp
  have htests : (Fintype.card (univ.powersetCard (r - 1) : Finset (Finset (Fin n))) : ℝ) ≤
      Real.exp ((Δ : ℝ) ^ (ε ^ 2)) := by
    rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
    have : n.choose (r - 1) ≤ n ^ q :=
      (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hn1 (by omega))
    exact (by exact_mod_cast this : ((n.choose (r - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ q).trans hexp
  obtain ⟨M, hMsub, hMdisj, hMtest⟩ := hΔ₀ Δ hΔ₀Δ (Finset (Fin n)) (auxEdges r H)
    (auxEdges_card hH) hdegAux hcodeg hcard
    (univ.powersetCard (r - 1) : Finset (Finset (Fin n))) (fun S F => testWeight S.1 F)
    (fun _ _ _ => testWeight_nonneg _ _) htests
  -- the packing
  obtain ⟨hP, hcov⟩ := packing_of_auxMatching hr hrq hH hMsub hMdisj
  refine ⟨_, hP, fun S hS => ?_⟩
  have hXG : M.biUnion id ⊆ G := hcov ▸ hP.coveredEdges_subset
  rw [hcov, deg_sdiff_of_subset hXG, ← sum_testWeight_of_pairwiseDisjoint hMdisj]
  set d : ℝ := (deg G S : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hd_n : d ≤ n := by rw [hd]; exact_mod_cast deg_le_n hG hS
  have hωM0 : 0 ≤ ∑ F ∈ M, testWeight S F := sum_nonneg fun F _ => testWeight_nonneg S F
  have hhalf : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - γ) :=
    Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
  by_cases hsmall : d < (n : ℝ) ^ (1 / 2 : ℝ)
  · linarith
  push_neg at hsmall
  -- the large test `S`
  have hW := auxEdges_sum_testWeight hr hrq hG hH S
  set W : ℝ := ∑ F ∈ auxEdges r H, testWeight S F with hWdef
  have hcardd : ((G.filter (fun e => S ⊆ e)).card : ℝ) = d := rfl
  have hWlo : d * ((ρ - t) * C) ≤ W := by
    rw [hW, ← hcardd, ← nsmul_eq_mul]
    apply card_nsmul_le_sum
    intro e he
    have := (abs_le.1 (hdegH e (mem_filter.1 he).1)).1
    linarith [sub_mul ρ t C]
  have hWhi : W ≤ d * ((ρ + t) * C) := by
    rw [hW, ← hcardd, ← nsmul_eq_mul]
    apply sum_le_card_nsmul
    intro e he
    have := (abs_le.1 (hdegH e (mem_filter.1 he).1)).2
    linarith [add_mul ρ t C]
  clear_value W d Δ t C
  clear hn₀ ev
  have hΔpow : (Δ : ℝ) ^ (1 + δ) ≤ 9 * C * (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_add hΔpos, Real.rpow_one]
    have h1 : (Δ : ℝ) ^ δ ≤ (3 * (n : ℝ) ^ s) ^ δ :=
      Real.rpow_le_rpow hΔpos.le (by linarith) hδ0.le
    have h2 : (3 * (n : ℝ) ^ s) ^ δ ≤ 3 * (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hn0R.le]
      have h3 : (3 : ℝ) ^ δ ≤ 3 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hδ1.le
      have h4 : (n : ℝ) ^ ((s : ℝ) * δ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1R hsδ
      exact mul_le_mul h3 h4 (by positivity) (by norm_num)
    calc (Δ : ℝ) * (Δ : ℝ) ^ δ ≤ (3 * C) * (3 * (n : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul hΔ3C (h1.trans h2) (by positivity) (by linarith)
      _ = 9 * C * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
  have helig : ∀ F ∈ auxEdges r H, testWeight S F * (Δ : ℝ) ^ (1 + δ) ≤ W := by
    intro F hF
    have hwk : testWeight S F ≤ k := by
      have := testWeight_le_card S F
      rwa [auxEdges_card hH F hF] at this
    have hk0 : (0 : ℝ) < k := by linarith
    calc testWeight S F * (Δ : ℝ) ^ (1 + δ)
        ≤ k * (9 * C * (n : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul hwk hΔpow (by positivity) hk0.le
      _ ≤ k * (9 * C * (ρ / (18 * k) * (n : ℝ) ^ (1 / 2 : ℝ))) := by
          gcongr
      _ = (ρ / 2) * C * (n : ℝ) ^ (1 / 2 : ℝ) := by field_simp; ring
      _ ≤ (ρ - t) * C * d := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hsmall
            (by positivity)
          exact mul_nonneg (by linarith) (by linarith)
      _ = d * ((ρ - t) * C) := by ring
      _ ≤ W := hWlo
  have hconc : |∑ F ∈ M, testWeight S F - W / Δ| ≤ (Δ : ℝ) ^ (-ε) * (W / Δ) := by
    have helig' : ∀ F ∈ auxEdges r H, testWeight S F * (Δ : ℝ) ^ (1 + δ) ≤
        ∑ F ∈ auxEdges r H, testWeight S F := by
      intro F hF; have := helig F hF; rwa [hWdef] at this
    rw [hWdef]
    exact hMtest ⟨S, mem_powersetCard.2 ⟨subset_univ _, Nat.eq_sub_of_add_eq hS⟩⟩ helig'
  have hb := large_test_bound hd0 (by linarith : (0 : ℝ) < C) hρ ht0 hΔlo hΔhi hWlo hWhi hconc
    (Real.rpow_nonneg hΔpos.le _)
  -- the error term is at most `n^{-γ}`
  have hT1 : (Δ : ℝ) ^ (-ε) ≤ (n : ℝ) ^ (-γ) / 3 := by
    have h1 : (Δ : ℝ) ^ (-ε) ≤ (A * n) ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hAn.trans hρC_Δ) (by linarith)
    rw [Real.mul_rpow hA0.le hn0R.le, Real.rpow_neg hA0.le] at h1
    have h2 : (A ^ ε)⁻¹ * (n : ℝ) ^ (-ε) ≤ (A ^ ε)⁻¹ * (A ^ ε / 3 * (n : ℝ) ^ (-γ)) :=
      mul_le_mul_of_nonneg_left F7a (by positivity)
    have h3 : (A ^ ε)⁻¹ * (A ^ ε / 3 * (n : ℝ) ^ (-γ)) = (n : ℝ) ^ (-γ) / 3 := by
      have : A ^ ε ≠ 0 := (Real.rpow_pos_of_pos hA0 ε).ne'
      field_simp
    linarith
  have hT2 : 2 * t / ρ ≤ (n : ℝ) ^ (-γ) / 3 := by
    rw [div_le_iff₀ hρ]; nlinarith
  have hT3 : 1 / (ρ * C) ≤ (n : ℝ) ^ (-γ) / 3 := by
    have h1 : 1 / (ρ * C) ≤ 1 / (A * n) := one_div_le_one_div_of_le (by positivity) hAn
    have h2 : 1 / (A * n) = A⁻¹ * (n : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]; field_simp
    have h3 : A⁻¹ * (n : ℝ) ^ (-1 : ℝ) ≤ A⁻¹ * (A / 3 * (n : ℝ) ^ (-γ)) :=
      mul_le_mul_of_nonneg_left F7c (by positivity)
    have h4 : A⁻¹ * (A / 3 * (n : ℝ) ^ (-γ)) = (n : ℝ) ^ (-γ) / 3 := by
      field_simp
    linarith
  have hT0 : 0 ≤ (Δ : ℝ) ^ (-ε) + 2 * t / ρ + 1 / (ρ * C) := by positivity
  have hfin : (n : ℝ) * (n : ℝ) ^ (-γ) = (n : ℝ) ^ (1 - γ) := by
    rw [sub_eq_add_neg, Real.rpow_add hn0R, Real.rpow_one]
  calc d - ∑ F ∈ M, testWeight S F ≤ d * ((Δ : ℝ) ^ (-ε) + 2 * t / ρ + 1 / (ρ * C)) := hb
    _ ≤ (n : ℝ) * (n : ℝ) ^ (-γ) :=
        mul_le_mul hd_n (by linarith) hT0 hn0R.le
    _ = (n : ℝ) ^ (1 - γ) := hfin

/-! ### Consequences -/

/-- **Corollary 2.4 (general polynomial error)** from the weighted pseudorandom matching
theorem. -/
theorem nibbleWithReservesGen_of_egjWeightedMatching (hEGJ : EGJWeightedMatching) :
    NibbleWithReservesGen :=
  nibbleWithReservesGen_of_nibbleLeftoverDegree
    (nibbleLeftoverDegree_of_egjWeightedMatching hEGJ)

/-- **Corollary 2.4, exactly as stated in the survey**, from the weighted pseudorandom matching
theorem. -/
theorem nibbleWithReserves_of_egjWeightedMatching (hEGJ : EGJWeightedMatching) :
    NibbleWithReserves :=
  nibbleWithReserves_of_nibbleLeftoverDegree (nibbleLeftoverDegree_of_egjWeightedMatching hEGJ)

/-- **The Existence Conjecture for Steiner systems** from refined refiners with attached
absorbers and the weighted pseudorandom matching theorem. -/
theorem steinerExistence_of_refinerWithAbsorbers_egjWeightedMatching
    (hRef : RefinerWithAbsorbers) (hEGJ : EGJWeightedMatching) : SteinerExistenceConjecture :=
  steinerExistence_of_refinerWithAbsorbers_nibbleLeftoverDegree hRef
    (nibbleLeftoverDegree_of_egjWeightedMatching hEGJ)

end RefinedAbsorption
