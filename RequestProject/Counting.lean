module
public import RequestProject.Basic

/-!
# Double counting and the necessity of the divisibility conditions

The basic counting fact behind all divisibility conditions: a copy of `K_q^r` containing an
`i`-set `S` (with `i ≤ r`) contains exactly `binom(q-i, r-i)` edges containing `S`.
From it we derive that `K_q^r`-decomposable `r`-graphs, and more generally `r`-graphs with
an integral `K_q^r`-decomposition (Definition 3.1), are `K_q^r`-divisible.
We also define fractional decompositions (Section 4.1).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of `r`-subsets `e` with `S ⊆ e ⊆ Q` is `binom(|Q|-|S|, r-|S|)` when `S ⊆ Q`. -/
theorem card_powersetCard_filter_superset {Q S : Finset V} {r : ℕ} (hSQ : S ⊆ Q)
    (hSr : S.card ≤ r) :
    ((Q.powersetCard r).filter (fun e => S ⊆ e)).card = (Q.card - S.card).choose (r - S.card) := by
  rw [← card_sdiff_of_subset hSQ, ← card_powersetCard]
  refine card_nbij' (fun e => e \ S) (fun f => f ∪ S) ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_coe, mem_filter, mem_powersetCard] at he ⊢
    refine ⟨sdiff_subset_sdiff he.1.1 Subset.rfl, ?_⟩
    rw [card_sdiff_of_subset he.2, he.1.2]
  · intro f hf
    simp only [mem_coe, mem_filter, mem_powersetCard] at hf ⊢
    have h1 := hf.1
    refine ⟨⟨union_subset (h1.trans sdiff_subset) hSQ, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint (disjoint_of_subset_left h1 disjoint_sdiff_self_left), hf.2]
    omega
  · intro e he
    simp only [mem_coe, mem_filter, mem_powersetCard] at he
    simp [sdiff_union_of_subset he.2]
  · intro f hf
    simp only [mem_coe, mem_powersetCard] at hf
    simp only
    rw [union_sdiff_right,
      sdiff_eq_self_of_disjoint (disjoint_of_subset_left hf.1 disjoint_sdiff_self_left)]

/-- The number of `r`-subsets `e` with `S ⊆ e ⊆ Q` is `0` when `S ⊄ Q`. -/
theorem card_powersetCard_filter_superset_of_not {Q S : Finset V} {r : ℕ} (hSQ : ¬ S ⊆ Q) :
    ((Q.powersetCard r).filter (fun e => S ⊆ e)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hSe
  exact hSQ (hSe.trans (mem_powersetCard.1 he).1)

variable [Fintype V]

/-- **Weighted double counting.**  For a family `T` of `q`-sets with weights `w`, and an
`i`-set `S` with `i ≤ r`, summing over all `r`-sets `e ⊇ S` the total weight of the members
of `T` containing `e` gives `binom(q-i, r-i)` times the total weight of the members of `T`
containing `S`. -/
theorem sum_weight_double_count {M : Type*} [AddCommMonoid M] (q r : ℕ)
    (T : Finset (Finset V)) (hT : ∀ Q ∈ T, Q.card = q) (w : Finset V → M) (S : Finset V)
    (hS : S.card ≤ r) :
    ∑ e ∈ (univ.powersetCard r).filter (fun e => S ⊆ e), ∑ Q ∈ T.filter (fun Q => e ⊆ Q), w Q
      = (q - S.card).choose (r - S.card) • ∑ Q ∈ T.filter (fun Q => S ⊆ Q), w Q := by
  have h1 : ∀ e : Finset V, ∑ Q ∈ T.filter (fun Q => e ⊆ Q), w Q
      = ∑ Q ∈ T, if e ⊆ Q then w Q else 0 := fun e => sum_filter _ _
  simp_rw [h1]
  rw [sum_comm, smul_sum]
  refine sum_congr rfl fun Q hQ => ?_
  rw [← sum_filter, sum_const]
  have : ((univ.powersetCard r).filter (fun e => S ⊆ e)).filter (fun e => e ⊆ Q)
      = (Q.powersetCard r).filter (fun e => S ⊆ e) := by
    ext e; simp [mem_powersetCard]; tauto
  rw [this]
  split_ifs with h
  · rw [card_powersetCard_filter_superset h hS, hT Q hQ]
  · rw [card_powersetCard_filter_superset_of_not h, zero_smul, smul_zero]

/-- The degree of `S` in an `r`-graph, written as a sum of indicators over all `r`-sets. -/
theorem deg_eq_sum_indicator {r : ℕ} {G : Finset (Finset V)} (hG : IsRGraph r G)
    (S : Finset V) :
    deg G S = ∑ e ∈ (univ.powersetCard r).filter (fun e => S ⊆ e), if e ∈ G then 1 else 0 := by
  rw [sum_boole, deg]
  congr 1
  ext e
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨he, hS⟩; exact ⟨⟨hG e he, hS⟩, he⟩
  · rintro ⟨⟨-, hS⟩, he⟩; exact ⟨he, hS⟩

/-- In a `K_q^r`-decomposition, the degree of an `i`-set `S` (with `i ≤ r`) equals
`binom(q-i, r-i)` times the number of cliques containing `S`. -/
theorem IsDecomposition.deg_eq {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) (S : Finset V) (hS : S.card ≤ r) :
    deg G S = (q - S.card).choose (r - S.card) * cliqueMult 𝒬 S := by
  rw [deg_eq_sum_indicator h.rgraph]
  have := sum_weight_double_count q r 𝒬 h.card_eq (fun _ => (1 : ℕ)) S hS
  simp only [sum_const, smul_eq_mul, mul_one] at this
  rw [cliqueMult, ← this]
  refine sum_congr rfl fun e he => ?_
  rw [← h.mult_eq e (mem_powersetCard.1 (mem_filter.1 he).1).2, cliqueMult]

/-- **Necessity of the divisibility conditions.**  Every `r`-graph admitting a
`K_q^r`-decomposition is `K_q^r`-divisible. -/
theorem IsDecomposition.isDivisible {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) : IsDivisible q r G := fun S hS =>
  ⟨_, h.deg_eq S hS.le⟩

/-- **Necessity of the divisibility conditions.**  Every `r`-graph admitting a
`K_q^r`-decomposition is `K_q^r`-divisible. -/
theorem HasDecomposition.isDivisible {q r : ℕ} {G : Finset (Finset V)}
    (h : HasDecomposition q r G) : IsDivisible q r G :=
  h.elim fun _ h => h.isDivisible

/-- **Integral `K_q^r`-decomposition** (Definition 3.1): an assignment `Φ` of integers to the
copies of `K_q^r` (i.e. to the `q`-subsets of the vertex set) such that the total weight of the
cliques containing an `r`-set `e` is `1` if `e` is an edge of `L` and `0` otherwise. -/
def IsIntegralDecomposition (q r : ℕ) (L : Finset (Finset V)) (Φ : Finset V → ℤ) : Prop :=
  ∀ e : Finset V, e.card = r →
    ∑ Q ∈ (univ.powersetCard q).filter (fun Q => e ⊆ Q), Φ Q = if e ∈ L then 1 else 0

/-- An `r`-graph admitting an integral `K_q^r`-decomposition is `K_q^r`-divisible (the easy,
necessary direction of the theorem of Graver–Jurkat and Wilson, Theorem 3.2). -/
theorem IsIntegralDecomposition.isDivisible {q r : ℕ} {L : Finset (Finset V)}
    (hL : IsRGraph r L) {Φ : Finset V → ℤ} (h : IsIntegralDecomposition q r L Φ) :
    IsDivisible q r L := by
  intro S hS
  have hT : ∀ Q ∈ (univ.powersetCard q : Finset (Finset V)), Q.card = q :=
    fun Q hQ => (mem_powersetCard.1 hQ).2
  have key := sum_weight_double_count q r (univ.powersetCard q) hT Φ S hS.le
  have hdeg : (deg L S : ℤ) = ∑ e ∈ (univ.powersetCard r).filter (fun e => S ⊆ e),
      ∑ Q ∈ (univ.powersetCard q).filter (fun Q => e ⊆ Q), Φ Q := by
    rw [deg_eq_sum_indicator hL, Nat.cast_sum]
    refine sum_congr rfl fun e he => ?_
    rw [h e (mem_powersetCard.1 (mem_filter.1 he).1).2]
    split_ifs <;> simp
  rw [key, nsmul_eq_mul] at hdeg
  exact Int.natCast_dvd_natCast.1 ⟨_, hdeg⟩

/-- Summing the indicator of a family of `q`-cliques over all `q`-sets containing `e`
counts the cliques of the family containing `e`. -/
theorem sum_indicator_eq_cliqueMult {R : Type*} [Semiring R] {q : ℕ} {𝒬 : Finset (Finset V)}
    (h𝒬 : ∀ Q ∈ 𝒬, Q.card = q) (e : Finset V) :
    ∑ Q ∈ (univ.powersetCard q).filter (fun Q => e ⊆ Q), (if Q ∈ 𝒬 then 1 else 0 : R)
      = (cliqueMult 𝒬 e : R) := by
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one, cliqueMult]
  congr 2
  ext Q
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨⟨h𝒬 Q h2, h1⟩, h2⟩

/-- A `K_q^r`-decomposition gives an integral `K_q^r`-decomposition (its indicator). -/
theorem IsDecomposition.isIntegralDecomposition {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) :
    IsIntegralDecomposition q r G (fun Q => if Q ∈ 𝒬 then 1 else 0) := by
  intro e he
  rw [sum_indicator_eq_cliqueMult h.card_eq, h.mult_eq e he]
  split_ifs <;> simp

/-- **Fractional `K_q^r`-decomposition** (Section 4.1): an assignment of non-negative real
weights to the copies of `K_q^r` in `G` such that the weights along each edge of `G` sum to
exactly `1`. -/
structure IsFractionalDecomposition (q r : ℕ) (G : Finset (Finset V)) (Φ : Finset V → ℝ) :
    Prop where
  nonneg : ∀ Q, 0 ≤ Φ Q
  support : ∀ Q, Φ Q ≠ 0 → Q.card = q ∧ cliqueEdges r Q ⊆ G
  sum_eq : ∀ e ∈ G, ∑ Q ∈ (univ.powersetCard q).filter (fun Q => e ⊆ Q), Φ Q = 1

/-- `G` admits a fractional `K_q^r`-decomposition. -/
def HasFractionalDecomposition (q r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∃ Φ, IsFractionalDecomposition q r G Φ

/-- A `K_q^r`-decomposition is also a fractional `K_q^r`-decomposition; hence admitting a
fractional decomposition is a necessary condition for admitting a decomposition. -/
theorem IsDecomposition.isFractionalDecomposition {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) :
    IsFractionalDecomposition q r G (fun Q => if Q ∈ 𝒬 then 1 else 0) := by
  refine ⟨fun Q => by split_ifs <;> norm_num, fun Q hQ => ?_, fun e he => ?_⟩
  · have hQ' : Q ∈ 𝒬 := by by_contra h'; simp [h'] at hQ
    refine ⟨h.card_eq Q hQ', fun e he => ?_⟩
    rw [cliqueEdges, mem_powersetCard] at he
    have := h.mult_eq e he.2
    have hpos : 0 < cliqueMult 𝒬 e := card_pos.2 ⟨Q, mem_filter.2 ⟨hQ', he.1⟩⟩
    split_ifs at this with hG
    · exact hG
    · omega
  · rw [sum_indicator_eq_cliqueMult h.card_eq, h.mult_eq e (h.rgraph e he), if_pos he]
    simp

/-- Admitting a decomposition implies admitting a fractional decomposition. -/
theorem HasDecomposition.hasFractionalDecomposition {q r : ℕ} {G : Finset (Finset V)}
    (h : HasDecomposition q r G) : HasFractionalDecomposition q r G :=
  h.elim fun _ h => ⟨_, h.isFractionalDecomposition⟩

end RefinedAbsorption
