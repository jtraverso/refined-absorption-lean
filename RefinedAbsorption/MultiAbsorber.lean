module
public import RefinedAbsorption.Counting

/-!
# Multi-absorbers and integral decompositions (Section 3.1)

A *multi-absorber* for an `r`-graph `L` is a multi-`r`-graph `A` (parallel edges allowed) with
a `K_q^r`-decomposition `Q₁` of `L + A` and a `K_q^r`-decomposition `Q₂` of `A`, where now a
decomposition is a *multiset* of cliques.  The paper notes that this is equivalent to an
integral `K_q^r`-decomposition of `L` (Definition 3.1): the positive cliques decompose `L + A`
and the negative cliques decompose `A`.  We prove this equivalence, and deduce that the theorem
of Graver–Jurkat and Wilson (Theorem 3.2) yields multi-absorbers.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A `K_q^r`-decomposition of the multi-`r`-graph with edge multiplicities `M` by a multiset
`𝒬` of copies of `K_q^r`: every `r`-set `e` lies in exactly `M e` cliques of `𝒬` (counted with
multiplicity). -/
def IsMultiDecomposition (q r : ℕ) (M : Finset V → ℕ) (𝒬 : Multiset (Finset V)) : Prop :=
  (∀ Q ∈ 𝒬, Q.card = q) ∧
    ∀ e : Finset V, e.card = r → (𝒬.filter (fun Q => e ⊆ Q)).card = M e

/-- A `K_q^r`-multi-absorber for `L`: a multi-`r`-graph `A` such that both `L + A` and `A`
admit `K_q^r`-decompositions (as multisets of cliques). -/
def IsMultiAbsorber (q r : ℕ) (L : Finset (Finset V)) (A : Finset V → ℕ) : Prop :=
  (∀ e, A e ≠ 0 → e.card = r) ∧
    (∃ Q₁, IsMultiDecomposition q r (fun e => A e + if e ∈ L then 1 else 0) Q₁) ∧
    (∃ Q₂, IsMultiDecomposition q r A Q₂)

/-- Counting cliques of a multiset of `q`-sets containing `e`, via multiplicities. -/
theorem card_filter_eq_sum_count {q : ℕ} {𝒬 : Multiset (Finset V)} (h𝒬 : ∀ Q ∈ 𝒬, Q.card = q)
    (e : Finset V) :
    (𝒬.filter (fun Q => e ⊆ Q)).card
      = ∑ Q ∈ (univ.powersetCard q).filter (fun Q => e ⊆ Q), 𝒬.count Q := by
  rw [← Multiset.sum_count_eq_card (s := univ.powersetCard q), sum_filter]
  · simp only [Multiset.count_filter]
  · intro a ha
    exact mem_powersetCard.2 ⟨subset_univ _, h𝒬 a (Multiset.mem_of_mem_filter ha)⟩

/-- The multiset of `q`-sets in which each `q`-set `Q` appears `n Q` times. -/
def cliqueMultiset (q : ℕ) (n : Finset V → ℕ) : Multiset (Finset V) :=
  (univ.powersetCard q).val.bind (fun Q => Multiset.replicate (n Q) Q)

theorem count_cliqueMultiset (q : ℕ) (n : Finset V → ℕ) (Q : Finset V) :
    (cliqueMultiset q n).count Q = if Q.card = q then n Q else 0 := by
  rw [cliqueMultiset, Multiset.count_bind]
  change ∑ Q' ∈ univ.powersetCard q, (Multiset.replicate (n Q') Q').count Q = _
  simp only [Multiset.count_replicate]
  rw [sum_ite_eq']
  simp [mem_powersetCard]

omit [DecidableEq V] in
theorem card_eq_of_mem_cliqueMultiset {q : ℕ} {n : Finset V → ℕ} {Q : Finset V}
    (hQ : Q ∈ cliqueMultiset q n) : Q.card = q := by
  obtain ⟨Q', hQ', hQQ'⟩ := Multiset.mem_bind.1 hQ
  rw [Multiset.eq_of_mem_replicate hQQ']
  exact (mem_powersetCard.1 hQ').2

/-- **Multi-absorbers are integral decompositions** (Section 3.1).  An `r`-graph `L` admits an
integral `K_q^r`-decomposition if and only if it has a `K_q^r`-multi-absorber. -/
theorem exists_integralDecomposition_iff_exists_multiAbsorber (q r : ℕ)
    (L : Finset (Finset V)) :
    (∃ Φ, IsIntegralDecomposition q r L Φ) ↔ ∃ A, IsMultiAbsorber q r L A := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    set Q₁ := cliqueMultiset q (fun Q => (Φ Q).toNat)
    set Q₂ := cliqueMultiset q (fun Q => (-Φ Q).toNat)
    let A : Finset V → ℕ := fun e => if e.card = r then (Q₂.filter (fun Q => e ⊆ Q)).card else 0
    refine ⟨A, fun e he => ?_, ⟨Q₁, fun Q hQ => card_eq_of_mem_cliqueMultiset hQ, fun e he => ?_⟩,
      ⟨Q₂, fun Q hQ => card_eq_of_mem_cliqueMultiset hQ, fun e he => ?_⟩⟩
    · by_contra h; exact he (if_neg h)
    · simp only [A, if_pos he]
      rw [card_filter_eq_sum_count (fun Q hQ => card_eq_of_mem_cliqueMultiset hQ),
        card_filter_eq_sum_count (fun Q hQ => card_eq_of_mem_cliqueMultiset hQ)]
      have h1 := hΦ e he
      have hc : ∀ Q ∈ (univ.powersetCard q).filter (fun Q => e ⊆ Q), Q.card = q :=
        fun Q hQ => (mem_powersetCard.1 (mem_filter.1 hQ).1).2
      rw [sum_congr rfl fun Q hQ => by rw [count_cliqueMultiset, if_pos (hc Q hQ)],
        sum_congr rfl fun Q hQ => (by rw [count_cliqueMultiset, if_pos (hc Q hQ)] :
          Q₂.count Q = (-Φ Q).toNat)]
      rw [← Int.natCast_inj]
      push_cast
      have : ∀ Q, ((Φ Q).toNat : ℤ) = ((-Φ Q).toNat : ℤ) + Φ Q := by
        intro Q; omega
      simp only [this, sum_add_distrib, h1]
    · simp [A, he]
  · rintro ⟨A, -, ⟨Q₁, hQ₁c, hQ₁⟩, ⟨Q₂, hQ₂c, hQ₂⟩⟩
    refine ⟨fun Q => (Q₁.count Q : ℤ) - Q₂.count Q, fun e he => ?_⟩
    have h1 := hQ₁ e he
    have h2 := hQ₂ e he
    rw [card_filter_eq_sum_count hQ₁c] at h1
    rw [card_filter_eq_sum_count hQ₂c] at h2
    simp only at h1
    rw [sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, h1, h2]
    split_ifs <;> simp

/-- **Theorem 3.2** (Graver–Jurkat, Wilson), as a proposition: for `q > r ≥ 1`, every
`K_q^r`-divisible `r`-graph `L` with `v(L) ≥ q + r` admits an integral `K_q^r`-decomposition.
(Stated here, not proved.) -/
def GraverJurkatWilson : Prop :=
  ∀ (q r : ℕ) (W : Type) [DecidableEq W] [Fintype W] (L : Finset (Finset W)),
    1 ≤ r → r < q → IsRGraph r L → IsDivisible q r L → q + r ≤ (vertexSet L).card →
      ∃ Φ, IsIntegralDecomposition q r L Φ

/-- Assuming the theorem of Graver–Jurkat and Wilson, every `K_q^r`-divisible `r`-graph on at
least `q + r` vertices has a `K_q^r`-multi-absorber. -/
theorem exists_multiAbsorber_of_graverJurkatWilson (hGJW : GraverJurkatWilson)
    {W : Type} [DecidableEq W] [Fintype W] {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q)
    {L : Finset (Finset W)} (hL : IsRGraph r L) (hdiv : IsDivisible q r L)
    (hv : q + r ≤ (vertexSet L).card) : ∃ A, IsMultiAbsorber q r L A :=
  (exists_integralDecomposition_iff_exists_multiAbsorber q r L).1
    (hGJW q r W L hr hrq hL hdiv hv)

end RefinedAbsorption
