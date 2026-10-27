module
public import RefinedAbsorption.ReserveCover
public import RefinedAbsorption.BoostExistence

/-!
# Corollary 2.4 from a nibble with leftover degree control

Corollary 2.4 of the survey (`NibbleWithReserves`) does not follow from the classical nibble
(Theorem 1.3) alone: that theorem only bounds the *number* of uncovered edges, which could all
contain the same `(r-1)`-set and exhaust its reserves.  What is needed is the standard
strengthening of the nibble in which the uncovered edges have small `(r-1)`-degrees
(`NibbleLeftoverDegree`).  We show that this strengthening implies Corollary 2.4, in both the
survey's form and the general polynomial-error form used in `ExistenceProof.lean`
(`nibbleWithReservesGen_of_nibbleLeftoverDegree`): the leftover of the nibble is covered with
the reserves by the deterministic greedy algorithm of `ReserveCover.lean` (`reserve_cover`).

Consequently the Existence Conjecture for Steiner systems follows from Theorem 1.10 and the
nibble with leftover degree control (`steinerExistence_of_omniAbsorber_nibbleLeftoverDegree`).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter

/-- **Nibble with leftover degree control.**  For `q > r ≥ 1`, `ρ ∈ (0,1]` and `β ∈ (0,1)`
there is `γ > 0` such that for all large `n`: if `G ⊆ K_n^r` and `H ⊆ K_q^r(G)` are such that
every edge of `G` is in `(ρ ± n^{-β}) binom(n, q-r)` cliques of `H`, then there is a
`K_q^r`-packing `P` of `G` such that every `(r-1)`-set lies in at most `n^{1-γ}` edges of `G`
not covered by `P`.

This is the form of the Rödl nibble with "tracked" degrees (e.g. the pseudorandom hypergraph
matching theorems with test sets) applied to the auxiliary `binom(q,r)`-uniform hypergraph whose
vertices are the edges of `G` and whose edges are the cliques of `H`: it is roughly
`ρ binom(n, q-r)`-regular, with codegrees at most `n^{q-r-1}`.  It is stated here, not proved outright;
`RequestProject/WeightedNibbleBridge.lean` derives it from the weighted pseudorandom matching
theorem of Ehard–Glock–Joos (`nibbleLeftoverDegree_of_egjWeightedMatching`). -/
def NibbleLeftoverDegree : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ β : ℝ, 0 < β → β < 1 →
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G ⊆ completeRGraph (Fin n) r, ∀ H ⊆ cliquesOf q r G,
      (∀ e ∈ G, |(cliqueMult H e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-β) * (n.choose (q - r))) →
      ∃ P, IsPacking q r G P ∧ MaxDegLE r (G \ coveredEdges r P) ((n : ℝ) ^ (1 - γ))

/-- Combining a packing `P₁` of `G` with a packing `P₂` of `L ∪ X`, where `L` consists of
edges of `G` not covered by `P₁` and `X` is disjoint from `G`, gives a packing of `G ∪ X`. -/
theorem IsPacking.union_leftover {n q r : ℕ} {G X L P₁ P₂ : Finset (Finset (Fin n))}
    (h₁ : IsPacking q r G P₁) (h₂ : IsPacking q r (L ∪ X) P₂) (hGX : Disjoint G X)
    (hL : L ⊆ G \ coveredEdges r P₁) : IsPacking q r (G ∪ X) (P₁ ∪ P₂) := by
  refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun f hf => ?_⟩
  · rcases mem_union.1 hQ with h | h
    · exact h₁.card_eq Q h
    · exact h₂.card_eq Q h
  · rcases mem_union.1 hQ with h | h
    · exact (h₁.sub Q h).trans subset_union_left
    · refine (h₂.sub Q h).trans (union_subset_union ?_ Subset.rfl)
      exact hL.trans sdiff_subset
  · have hle : cliqueMult (P₁ ∪ P₂) f ≤ cliqueMult P₁ f + cliqueMult P₂ f := by
      unfold cliqueMult; rw [filter_union]; exact card_union_le _ _
    have h1 := h₁.mult_le f hf
    have h2 := h₂.mult_le f hf
    by_contra hcon
    have hp1 : 0 < cliqueMult P₁ f := by omega
    have hp2 : 0 < cliqueMult P₂ f := by omega
    obtain ⟨Q₁, hQ₁⟩ := card_pos.1 hp1
    obtain ⟨Q₂, hQ₂⟩ := card_pos.1 hp2
    rw [mem_filter] at hQ₁ hQ₂
    have hcov : f ∈ coveredEdges r P₁ :=
      mem_biUnion.2 ⟨Q₁, hQ₁.1, mem_powersetCard.2 ⟨hQ₁.2, hf⟩⟩
    have hf2 : f ∈ L ∪ X := h₂.sub Q₂ hQ₂.1 (mem_powersetCard.2 ⟨hQ₂.2, hf⟩)
    rcases mem_union.1 hf2 with h | h
    · exact (mem_sdiff.1 (hL h)).2 hcov
    · exact disjoint_left.1 hGX (h₁.coveredEdges_subset hcov) h

/-- **Corollary 2.4 (general polynomial error) from the nibble with leftover degree
control.** -/
theorem nibbleWithReservesGen_of_nibbleLeftoverDegree (h : NibbleLeftoverDegree) :
    NibbleWithReservesGen := by
  intro q r hr hrq ρ hρ hρ1 β hβ hβ1
  obtain ⟨γ, hγ, n₀, hn₀⟩ := h q r hr hrq ρ hρ hρ1 β hβ hβ1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set α : ℝ := min (γ / (2 * r)) (1 / 2) with hαdef
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hα2 : α ≤ 1 / 2 := min_le_right _ _
  have hαγ : 2 * α * r ≤ γ := by
    have : α ≤ γ / (2 * r) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (reserve_cover q r hr hα hα2 hαγ)
  refine ⟨α, hα, by linarith, max n₀ N, fun n hn G hGK H hHG hH X hXK hres => ?_⟩
  obtain ⟨P₁, hP₁, hdeg⟩ := hn₀ n (le_of_max_le_left hn) G hGK H hHG hH
  have hGX : Disjoint G X := by
    rw [disjoint_right]; intro f hf hfG
    exact (mem_sdiff.1 (hXK hf)).2 hfG
  obtain ⟨P₂, hP₂, hcov⟩ := hN n (le_of_max_le_right hn) (G \ coveredEdges r P₁) X
    (sdiff_subset.trans hGK) (disjoint_of_subset_left sdiff_subset hGX) hdeg
    (fun e he => hres e (mem_sdiff.1 he).1)
  refine ⟨P₁ ∪ P₂, hP₁.union_leftover hP₂ hGX Subset.rfl, fun e he => ?_⟩
  by_cases hc : e ∈ coveredEdges r P₁
  · obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.1 hc
    exact mem_biUnion.2 ⟨Q, mem_union_left _ hQ, heQ⟩
  · obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.1 (hcov (mem_sdiff.2 ⟨he, hc⟩))
    exact mem_biUnion.2 ⟨Q, mem_union_right _ hQ, heQ⟩

/-- **Corollary 2.4, exactly as stated in the survey**, from the nibble with leftover degree
control. -/
theorem nibbleWithReserves_of_nibbleLeftoverDegree (h : NibbleLeftoverDegree) :
    NibbleWithReserves :=
  (nibbleWithReservesGen_of_nibbleLeftoverDegree h).nibbleWithReserves

/-- **The Existence Conjecture for Steiner systems** from Theorem 1.10 (refined efficient
omni-absorbers) and the nibble with leftover degree control. -/
theorem steinerExistence_of_omniAbsorber_nibbleLeftoverDegree
    (hOmni : RefinedEfficientOmniAbsorber) (hNib : NibbleLeftoverDegree) :
    SteinerExistenceConjecture :=
  steinerExistence_of_omniAbsorber_nibbleWithReserves hOmni
    (nibbleWithReserves_of_nibbleLeftoverDegree hNib)

end RefinedAbsorption
