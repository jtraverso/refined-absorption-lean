module
public import RequestProject.Multigraph.NibbleMulti
public import RequestProject.Multigraph.StrongReserves
public import RequestProject.Boost
public import RequestProject.Final

/-!
# The Existence Conjecture for all `λ`

We prove the Existence Conjecture (Conjecture 1.1 of the survey, Keevash's theorem) for every
`λ ≥ 1`, with simple designs (no repeated blocks), by the refined absorption method:

1. reserves `X` with many reserve cliques through every `r`-set (`strongReservesLemma`);
2. a refined efficient omni-absorber `A` for `X` (Theorem 1.10, already proved for `λ = 1`); let
   `F'` be the cliques used by its decompositions;
3. the multigraph `λ K_n^r` minus one copy of `A ∪ X` is written in `λ` layers: the layer
   `J = K_n^r \ (A ∪ X)` and `λ - 1` copies of `K_n^r`; the boost lemma gives clique families for
   both kinds of layers;
4. Corollary 2.4 for multigraphs (`nibbleWithReservesMulti_proved`), avoiding `F'`, covers the
   multigraph, using every edge of `X` at most once more;
5. the edges of `X` not used that extra time form a leftover `L ⊆ X`, which is automatically
   `K_q^r`-divisible (`isDivisible_of_count`), and is absorbed by `A`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-- If a family `P` of `q`-sets together with the `r`-graphs `A` and `L` covers every `r`-set
exactly `l` times, `A` is `K_q^r`-divisible and `l binom(n,r)` satisfies the design divisibility
conditions, then `L` is `K_q^r`-divisible. -/
theorem isDivisible_of_count {n q r l : ℕ} {P A L : Finset (Finset (Fin n))}
    (hPq : ∀ Q ∈ P, Q.card = q) (hA : IsRGraph r A) (hL : IsRGraph r L)
    (hAdiv : IsDivisible q r A) (hdiv : DesignDivisibility n q r l)
    (hid : ∀ T : Finset (Fin n), T.card = r →
      cliqueMult P T + (if T ∈ A then 1 else 0) + (if T ∈ L then 1 else 0) = l) :
    IsDivisible q r L := by
  intro S hS
  set E := (univ.powersetCard r).filter (fun T : Finset (Fin n) => S ⊆ T) with hE
  have h1 : ∑ T ∈ E, cliqueMult P T = (q - S.card).choose (r - S.card) * cliqueMult P S := by
    have := sum_weight_double_count q r P hPq (fun _ => (1 : ℕ)) S hS.le
    simp only [sum_const, smul_eq_mul, mul_one] at this
    exact this
  have h2 := deg_eq_sum_indicator hA S
  have h3 := deg_eq_sum_indicator hL S
  have h4 : E.card = (n - S.card).choose (r - S.card) := by
    have := deg_completeRGraph (n := n) (r := r) (S := S) hS.le
    rw [← this]; rfl
  have hsum : ∑ T ∈ E, (cliqueMult P T + (if T ∈ A then 1 else 0) + (if T ∈ L then 1 else 0)) =
      ∑ T ∈ E, l := sum_congr rfl fun T hT => hid T (mem_powersetCard.1 (mem_filter.1 hT).1).2
  rw [sum_add_distrib, sum_add_distrib, h1, ← h2, ← h3, sum_const, h4, smul_eq_mul] at hsum
  have hd := hdiv S.card hS
  have hAd := hAdiv S hS
  rw [mul_comm] at hd
  rw [← hsum] at hd
  exact (Nat.dvd_add_right (dvd_add (dvd_mul_right _ _) hAd)).1 hd

theorem layerCount_first_then_const {V : Type*} [DecidableEq V] {J K : Finset (Finset V)}
    {T : Finset V} (hT : T ∈ K) (k : ℕ) :
    layerCount (k + 1) (fun j => if j = 0 then J else K) T = (if T ∈ J then 1 else 0) + k := by
  induction k with
  | zero => rw [layerCount_succ, layerCount_zero]; simp
  | succ k ih => rw [layerCount_succ, ih]; simp [hT]; omega

/-- **The Existence Conjecture for every `λ`**, from Theorem 1.10 (refined efficient
omni-absorbers). -/
theorem existenceConjecture_of_omniAbsorber (hOmni : RefinedEfficientOmniAbsorber) :
    ExistenceConjecture := by
  classical
  intro q r l hr hrq hl
  have hr1 : 1 ≤ r := by omega
  obtain ⟨C, hC1, hOmni'⟩ := hOmni q r hr1 hrq
  obtain ⟨ε, hε, -, n₂, hBoost'⟩ := boostLemma q r hr1 hrq
  obtain ⟨α, hα, -, n₃, hMulti⟩ := nibbleWithReservesMulti_proved q r hr1 hrq (1 / 2)
    (by norm_num) (by norm_num) (1 / 4) (by norm_num) (by norm_num) l C
  obtain ⟨δ, hδ, n₁, hRes'⟩ := strongReservesLemma q r hr1 hrq α hα
  obtain ⟨n₄, hn₄⟩ := Filter.eventually_atTop.1
    (eventually_parameter_bounds q r C hr hC1 ε δ hε hδ)
  refine ⟨max (max n₁ n₂) (max n₃ n₄), fun n hn hdiv => ?_⟩
  obtain ⟨hn1, hD, hdeg, hconv⟩ := hn₄ n (by omega)
  set K := completeRGraph (Fin n) r with hKdef
  -- Step 1: reserves
  obtain ⟨X, hXK, hXdeg, hXres⟩ := hRes' n (by omega)
  have hXr : IsRGraph r X := fun e he => (mem_powersetCard.1 (hXK he)).2
  -- Step 2: refined efficient omni-absorber for the reserves
  obtain ⟨A, F, QA, hA, hCref, hAdeg⟩ := hOmni' n X ((n : ℝ) ^ (1 - δ)) hXr hXdeg hD
  have hAr : IsRGraph r A := hA.isDecomposition_self.rgraph
  have hAK : A ⊆ K := fun e he => mem_powersetCard.2 ⟨subset_univ _, hAr e he⟩
  set F' := (X.powerset.filter (fun L => IsDivisible q r L)).biUnion QA with hF'def
  have hF'mult : ∀ e : Finset (Fin n), e.card = r → cliqueMult F' e ≤ C := by
    intro e he
    by_cases heXA : e ∈ X ∪ A
    · refine le_trans (card_le_card (filter_subset_filter _ ?_)) (hCref e heXA)
      intro Q hQ
      obtain ⟨L, hL, hQL⟩ := mem_biUnion.1 hQ
      obtain ⟨hL1, hL2⟩ := mem_filter.1 hL
      exact hA.subset_family L (mem_powerset.1 hL1) hL2 hQL
    · apply le_of_eq_of_le _ (Nat.zero_le C)
      rw [cliqueMult, card_eq_zero, filter_eq_empty_iff]
      intro Q hQ heQ
      obtain ⟨L, hL, hQL⟩ := mem_biUnion.1 hQ
      obtain ⟨hL1, hL2⟩ := mem_filter.1 hL
      have := (hA.decomp L (mem_powerset.1 hL1) hL2).cliqueEdges_subset hQL
        (mem_powersetCard.2 ⟨heQ, he⟩)
      rcases mem_union.1 this with h | h
      · exact heXA (mem_union_right _ h)
      · exact heXA (mem_union_left _ (mem_powerset.1 hL1 h))
  -- Step 3: boost on the layers
  set J := K \ (A ∪ X) with hJdef
  have hJK : J ⊆ K := sdiff_subset
  have hJdeg : MinDegGE r J ((1 - ε) * n) := by
    intro S hS
    have h1 : deg K S ≤ deg J S + deg A S + deg X S := by
      unfold deg
      calc (K.filter (fun e => S ⊆ e)).card
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
    have h2 : deg K S = n - (r - 1) := by
      rw [hKdef, deg_completeRGraph (by omega), show r - S.card = 1 by omega,
        Nat.choose_one_right, show S.card = r - 1 by omega]
    have h3 : n ≤ (n - (r - 1)) + r := by omega
    have h3' : (n : ℝ) ≤ ((n - (r - 1) : ℕ) : ℝ) + r := by exact_mod_cast h3
    have h1' : ((deg K S : ℕ) : ℝ) ≤ deg J S + deg A S + deg X S := by exact_mod_cast h1
    rw [h2] at h1'
    have hAd := hAdeg S hS
    have hXd := hXdeg S hS
    nlinarith
  have hKdeg : MinDegGE r K ((1 - ε) * n) := by
    intro S hS
    refine (hJdeg S hS).trans ?_
    exact_mod_cast card_le_card (filter_subset_filter _ hJK)
  obtain ⟨HJ, hHJ, hHJreg⟩ := hBoost' n (by omega) J hJK hJdeg
  obtain ⟨HK, hHK, hHKreg⟩ := hBoost' n (by omega) K Subset.rfl hKdeg
  -- Step 4: the nibble with reserves for the multigraph `J + (λ - 1) K`
  set G : ℕ → Finset (Finset (Fin n)) := fun j => if j = 0 then J else K with hGdef
  set H : ℕ → Finset (Finset (Fin n)) := fun j => if j = 0 then HJ else HK with hHdef
  have hG : ∀ j < l, G j ⊆ K := by
    intro j _; by_cases hj : j = 0
    · simp only [hGdef, if_pos hj]; exact hJK
    · simp only [hGdef, if_neg hj]; exact Subset.rfl
  have hH : ∀ j < l, H j ⊆ cliquesOf q r (G j) := by
    intro j _; by_cases hj : j = 0
    · simp only [hGdef, hHdef, if_pos hj]; exact hHJ
    · simp only [hGdef, hHdef, if_neg hj]; exact hHK
  have hreg : ∀ j < l, ∀ e ∈ G j, |(cliqueMult (H j) e : ℝ) - (1 / 2) * (n.choose (q - r))|
      ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n.choose (q - r)) := by
    intro j _ e he; by_cases hj : j = 0
    · simp only [hGdef, hHdef, if_pos hj] at he ⊢
      exact clique_deg_conversion (by omega) (hHJreg e he) hconv
    · simp only [hGdef, hHdef, if_neg hj] at he ⊢
      exact clique_deg_conversion (by omega) (hHKreg e he) hconv
  have hres : ∀ j < l, ∀ e ∈ G j,
      (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card :=
    fun j hj e he => hXres e (hG j hj he)
  obtain ⟨P, hPq, hPF', hP⟩ := hMulti n (by omega) G H X F' hG hH hreg hF'mult hres
  -- Step 5: absorb the leftover
  have hlc : ∀ T : Finset (Fin n), T.card = r →
      layerCount l G T = (if T ∈ J then 1 else 0) + (l - 1) := by
    intro T hT
    have hTK : T ∈ K := mem_powersetCard.2 ⟨subset_univ _, hT⟩
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    rw [layerCount_first_then_const hTK k]; simp
  set U := X.filter (fun T => layerCount l G T < cliqueMult P T) with hUdef
  set L := X \ U with hLdef
  have hLX : L ⊆ X := sdiff_subset
  have hAX : Disjoint X A := hA.disjoint
  have hid : ∀ T : Finset (Fin n), T.card = r →
      cliqueMult P T + (if T ∈ A then 1 else 0) + (if T ∈ L then 1 else 0) = l := by
    intro T hT
    have hTK : T ∈ K := mem_powersetCard.2 ⟨subset_univ _, hT⟩
    obtain ⟨h1, h2⟩ := hP T hT
    have hLmem : T ∈ L ↔ T ∈ X ∧ ¬ (layerCount l G T < cliqueMult P T) := by
      simp only [hLdef, hUdef, mem_sdiff, mem_filter]; tauto
    rw [hlc T hT] at h1 h2 hLmem
    by_cases hTA : T ∈ A
    · have hTX : T ∉ X := fun h => disjoint_left.1 hAX h hTA
      have hTJ : T ∉ J := fun h => (mem_sdiff.1 h).2 (mem_union_left _ hTA)
      have hTL : T ∉ L := fun h => hTX (hLX h)
      simp only [hTA, hTX, hTJ, hTL, if_true, if_false] at h1 h2 ⊢
      omega
    · by_cases hTX : T ∈ X
      · have hTJ : T ∉ J := fun h => (mem_sdiff.1 h).2 (mem_union_right _ hTX)
        simp only [hTA, hTX, hTJ, if_true, if_false] at h1 h2 hLmem ⊢
        by_cases hlt : 0 + (l - 1) < cliqueMult P T
        · have hTL : T ∉ L := fun h => (hLmem.1 h).2 hlt
          simp only [hTL, if_false]; omega
        · have hTL : T ∈ L := hLmem.2 ⟨trivial, hlt⟩
          simp only [hTL, if_true]; omega
      · have hTJ : T ∈ J := mem_sdiff.2 ⟨hTK, by simp [hTA, hTX]⟩
        have hTL : T ∉ L := fun h => hTX (hLX h)
        simp only [hTA, hTX, hTJ, hTL, if_true, if_false] at h1 h2 ⊢
        omega
  have hAdiv : IsDivisible q r A := hA.isDecomposition_self.isDivisible
  have hLdiv : IsDivisible q r L :=
    isDivisible_of_count hPq hAr (fun e he => hXr e (hLX he)) hAdiv hdiv hid
  have hdec := hA.decomp L hLX hLdiv
  have hsub : QA L ⊆ F' := fun Q hQ =>
    mem_biUnion.2 ⟨L, mem_filter.2 ⟨mem_powerset.2 hLX, hLdiv⟩, hQ⟩
  have hdisj : Disjoint P (QA L) := disjoint_of_subset_right hsub hPF'
  refine ⟨P ∪ QA L, ⟨fun B hB => ?_, fun T hT => ?_⟩⟩
  · rcases mem_union.1 hB with h | h
    · exact hPq B h
    · exact hdec.card_eq B h
  · rw [cliqueMult_union_of_disjoint hdisj, hdec.mult_eq T hT]
    have := hid T hT
    by_cases hTA : T ∈ A
    · have hTL : T ∉ L := fun h => disjoint_left.1 hAX (hLX h) hTA
      simp only [hTA, hTL, mem_union, true_or, if_true, if_false] at this ⊢; omega
    · by_cases hTL : T ∈ L
      · simp only [hTA, hTL, mem_union, or_true, if_true, if_false] at this ⊢; omega
      · simp only [hTA, hTL, mem_union, or_false, if_false] at this ⊢; omega

/-- **The Existence Conjecture (Conjecture 1.1, Keevash's theorem) for every `λ ≥ 1`**, with
simple designs, proved by refined absorption. -/
theorem existenceConjecture_proved : ExistenceConjecture :=
  existenceConjecture_of_omniAbsorber Final.theorem_1_10

end RefinedAbsorption
