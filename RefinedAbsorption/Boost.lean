module
public import RefinedAbsorption.Statements
public import RefinedAbsorption.BeckFiala
public import RefinedAbsorption.Gadget

/-!
# Proof of the boost lemma (Lemma 2.2)

We prove `BoostLemma`: for `q > r ≥ 1` there is `ε > 0` such that for all large `n`, every
`J ⊆ K_n^r` with `δ_{r-1}(J) ≥ (1-ε) n` contains a family `H` of copies of `K_q^r` such that
every edge of `J` lies in `(1/2 ± n^{-1/3}) binom(n-r, q-r)` members of `H`.

The proof is deterministic:

1. **Counting.**  Since every `(r-1)`-set has at most `εn` non-neighbours in `J`, for an edge
   `e ∈ J` at most `2^r ε n^s` of the `s`-sets `T` disjoint from `e` fail to span a clique of
   `J` together with `e` (`card_badT_le`).
2. **Fractional version** (`exists_fractional_boost`).  Give every clique of `J` weight `1/2`;
   an edge `e` then receives weight `k(e)/2` where `k(e) ≥ binom(n-r, q-r) - 2^r ε n^{q-r}`.
   The deficit `d(e)` is corrected exactly, using the edge gadgets of `Gadget.lean` on all
   `q`-sets `W` such that `e ∪ W` is a clique of `J`, each with weight `d(e)/#W`.  The counting
   bounds show that every clique weight stays in `[0, 1]`.
3. **Rounding** (`beck_fiala`).  Every clique contains `binom(q, r)` edges, so iterated rounding
   gives a `0/1` weighting, i.e. a family `H`, with error at most `binom(q, r)` on every edge;
   this is at most `n^{-1/3} binom(n-r, q-r)` for large `n`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

section Counting

variable {n r : ℕ} {J : Finset (Finset (Fin n))} {ε : ℝ}

/-- Every `(r-1)`-set has at most `εn` non-neighbours in `J`. -/
theorem card_nonNbr_le (hJK : J ⊆ completeRGraph (Fin n) r)
    (hdeg : MinDegGE r J ((1 - ε) * n)) {S : Finset (Fin n)} (hS : S.card + 1 = r) :
    (((univ \ S).filter (fun v => insert v S ∉ J)).card : ℝ) ≤ ε * n := by
  classical
  set good := (univ \ S).filter (fun v => insert v S ∈ J) with hgood
  set bad := (univ \ S).filter (fun v => insert v S ∉ J) with hbad
  have hSn : S.card ≤ n := by simpa using card_le_univ S
  have hsum : good.card + bad.card = n - S.card := by
    rw [hgood, hbad, card_filter_add_card_filter_not, card_sdiff_of_subset (subset_univ _),
      card_univ, Fintype.card_fin]
  have hdg : deg J S ≤ good.card := by
    unfold deg
    apply card_le_card_of_surjOn (fun v => insert v S)
    intro e he
    simp only [coe_filter, Set.mem_setOf_eq] at he
    have hecard : e.card = r := (mem_powersetCard.1 (hJK he.1)).2
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e \ S := by
      have : (e \ S).card = 1 := by rw [card_sdiff_of_subset he.2]; omega
      obtain ⟨v, hv⟩ := card_eq_one.1 this; exact ⟨v, by simp [hv]⟩
    have heq : insert v S = e := by
      apply eq_of_subset_of_card_le (insert_subset (mem_sdiff.1 hv).1 he.2)
      rw [card_insert_of_notMem (mem_sdiff.1 hv).2]; omega
    refine ⟨v, ?_, heq⟩
    simp [hgood, (mem_sdiff.1 hv).2, heq, he.1]
  have h1 := hdeg S hS
  have h2 : (bad.card : ℝ) + good.card = n - S.card := by
    rw [add_comm]
    exact_mod_cast (by rw [hsum]; push_cast [hSn]; ring :
      ((good.card + bad.card : ℕ) : ℝ) = n - S.card)
  have h3 : (deg J S : ℝ) ≤ good.card := by exact_mod_cast hdg
  have h4 : (S.card : ℝ) + 1 = r := by exact_mod_cast hS
  have h5 : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  nlinarith

theorem eps_mul_nonneg (hJK : J ⊆ completeRGraph (Fin n) r)
    (hdeg : MinDegGE r J ((1 - ε) * n)) {e : Finset (Fin n)} (he : e.card = r) (hr : 1 ≤ r) :
    0 ≤ ε * n := by
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := e) (n := r - 1) (by omega)
  exact le_trans (Nat.cast_nonneg _) (card_nonNbr_le hJK hdeg (S := S) (by omega))

/-- Few `p`-sets `P` outside `e` complete a given `U ⊊ e` to a non-edge. -/
theorem card_badP_le (hJK : J ⊆ completeRGraph (Fin n) r)
    (hdeg : MinDegGE r J ((1 - ε) * n)) {e U : Finset (Fin n)} (hUe : U ⊆ e)
    (he : e.card = r) (hU : U.card < r) :
    ((((univ \ e).powersetCard (r - U.card)).filter (fun P => U ∪ P ∉ J)).card : ℝ) ≤
      ε * n * n ^ (r - U.card - 1) := by
  classical
  set p := r - U.card with hp
  have hεn := eps_mul_nonneg hJK hdeg he (by omega)
  have hsub : ((univ \ e).powersetCard p).filter (fun P => U ∪ P ∉ J) ⊆
      ((univ \ e).powersetCard (p - 1)).biUnion (fun P' =>
        ((univ \ (U ∪ P')).filter (fun v => insert v (U ∪ P') ∉ J)).image
          (fun v => insert v P')) := by
    intro P hP
    rw [mem_filter, mem_powersetCard] at hP
    obtain ⟨⟨hPe, hPc⟩, hPJ⟩ := hP
    obtain ⟨v, hv⟩ : P.Nonempty := card_pos.1 (by omega)
    have hve : v ∉ e := (mem_sdiff.1 (hPe hv)).2
    rw [mem_biUnion]
    refine ⟨P.erase v, mem_powersetCard.2 ⟨(erase_subset _ _).trans hPe, by
      rw [card_erase_of_mem hv]; omega⟩, mem_image.2 ⟨v, ?_, insert_erase hv⟩⟩
    rw [mem_filter, mem_sdiff, mem_union, not_or]
    refine ⟨⟨mem_univ _, fun h => hve (hUe h), notMem_erase _ _⟩, ?_⟩
    rwa [← union_insert, insert_erase hv]
  have hcard := card_le_card hsub
  have h1 : ((((univ \ e).powersetCard (p - 1)).biUnion (fun P' =>
        ((univ \ (U ∪ P')).filter (fun v => insert v (U ∪ P') ∉ J)).image
          (fun v => insert v P'))).card : ℝ) ≤
      ∑ P' ∈ (univ \ e).powersetCard (p - 1), ε * n := by
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    refine sum_le_sum fun P' hP' => ?_
    rw [mem_powersetCard] at hP'
    refine (Nat.cast_le.2 card_image_le).trans (card_nonNbr_le hJK hdeg ?_)
    rw [card_union_of_disjoint (disjoint_of_subset_left hUe
      (disjoint_of_subset_right hP'.1 disjoint_sdiff)), hP'.2]
    omega
  rw [sum_const, nsmul_eq_mul, card_powersetCard] at h1
  have h2 : (((univ \ e).card.choose (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ (p - 1) := by
    have : (univ \ e).card ≤ n := by simpa using card_le_univ (univ \ e)
    exact_mod_cast (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left this _)
  calc _ ≤ _ := Nat.cast_le.2 hcard
    _ ≤ _ := h1
    _ ≤ (n : ℝ) ^ (p - 1) * (ε * n) := mul_le_mul_of_nonneg_right h2 hεn
    _ = _ := by ring

theorem ccount_le {m s j n : ℕ} (hm : m ≤ n) :
    ccount m s j ≤ if s ≤ j then n ^ (j - s) else 0 := by
  unfold ccount
  split_ifs
  · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  · rfl

/-- For an edge `e ∈ J`, at most `2^r ε n^s` of the `s`-sets `T` disjoint from `e` are such
that `e ∪ T` is not a clique of `J`. -/
theorem card_badT_le (hJK : J ⊆ completeRGraph (Fin n) r)
    (hdeg : MinDegGE r J ((1 - ε) * n)) (hr : 1 ≤ r) {e : Finset (Fin n)} (heJ : e ∈ J) (s : ℕ) :
    ((((univ \ e).powersetCard s).filter (fun T => ¬ cliqueEdges r (e ∪ T) ⊆ J)).card : ℝ) ≤
      2 ^ r * ε * n ^ s := by
  classical
  have he : e.card = r := (mem_powersetCard.1 (hJK heJ)).2
  have hεn := eps_mul_nonneg hJK hdeg he hr
  have hn : 0 < n := by
    have := card_le_univ e; simp at this; omega
  have hε : 0 ≤ ε := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  set badP : Finset (Fin n) → Finset (Finset (Fin n)) := fun U =>
    ((univ \ e).powersetCard (r - U.card)).filter (fun P => U ∪ P ∉ J) with hbadP
  have hsub : ((univ \ e).powersetCard s).filter (fun T => ¬ cliqueEdges r (e ∪ T) ⊆ J) ⊆
      (e.powerset.filter (fun U => U.card < r)).biUnion (fun U => (badP U).biUnion
        (fun P => ((univ \ e).powersetCard s).filter (fun T => P ⊆ T))) := by
    intro T hT
    rw [mem_filter] at hT
    obtain ⟨hTs, hTJ⟩ := hT
    obtain ⟨f, hf, hfJ⟩ := not_subset.1 hTJ
    rw [cliqueEdges, mem_powersetCard] at hf
    have hU : (f ∩ e).card < r := by
      by_contra hcon
      have h1 : f ∩ e = e := eq_of_subset_of_card_le inter_subset_right (by omega)
      have h2 : f = e := (eq_of_subset_of_card_le (h1 ▸ inter_subset_left : e ⊆ f)
        (by omega)).symm
      exact hfJ (h2 ▸ heJ)
    have hsplit := card_sdiff_add_card_inter f e
    rw [mem_biUnion]
    refine ⟨f ∩ e, mem_filter.2 ⟨mem_powerset.2 inter_subset_right, hU⟩, ?_⟩
    rw [mem_biUnion]
    refine ⟨f \ e, ?_, mem_filter.2 ⟨hTs, ?_⟩⟩
    · rw [hbadP, mem_filter, mem_powersetCard]
      refine ⟨⟨sdiff_subset_sdiff (subset_univ _) Subset.rfl, by omega⟩, ?_⟩
      have : f ∩ e ∪ f \ e = f := by ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
      rwa [this]
    · intro x hx
      rw [mem_sdiff] at hx
      rcases mem_union.1 (hf.1 hx.1) with h | h
      · exact absurd h hx.2
      · exact h
  have hcard := card_le_card hsub
  refine (Nat.cast_le.2 hcard).trans ?_
  refine (Nat.cast_le.2 card_biUnion_le).trans ?_
  push_cast
  have hU : ∀ U ∈ e.powerset.filter (fun U => U.card < r),
      ((((badP U).biUnion (fun P => ((univ \ e).powersetCard s).filter
        (fun T => P ⊆ T))).card : ℕ) : ℝ) ≤ ε * n ^ s := by
    intro U hU
    rw [mem_filter, mem_powerset] at hU
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    have hP : ∀ P ∈ badP U, ((((univ \ e).powersetCard s).filter (fun T => P ⊆ T)).card : ℝ) ≤
        if r - U.card ≤ s then (n : ℝ) ^ (s - (r - U.card)) else 0 := by
      intro P hP
      rw [hbadP, mem_filter, mem_powersetCard] at hP
      rw [card_filter_superset_eq_ccount hP.1.1, hP.1.2]
      have := ccount_le (m := (univ \ e).card) (s := r - U.card) (j := s) (n := n)
        (by simpa using card_le_univ (univ \ e))
      split_ifs at this ⊢ <;> exact_mod_cast this
    refine (sum_le_sum hP).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hb := card_badP_le hJK hdeg hU.1 he hU.2
    split_ifs with h
    · calc ((badP U).card : ℝ) * (n : ℝ) ^ (s - (r - U.card))
          ≤ ε * n * n ^ (r - U.card - 1) * (n : ℝ) ^ (s - (r - U.card)) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = ε * (n ^ (1 + (r - U.card - 1) + (s - (r - U.card)))) := by ring
        _ = ε * n ^ s := by congr 2; omega
    · simp only [mul_zero]; positivity
  refine (sum_le_sum hU).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have : ((e.powerset.filter (fun U => U.card < r)).card : ℝ) ≤ 2 ^ r := by
    have := card_le_card (filter_subset (fun U : Finset (Fin n) => U.card < r) e.powerset)
    rw [card_powerset, he] at this
    exact_mod_cast this
  calc _ ≤ (2 : ℝ) ^ r * (ε * n ^ s) := mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := by ring

end Counting

/-- The number of pairs `(e, W)` (`e` an `r`-set, `W` a disjoint `q`-set) with `Q ⊆ e ∪ W`,
for a fixed `q`-set `Q`, is at most `2^{q+r} n^r`. -/
theorem card_pairs_le {n q r : ℕ} {Q : Finset (Fin n)} (hQ : Q.card = q)
    (E : Finset (Finset (Fin n))) (hE : E ⊆ completeRGraph (Fin n) r) :
    ∑ e ∈ E, (((univ \ e).powersetCard q).filter (fun W => Q ⊆ e ∪ W)).card ≤
      2 ^ (q + r) * n ^ r := by
  classical
  rw [← card_sigma]
  have hinj : Set.InjOn (fun p : (Σ _ : Finset (Fin n), Finset (Fin n)) =>
      (⟨(p.1 ∪ p.2) \ Q, p.1⟩ : Σ _ : Finset (Fin n), Finset (Fin n)))
      (E.sigma (fun e => ((univ \ e).powersetCard q).filter (fun W => Q ⊆ e ∪ W))) := by
    rintro ⟨e, W⟩ hp ⟨e', W'⟩ hp' h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_powersetCard] at hp hp'
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : e = e' := eq_of_heq h2
    subst h2'
    have hu : e ∪ W = e ∪ W' := by
      rw [← sdiff_union_of_subset hp.2.2, ← sdiff_union_of_subset hp'.2.2, h1]
    have hW : W = (e ∪ W) \ e := by
      rw [union_sdiff_left, sdiff_eq_self_of_disjoint]
      exact disjoint_of_subset_left hp.2.1.1 disjoint_sdiff_self_left
    have hW' : W' = (e ∪ W') \ e := by
      rw [union_sdiff_left, sdiff_eq_self_of_disjoint]
      exact disjoint_of_subset_left hp'.2.1.1 disjoint_sdiff_self_left
    rw [hW, hW', hu]
  have hmaps : Set.MapsTo (fun p : (Σ _ : Finset (Fin n), Finset (Fin n)) =>
      (⟨(p.1 ∪ p.2) \ Q, p.1⟩ : Σ _ : Finset (Fin n), Finset (Fin n)))
      (E.sigma (fun e => ((univ \ e).powersetCard q).filter (fun W => Q ⊆ e ∪ W)))
      ((univ.powersetCard r).sigma (fun R => (Q ∪ R).powersetCard r)) := by
    rintro ⟨e, W⟩ hp
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_powersetCard] at hp ⊢
    obtain ⟨heE, ⟨hWe, hWc⟩, hQ'⟩ := hp
    have hec : e.card = r := (mem_powersetCard.1 (hE heE)).2
    have hdisj : Disjoint e W := disjoint_of_subset_right hWe disjoint_sdiff
    refine ⟨⟨subset_univ _, ?_⟩, ?_, hec⟩
    · rw [card_sdiff_of_subset hQ', card_union_of_disjoint hdisj]; omega
    · intro x hx
      by_cases hxQ : x ∈ Q
      · exact mem_union_left _ hxQ
      · exact mem_union_right _ (mem_sdiff.2 ⟨mem_union_left _ hx, hxQ⟩)
  refine (card_le_card_of_injOn _ hmaps hinj).trans ?_
  rw [card_sigma]
  calc ∑ R ∈ univ.powersetCard r, ((Q ∪ R).powersetCard r).card
      ≤ ∑ R ∈ (univ : Finset (Fin n)).powersetCard r, 2 ^ (q + r) := by
        refine sum_le_sum fun R hR => ?_
        rw [card_powersetCard]
        refine (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) ?_)
        refine (card_union_le _ _).trans ?_
        rw [hQ, (mem_powersetCard.1 hR).2]
    _ ≤ 2 ^ (q + r) * n ^ r := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.choose_le_pow _ _)

/-- A lower bound for binomial coefficients. -/
theorem choose_sub_ge {n r k : ℕ} (hn : 2 * (k + r) ≤ n) :
    ((n : ℝ) / 2) ^ k / k.factorial ≤ ((n - r).choose k : ℝ) := by
  have h := Nat.pow_le_choose (α := ℝ) k (n - r)
  refine le_trans ?_ h
  gcongr
  have : ((n - r + 1 - k : ℕ) : ℝ) = (n : ℝ) - r + 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub (by omega)]; simp
  rw [this]
  have : (2 : ℝ) * (k + r) ≤ n := by exact_mod_cast hn
  linarith


/-! ### The fractional boost -/

/-- The `q`-sets `W` disjoint from `e` such that `e ∪ W` is a clique of `J`. -/
def gadgetSets {n : ℕ} (q r : ℕ) (J : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  ((univ \ e).powersetCard q).filter (fun W => cliqueEdges r (e ∪ W) ⊆ J)

/-- Half of the number of copies of `K_q^r` containing `e` which are missing from `J`. -/
noncomputable def deficit {n : ℕ} (q r : ℕ) (J : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : ℝ :=
  (((n - r).choose (q - r) : ℕ) - (cliqueMult (cliquesOf q r J) e : ℝ)) / 2

/-- The total gadget correction received by the `q`-set `Q`. -/
noncomputable def correction {n : ℕ} (q r : ℕ) (J : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) : ℝ :=
  ∑ e ∈ J, ∑ W ∈ gadgetSets q r J e, deficit q r J e / (gadgetSets q r J e).card *
    (if Q ⊆ e ∪ W then gadgetWeight q r (Q ∩ e).card else 0)

/-- The fractional clique weighting: `1/2` plus the gadget corrections on cliques of `J`. -/
noncomputable def fracWeight {n : ℕ} (q r : ℕ) (J : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) : ℝ :=
  if Q ∈ cliquesOf q r J then 1 / 2 + correction q r J Q else 0

theorem cliqueMult_add_bad {n q r : ℕ} (hrq : r ≤ q) {J : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (he : e.card = r) :
    cliqueMult (cliquesOf q r J) e +
      (((univ \ e).powersetCard (q - r)).filter (fun T => ¬ cliqueEdges r (e ∪ T) ⊆ J)).card =
      (n - r).choose (q - r) := by
  classical
  have h1 : cliqueMult (cliquesOf q r J) e =
      (((univ \ e).powersetCard (q - r)).filter (fun T => cliqueEdges r (e ∪ T) ⊆ J)).card := by
    unfold cliqueMult cliquesOf
    refine card_nbij' (fun Q => Q \ e) (fun T => e ∪ T) ?_ ?_ ?_ ?_
    · intro Q hQ
      simp only [coe_filter, mem_filter, mem_powersetCard, Set.mem_setOf_eq] at hQ ⊢
      obtain ⟨⟨⟨-, hQc⟩, hQJ⟩, heQ⟩ := hQ
      refine ⟨⟨sdiff_subset_sdiff (subset_univ _) Subset.rfl, ?_⟩, ?_⟩
      · rw [card_sdiff_of_subset heQ, hQc, he]
      · rwa [union_sdiff_of_subset heQ]
    · intro T hT
      simp only [coe_filter, mem_filter, mem_powersetCard, Set.mem_setOf_eq] at hT ⊢
      obtain ⟨⟨hTe, hTc⟩, hTJ⟩ := hT
      refine ⟨⟨⟨subset_univ _, ?_⟩, hTJ⟩, subset_union_left⟩
      rw [card_union_of_disjoint (disjoint_of_subset_right hTe disjoint_sdiff), he, hTc]
      omega
    · intro Q hQ
      simp only [coe_filter, mem_filter, Set.mem_setOf_eq] at hQ
      exact union_sdiff_of_subset hQ.2
    · intro T hT
      simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hT
      simp only
      rw [union_sdiff_left, sdiff_eq_self_of_disjoint]
      exact disjoint_of_subset_left hT.1.1 disjoint_sdiff_self_left
  rw [h1, card_filter_add_card_filter_not, card_powersetCard, card_sdiff_of_subset (subset_univ _),
    card_univ, Fintype.card_fin, he]

theorem card_gadgetSets_add_bad {n q r : ℕ} {J : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (he : e.card = r) :
    (gadgetSets q r J e).card +
      (((univ \ e).powersetCard q).filter (fun T => ¬ cliqueEdges r (e ∪ T) ⊆ J)).card =
      (n - r).choose q := by
  rw [gadgetSets, card_filter_add_card_filter_not, card_powersetCard,
    card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, he]

/-- The gadget corrections exactly make up the deficit of every edge `f ∈ J`. -/
theorem sum_correction {n q r : ℕ} (hrq : r ≤ q) {J : Finset (Finset (Fin n))}
    (hJK : J ⊆ completeRGraph (Fin n) r) {f : Finset (Fin n)} (hfJ : f ∈ J)
    (hG : (gadgetSets q r J f).card ≠ 0) :
    ∑ Q ∈ (cliquesOf q r J).filter (fun Q => f ⊆ Q), correction q r J Q = deficit q r J f := by
  classical
  have hfr : f.card = r := (mem_powersetCard.1 (hJK hfJ)).2
  unfold correction
  rw [sum_comm]
  have key : ∀ e ∈ J, ∀ W ∈ gadgetSets q r J e,
      ∑ Q ∈ (cliquesOf q r J).filter (fun Q => f ⊆ Q),
        (if Q ⊆ e ∪ W then gadgetWeight q r (Q ∩ e).card else 0) = if f = e then 1 else 0 := by
    intro e he W hW
    have her : e.card = r := (mem_powersetCard.1 (hJK he)).2
    rw [gadgetSets, mem_filter, mem_powersetCard] at hW
    obtain ⟨⟨hWe, hWc⟩, hWJ⟩ := hW
    have hdisj : Disjoint e W := disjoint_of_subset_right hWe disjoint_sdiff
    rw [← sum_filter]
    have hfil : ((cliquesOf q r J).filter (fun Q => f ⊆ Q)).filter (fun Q => Q ⊆ e ∪ W) =
        ((e ∪ W).powersetCard q).filter (fun Q => f ⊆ Q) := by
      ext Q
      simp only [cliquesOf, mem_filter, mem_powersetCard, subset_univ, true_and]
      constructor
      · rintro ⟨⟨⟨hQc, -⟩, hfQ⟩, hQeW⟩; exact ⟨⟨hQeW, hQc⟩, hfQ⟩
      · rintro ⟨⟨hQeW, hQc⟩, hfQ⟩
        exact ⟨⟨⟨hQc, (powersetCard_mono hQeW).trans hWJ⟩, hfQ⟩, hQeW⟩
    rw [hfil]
    by_cases hf : f ⊆ e ∪ W
    · exact gadget_sum hrq hdisj her hWc hf hfr
    · have hne : f ≠ e := by rintro rfl; exact hf subset_union_left
      rw [if_neg hne, sum_eq_zero]
      intro Q hQ
      rw [mem_filter, mem_powersetCard] at hQ
      exact absurd (hQ.2.trans hQ.1.1) hf
  rw [sum_congr rfl fun e he => (sum_comm.trans (sum_congr rfl fun W hW => by
    rw [← mul_sum, key e he W hW]))]
  rw [sum_eq_single f]
  · simp only [if_true, mul_one, sum_const, nsmul_eq_mul]
    field_simp
  · intro e _ hne
    exact sum_eq_zero fun W _ => by rw [if_neg (Ne.symm hne), mul_zero]
  · intro h; exact absurd hfJ h

/-- A bound for the gadget correction of a `q`-set. -/
theorem abs_correction_le {n q r : ℕ} {J : Finset (Finset (Fin n))}
    (hJK : J ⊆ completeRGraph (Fin n) r) {Q : Finset (Fin n)} (hQ : Q.card = q) {cmax : ℝ}
    (hcm : 0 ≤ cmax)
    (hc : ∀ e ∈ J, 0 ≤ deficit q r J e / (gadgetSets q r J e).card ∧
      deficit q r J e / (gadgetSets q r J e).card ≤ cmax) :
    |correction q r J Q| ≤ cmax * gadgetBound q r * (2 ^ (q + r) * n ^ r) := by
  classical
  unfold correction
  have hB := gadgetBound_nonneg q r
  have h1 : ∀ e ∈ J, ∀ W ∈ gadgetSets q r J e,
      |deficit q r J e / (gadgetSets q r J e).card *
        (if Q ⊆ e ∪ W then gadgetWeight q r (Q ∩ e).card else 0)| ≤
      cmax * gadgetBound q r * (if Q ⊆ e ∪ W then 1 else 0) := by
    intro e he W _
    rw [abs_mul, abs_of_nonneg (hc e he).1]
    split_ifs
    · rw [mul_one]
      exact mul_le_mul (hc e he).2 (abs_gadgetWeight_le _ _ _) (abs_nonneg _)
        ((hc e he).1.trans (hc e he).2)
    · simp
  calc _ ≤ ∑ e ∈ J, ∑ W ∈ gadgetSets q r J e, |deficit q r J e / (gadgetSets q r J e).card *
        (if Q ⊆ e ∪ W then gadgetWeight q r (Q ∩ e).card else 0)| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ e ∈ J, ∑ W ∈ gadgetSets q r J e,
          cmax * gadgetBound q r * (if Q ⊆ e ∪ W then 1 else 0) :=
        sum_le_sum fun e he => sum_le_sum fun W hW => h1 e he W hW
    _ = cmax * gadgetBound q r * ∑ e ∈ J, (((gadgetSets q r J e).filter
          (fun W => Q ⊆ e ∪ W)).card : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun e _ => ?_
        rw [← mul_sum, sum_boole]
    _ ≤ cmax * gadgetBound q r * (2 ^ (q + r) * n ^ r) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hcm hB)
        have := card_pairs_le hQ J hJK
        have h2 : ∑ e ∈ J, ((gadgetSets q r J e).filter (fun W => Q ⊆ e ∪ W)).card ≤
            ∑ e ∈ J, (((univ \ e).powersetCard q).filter (fun W => Q ⊆ e ∪ W)).card :=
          sum_le_sum fun e _ => card_le_card (filter_subset_filter _ (filter_subset _ _))
        exact_mod_cast h2.trans this

/-- **Fractional boost.**  If `J` has minimum `(r-1)`-degree at least `(1-ε)n` with `ε` small,
then `fracWeight` is a `[0,1]`-weighting of the copies of `K_q^r` in `J` giving every edge of
`J` total weight exactly `binom(n-r, q-r)/2`. -/
theorem fracWeight_spec {n q r : ℕ} {J : Finset (Finset (Fin n))} {ε : ℝ} (hr : 1 ≤ r)
    (hrq : r < q) (hn : 2 * (q + r) ≤ n) (hJK : J ⊆ completeRGraph (Fin n) r)
    (hdeg : MinDegGE r J ((1 - ε) * n))
    (hε1 : 2 ^ r * ε * (2 * q.factorial * 2 ^ q) ≤ 1)
    (hε2 : gadgetBound q r * 2 ^ (2 * q + 2 * r) * q.factorial * ε ≤ 1 / 2) :
    (∀ Q, 0 ≤ fracWeight q r J Q ∧ fracWeight q r J Q ≤ 1) ∧
      ∀ f ∈ J, ∑ Q ∈ (cliquesOf q r J).filter (fun Q => f ⊆ Q), fracWeight q r J Q =
        ((n - r).choose (q - r) : ℝ) / 2 := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfact : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  -- lower bound for the number of gadget sets
  set Nmin : ℝ := ((n : ℝ) / 2) ^ q / (2 * q.factorial) with hNmin
  have hNminpos : 0 < Nmin := by positivity
  have hε : 0 ≤ ε := by
    obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := r - 1)
      (by simp; omega)
    have := le_trans (Nat.cast_nonneg _) (card_nonNbr_le hJK hdeg (S := S) (by omega))
    nlinarith
  have hG : ∀ e ∈ J, Nmin ≤ (gadgetSets q r J e).card := by
    intro e he
    have her : e.card = r := (mem_powersetCard.1 (hJK he)).2
    have h1 := card_gadgetSets_add_bad (q := q) (J := J) her
    have h2 := card_badT_le hJK hdeg hr he q
    have h3 := choose_sub_ge (n := n) (r := r) (k := q) (by omega)
    have h4 : ((gadgetSets q r J e).card : ℝ) +
        ((((univ \ e).powersetCard q).filter (fun T => ¬ cliqueEdges r (e ∪ T) ⊆ J)).card : ℝ)
        = ((n - r).choose q : ℝ) := by exact_mod_cast h1
    have h5 : 2 ^ r * ε * (n : ℝ) ^ q ≤ ((n : ℝ) / 2) ^ q / (2 * q.factorial) := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      have : (0 : ℝ) < 2 ^ q := by positivity
      rw [le_div_iff₀ this]
      have hnq : (0 : ℝ) ≤ (n : ℝ) ^ q := by positivity
      nlinarith
    have h6 : ((n : ℝ) / 2) ^ q / q.factorial = 2 * Nmin := by
      rw [hNmin]; field_simp
    linarith
  -- bounds on the deficits
  set Dmax : ℝ := 2 ^ r * ε * (n : ℝ) ^ (q - r) / 2 with hDmax
  have hD : ∀ e ∈ J, 0 ≤ deficit q r J e ∧ deficit q r J e ≤ Dmax := by
    intro e he
    have her : e.card = r := (mem_powersetCard.1 (hJK he)).2
    have h1 := cliqueMult_add_bad (q := q) (J := J) hrq.le her
    have h2 := card_badT_le hJK hdeg hr he (q - r)
    have h3 : (cliqueMult (cliquesOf q r J) e : ℝ) +
        ((((univ \ e).powersetCard (q - r)).filter
          (fun T => ¬ cliqueEdges r (e ∪ T) ⊆ J)).card : ℝ)
        = ((n - r).choose (q - r) : ℝ) := by exact_mod_cast h1
    unfold deficit
    constructor <;> [linarith [Nat.cast_nonneg (α := ℝ) (((univ \ e).powersetCard (q - r)).filter
      (fun T => ¬ cliqueEdges r (e ∪ T) ⊆ J)).card]; linarith]
  set cmax : ℝ := Dmax / Nmin with hcmax
  have hc : ∀ e ∈ J, 0 ≤ deficit q r J e / (gadgetSets q r J e).card ∧
      deficit q r J e / (gadgetSets q r J e).card ≤ cmax := by
    intro e he
    have hGe := hG e he
    have hGpos : (0 : ℝ) < (gadgetSets q r J e).card := hNminpos.trans_le hGe
    refine ⟨div_nonneg (hD e he).1 hGpos.le, ?_⟩
    calc deficit q r J e / (gadgetSets q r J e).card ≤ Dmax / (gadgetSets q r J e).card :=
          div_le_div_of_nonneg_right (hD e he).2 hGpos.le
      _ ≤ Dmax / Nmin := div_le_div_of_nonneg_left (by positivity) hNminpos hGe
  have hcm : 0 ≤ cmax := by positivity
  have hcorr : ∀ Q ∈ cliquesOf q r J, |correction q r J Q| ≤ 1 / 2 := by
    intro Q hQ
    have hQc : Q.card = q := (mem_powersetCard.1 (mem_filter.1 hQ).1).2
    refine (abs_correction_le hJK hQc hcm hc).trans (le_trans (le_of_eq ?_) hε2)
    rw [hcmax, hDmax, hNmin]
    have hpow : (n : ℝ) ^ q = (n : ℝ) ^ (q - r) * (n : ℝ) ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hrq.le]
    rw [div_pow, hpow]
    field_simp
    ring
  refine ⟨fun Q => ?_, fun f hf => ?_⟩
  · unfold fracWeight
    split_ifs with hQ
    · have := abs_le.1 (hcorr Q hQ)
      constructor <;> linarith [this.1, this.2]
    · exact ⟨le_rfl, zero_le_one⟩
  · have hGf : (gadgetSets q r J f).card ≠ 0 := by
      have := hNminpos.trans_le (hG f hf)
      exact_mod_cast this.ne'
    have h1 : ∑ Q ∈ (cliquesOf q r J).filter (fun Q => f ⊆ Q), fracWeight q r J Q =
        ∑ Q ∈ (cliquesOf q r J).filter (fun Q => f ⊆ Q), (1 / 2 + correction q r J Q) :=
      sum_congr rfl fun Q hQ => if_pos (mem_filter.1 hQ).1
    rw [h1, sum_add_distrib, sum_correction hrq.le hJK hf hGf, sum_const, nsmul_eq_mul]
    unfold deficit cliqueMult
    ring


/-! ### Rounding and the boost lemma -/

/-- **Boost from a fractional boost, by iterated rounding.**  If `J ⊆ K_n^r` and the copies of
`K_q^r` in `J` carry `[0,1]`-weights giving every edge of `J` total weight `w`, then there is a
family `H` of copies of `K_q^r` in `J` such that every edge of `J` lies in `w ± binom(q, r)`
members of `H`. -/
theorem exists_boost_of_fractional {n q r : ℕ} {J : Finset (Finset (Fin n))}
    (hJK : J ⊆ completeRGraph (Fin n) r) (ψ : Finset (Fin n) → ℝ)
    (hψ : ∀ Q, 0 ≤ ψ Q ∧ ψ Q ≤ 1) (w : ℝ)
    (hload : ∀ f ∈ J, ∑ Q ∈ (cliquesOf q r J).filter (fun Q => f ⊆ Q), ψ Q = w) :
    ∃ H ⊆ cliquesOf q r J, ∀ e ∈ J, |(cliqueMult H e : ℝ) - w| ≤ q.choose r := by
  classical
  set Ω := cliquesOf q r J
  have ht : ∀ Q, (J.filter (fun e => Q ∈ Ω.filter (fun Q => e ⊆ Q))).card ≤ q.choose r := by
    intro Q
    by_cases hQ : Q ∈ Ω
    · have hQc : Q.card = q := (mem_powersetCard.1 (mem_filter.1 hQ).1).2
      calc _ ≤ (Q.powersetCard r).card := by
            refine card_le_card fun e he => ?_
            rw [mem_filter, mem_filter] at he
            exact mem_powersetCard.2 ⟨he.2.2, (mem_powersetCard.1 (hJK he.1)).2⟩
        _ = q.choose r := by rw [card_powersetCard, hQc]
    · rw [card_eq_zero.2]
      · exact Nat.zero_le _
      · exact filter_eq_empty_iff.2 fun e _ h => hQ (mem_filter.1 h).1
  obtain ⟨y, hy01, hy⟩ := beck_fiala J (fun e => Ω.filter (fun Q => e ⊆ Q)) (q.choose r) ht ψ hψ
  refine ⟨Ω.filter (fun Q => y Q = 1), filter_subset _ _, fun e he => ?_⟩
  have hU : ∀ Q ∈ Ω.filter (fun Q => e ⊆ Q), y Q = 0 ∨ y Q = 1 :=
    fun Q hQ => hy01 Q (mem_biUnion.2 ⟨e, he, hQ⟩)
  have h1 : (cliqueMult (Ω.filter (fun Q => y Q = 1)) e : ℝ) =
      ∑ Q ∈ Ω.filter (fun Q => e ⊆ Q), y Q := by
    have : ∑ Q ∈ Ω.filter (fun Q => e ⊆ Q), y Q =
        ∑ Q ∈ Ω.filter (fun Q => e ⊆ Q), (if y Q = 1 then (1 : ℝ) else 0) := by
      refine sum_congr rfl fun Q hQ => ?_
      rcases hU Q hQ with h | h <;> simp [h]
    rw [this, sum_boole, cliqueMult, filter_filter, filter_filter]
    congr 2
    ext Q; simp [and_comm]
  rw [h1, ← hload e he, ← sum_sub_distrib]
  exact hy e he

/-- **Boost with constant error.**  For `q > r ≥ 1` there is `ε ∈ (0,1)` such that for all
`n ≥ 2(q+r)`, every `J ⊆ K_n^r` with `δ_{r-1}(J) ≥ (1-ε) n` contains a family `H` of copies of
`K_q^r` such that every edge of `J` lies in `binom(n-r, q-r)/2 ± binom(q, r)` members of `H`. -/
theorem exists_boost_const_error {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ n : ℕ, 2 * (q + r) ≤ n → ∀ J ⊆ completeRGraph (Fin n) r,
      MinDegGE r J ((1 - ε) * n) → ∃ H ⊆ cliquesOf q r J, ∀ e ∈ J,
        |(cliqueMult H e : ℝ) - 1 / 2 * ((n - r).choose (q - r) : ℝ)| ≤ q.choose r := by
  set B := gadgetBound q r with hB
  have hB0 : 0 ≤ B := gadgetBound_nonneg q r
  have hfact : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  set den : ℝ := 2 ^ (2 * q + 2 * r + 2) * q.factorial * (B + 1) with hdendef
  have h4den : (4 : ℝ) ≤ den := by
    have h2 : (4 : ℝ) ≤ 2 ^ (2 * q + 2 * r + 2) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 := mul_le_mul h2 hfact (by norm_num) (by positivity)
    have h4 := mul_le_mul h3 (show (1 : ℝ) ≤ B + 1 by linarith) (by norm_num) (by positivity)
    rw [hdendef]; linarith
  set ε : ℝ := 1 / den with hεdef
  have hεpos : 0 < ε := by positivity
  have hεden : ε * den = 1 := by rw [hεdef]; field_simp
  have hε1' : ε < 1 := by
    rw [hεdef, div_lt_one (by positivity)]; linarith
  -- the smallness conditions on `ε`
  have hε1 : 2 ^ r * ε * (2 * q.factorial * 2 ^ q) ≤ 1 := by
    have h1 : 2 ^ r * ε * (2 * q.factorial * 2 ^ q) = ε * (2 ^ (q + r + 1) * q.factorial) := by
      ring
    have h2 : (2 : ℝ) ^ (q + r + 1) * q.factorial ≤ den := by
      have h3 : (2 : ℝ) ^ (q + r + 1) ≤ 2 ^ (2 * q + 2 * r + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 := mul_le_mul_of_nonneg_right h3 (show (0 : ℝ) ≤ q.factorial by positivity)
      have h5 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ B + 1 by linarith)
        (show (0 : ℝ) ≤ 2 ^ (2 * q + 2 * r + 2) * q.factorial by positivity)
      rw [hdendef]; linarith
    rw [h1, ← hεden]
    exact mul_le_mul_of_nonneg_left h2 hεpos.le
  have hε2 : B * 2 ^ (2 * q + 2 * r) * q.factorial * ε ≤ 1 / 2 := by
    have key : B * 2 ^ (2 * q + 2 * r) * q.factorial * ε * (4 * (B + 1)) = B := by
      rw [hdendef] at hεden
      linear_combination B * hεden
    have h4 : 0 < 4 * (B + 1) := by linarith
    nlinarith
  refine ⟨ε, hεpos, hε1', fun n hn2 J hJK hdeg => ?_⟩
  obtain ⟨hψ, hload⟩ := fracWeight_spec hr hrq hn2 hJK hdeg hε1 hε2
  obtain ⟨H, hH, hHe⟩ := exists_boost_of_fractional hJK _ hψ _ hload
  refine ⟨H, hH, fun e he => ?_⟩
  have h1 := hHe e he
  rwa [show ((n - r).choose (q - r) : ℝ) / 2 = 1 / 2 * ((n - r).choose (q - r) : ℝ) by ring] at h1

/-- **Lemma 2.2 (Boost).**  For `q > r ≥ 1` there is `ε ∈ (0,1)` such that for all large `n`,
every `J ⊆ K_n^r` with `δ_{r-1}(J) ≥ (1-ε) n` contains a family `H` of copies of `K_q^r` such
that every edge of `J` lies in `(1/2 ± n^{-1/3}) binom(n-r, q-r)` members of `H`. -/
theorem boostLemma : BoostLemma := by
  intro q r hr hrq
  obtain ⟨ε, hεpos, hε1', hb⟩ := exists_boost_const_error hr hrq
  -- the threshold for `n`
  set C : ℝ := 2 * q.choose r * (q - r).factorial with hC
  have hC1 : 1 ≤ C := by
    have h1 : (1 : ℝ) ≤ q.choose r := by exact_mod_cast Nat.choose_pos hrq.le
    have h2 : (1 : ℝ) ≤ (q - r).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [hC]; nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge (C ^ 3)
  refine ⟨ε, hεpos, hε1', max (2 * (q + r)) n₁, fun n hn J hJK hdeg => ?_⟩
  have hn2 : 2 * (q + r) ≤ n := le_of_max_le_left hn
  have hnC : C ^ 3 ≤ n := hn₁.trans (by exact_mod_cast le_of_max_le_right hn)
  obtain ⟨H, hH, hHe⟩ := hb n hn2 J hJK hdeg
  refine ⟨H, hH, fun e he => (hHe e he).trans ?_⟩
  -- `binom(q, r) ≤ n^{-1/3} binom(n-r, q-r)` for large `n`
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM := choose_sub_ge (n := n) (r := r) (k := q - r) (by omega)
  have hn2' : (1 : ℝ) ≤ n / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (show 2 ≤ n by omega)
  have hM2 : (n : ℝ) / 2 / (q - r).factorial ≤ ((n - r).choose (q - r) : ℝ) := by
    refine le_trans ?_ hM
    gcongr
    calc (n : ℝ) / 2 = (n / 2) ^ 1 := (pow_one _).symm
      _ ≤ (n / 2) ^ (q - r) := pow_le_pow_right₀ hn2' (by omega)
  set s : ℝ := (n : ℝ) ^ (1 / 3 : ℝ) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos hnpos _
  have hs3 : s ^ 3 = n := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hsC : C ≤ s := by
    by_contra hcon
    push_neg at hcon
    have : s ^ 3 < C ^ 3 := pow_lt_pow_left₀ hcon hspos.le (by norm_num)
    linarith
  have hneg : (n : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / s := by
    rw [Real.rpow_neg hnpos.le, hs]; exact inv_eq_one_div _
  rw [hneg]
  have hfq : (0 : ℝ) < (q - r).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hspos]
  have h3 : (q.choose r : ℝ) * s * (2 * (q - r).factorial) ≤ s ^ 3 := by
    have : (q.choose r : ℝ) * (2 * (q - r).factorial) = C := by rw [hC]; ring
    have hs1 : 1 ≤ s := hC1.trans hsC
    nlinarith [mul_le_mul hsC hsC (by linarith) hspos.le, pow_le_pow_right₀ hs1
      (show 2 ≤ 3 by norm_num)]
  rw [hs3] at h3
  calc (q.choose r : ℝ) * s = (q.choose r * s * (2 * (q - r).factorial)) /
        (2 * (q - r).factorial) := by field_simp
    _ ≤ n / (2 * (q - r).factorial) := by gcongr
    _ = (n : ℝ) / 2 / (q - r).factorial := by rw [div_div]
    _ ≤ _ := hM2

end RefinedAbsorption
