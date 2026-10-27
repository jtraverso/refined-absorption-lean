module
public import RequestProject.Counting

/-!
# Partial Steiner systems and how many there are

A *partial Steiner system* with parameters `(q, r)` is a family of `q`-sets such that every
`r`-set lies in at most one of them.  This file defines them and proves a lower bound on the
number of partial Steiner systems with `k` blocks inside a fixed `u`-set `U`:
if `2 k B ≤ binom(u, q)` with `B = binom(q, r) binom(u - r, q - r)`, there are at least `B^k`
of them (`card_psFamily_ge`).  The proof is the greedy extension argument written as a double
count: a partial system with `k` blocks has at least `binom(u, q) - k B` extensions by one block.
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset

variable {V : Type*} [DecidableEq V]

/-- A **partial Steiner system** with parameters `(q, r)`: a family of `q`-sets such that every
`r`-set lies in at most one of them. -/
def IsPartialSteinerSystem (q r : ℕ) (P : Finset (Finset V)) : Prop :=
  (∀ Q ∈ P, Q.card = q) ∧ ∀ T : Finset V, T.card = r → cliqueMult P T ≤ 1

theorem isPartialSteinerSystem_empty (q r : ℕ) :
    IsPartialSteinerSystem q r (∅ : Finset (Finset V)) :=
  ⟨by simp, fun T _ => by simp [cliqueMult]⟩

open Classical in
/-- The partial Steiner systems with exactly `k` blocks, all inside `U`. -/
noncomputable def psFamily (q r k : ℕ) (U : Finset V) : Finset (Finset (Finset V)) :=
  ((U.powersetCard q).powersetCard k).filter (IsPartialSteinerSystem q r)

open Classical in
/-- The blocks `Q ⊆ U` that extend the partial system `P`. -/
noncomputable def goodExt (q r : ℕ) (U : Finset V) (P : Finset (Finset V)) : Finset (Finset V) :=
  (U.powersetCard q).filter (fun Q => Q ∉ P ∧ IsPartialSteinerSystem q r (insert Q P))

/-- The `q`-subsets of `U` containing a fixed `r`-subset `T ⊆ U`. -/
theorem card_blocks_through {q r : ℕ} (hrq : r ≤ q) {U T : Finset V} (hTU : T ⊆ U)
    (hT : T.card = r) :
    ((U.powersetCard q).filter (fun Q => T ⊆ Q)).card = (U.card - r).choose (q - r) := by
  rw [card_powersetCard_filter_superset hTU (by omega), hT]

/-- The blocks `Q ⊆ U` that do not extend `P` all share an `r`-set with a block of `P`. -/
theorem not_good_subset {q r : ℕ} (hrq : r ≤ q) {U : Finset V} {P : Finset (Finset V)}
    (hP : IsPartialSteinerSystem q r P) :
    (U.powersetCard q).filter (fun Q => Q ∉ goodExt q r U P) ⊆
      P.biUnion (fun Q₀ => (Q₀.powersetCard r).biUnion
        (fun T => (U.powersetCard q).filter (fun Q => T ⊆ Q))) := by
  classical
  intro Q hQ
  obtain ⟨hQU, hng⟩ := mem_filter.1 hQ
  have hQc : Q.card = q := (mem_powersetCard.1 hQU).2
  simp only [goodExt, mem_filter, hQU, true_and, not_and_or, not_not] at hng
  simp only [mem_biUnion, mem_filter, mem_powersetCard]
  rcases hng with hQP | hbad
  · obtain ⟨T, hTQ, hT⟩ := exists_subset_card_eq (show r ≤ Q.card by omega)
    exact ⟨Q, hQP, T, ⟨hTQ, hT⟩, (mem_powersetCard.1 hQU), hTQ⟩
  · by_cases hQP : Q ∈ P
    · obtain ⟨T, hTQ, hT⟩ := exists_subset_card_eq (show r ≤ Q.card by omega)
      exact ⟨Q, hQP, T, ⟨hTQ, hT⟩, (mem_powersetCard.1 hQU), hTQ⟩
    · simp only [IsPartialSteinerSystem, not_and_or, not_forall, not_le] at hbad
      rcases hbad with ⟨Q', hQ', hc⟩ | ⟨T, hT, hm⟩
      · exfalso
        rcases mem_insert.1 hQ' with rfl | hQ'
        · exact hc hQc
        · exact hc (hP.1 Q' hQ')
      · have hmult : cliqueMult (insert Q P) T =
            cliqueMult P T + if T ⊆ Q then 1 else 0 := by
          unfold cliqueMult
          rw [filter_insert]
          split_ifs with h
          · rw [card_insert_of_notMem (fun h' => hQP (mem_filter.1 h').1)]
          · rfl
        have h1 := hP.2 T hT
        rw [hmult] at hm
        split_ifs at hm with hTQ
        · have : 0 < cliqueMult P T := by omega
          obtain ⟨Q₀, hQ₀⟩ := card_pos.1 this
          obtain ⟨hQ₀P, hTQ₀⟩ := mem_filter.1 hQ₀
          exact ⟨Q₀, hQ₀P, T, ⟨hTQ₀, hT⟩, (mem_powersetCard.1 hQU), hTQ⟩
        · omega

/-- A partial system with `k` blocks inside `U` has at least `binom(u,q) - k B` extensions. -/
theorem card_goodExt_ge {q r : ℕ} (hrq : r ≤ q) {U : Finset V} {P : Finset (Finset V)}
    (hP : IsPartialSteinerSystem q r P) :
    (U.card.choose q) - P.card * (q.choose r * (U.card - r).choose (q - r)) ≤
      (goodExt q r U P).card := by
  classical
  have hsplit := card_filter_add_card_filter_not
    (s := U.powersetCard q) (fun Q => Q ∈ goodExt q r U P)
  have hgood : (U.powersetCard q).filter (fun Q => Q ∈ goodExt q r U P) = goodExt q r U P := by
    ext Q; simp only [mem_filter, and_iff_right_iff_imp]
    intro h; exact (mem_filter.1 h).1
  rw [hgood, card_powersetCard] at hsplit
  have hbad := card_le_card (not_good_subset (U := U) hrq hP)
  have hb2 : (P.biUnion (fun Q₀ => (Q₀.powersetCard r).biUnion
        (fun T => (U.powersetCard q).filter (fun Q => T ⊆ Q)))).card ≤
      P.card * (q.choose r * (U.card - r).choose (q - r)) := by
    refine (card_biUnion_le).trans ?_
    rw [← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun Q₀ hQ₀ => (card_biUnion_le).trans ?_
    rw [show q.choose r = (Q₀.powersetCard r).card by rw [card_powersetCard, hP.1 Q₀ hQ₀],
      ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun T hT => ?_
    by_cases hTU : T ⊆ U
    · rw [card_blocks_through hrq hTU (mem_powersetCard.1 hT).2]
    · rw [card_eq_zero.2]
      · exact Nat.zero_le _
      · exact filter_eq_empty_iff.2 fun Q hQ hTQ => hTU (hTQ.trans (mem_powersetCard.1 hQ).1)
  omega

/-- Adding a good block gives a partial system with one more block. -/
theorem insert_mem_psFamily {q r k : ℕ} {U : Finset V} {P : Finset (Finset V)}
    (hP : P ∈ psFamily q r k U) {Q : Finset V} (hQ : Q ∈ goodExt q r U P) :
    insert Q P ∈ psFamily q r (k + 1) U := by
  classical
  simp only [psFamily, goodExt, mem_filter, mem_powersetCard] at hP hQ ⊢
  refine ⟨⟨insert_subset (mem_powersetCard.2 hQ.1) hP.1.1, ?_⟩, hQ.2.2⟩
  rw [card_insert_of_notMem hQ.2.1, hP.1.2]

/-- **Double counting.**  `∑_{P} |good(P)| ≤ (k + 1) |PS_{k+1}|`. -/
theorem sum_goodExt_le {q r k : ℕ} (U : Finset V) :
    ∑ P ∈ psFamily q r k U, (goodExt q r U P).card ≤ (k + 1) * (psFamily q r (k + 1) U).card := by
  classical
  have h1 : ∑ P ∈ psFamily q r k U, (goodExt q r U P).card =
      ((psFamily q r k U).sigma (fun P => goodExt q r U P)).card := (card_sigma _ _).symm
  have h2 : (k + 1) * (psFamily q r (k + 1) U).card =
      ((psFamily q r (k + 1) U).sigma (fun P => P)).card := by
    rw [card_sigma, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun P hP => ?_
    simp only [psFamily, mem_filter, mem_powersetCard] at hP
    exact hP.1.2.symm
  rw [h1, h2]
  refine card_le_card_of_injOn (fun x => ⟨insert x.2 x.1, x.2⟩) ?_ ?_
  · intro x hx
    rw [mem_coe, mem_sigma] at hx ⊢
    exact ⟨insert_mem_psFamily hx.1 hx.2, mem_insert_self _ _⟩
  · intro x hx y hy hxy
    rw [mem_coe, mem_sigma] at hx hy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hx2 : x.2 ∉ x.1 := (mem_filter.1 hx.2).2.1
    have hy2 : y.2 ∉ y.1 := (mem_filter.1 hy.2).2.1
    have e1 : x.1 = y.1 := by
      have := congrArg (fun s => s.erase x.2) h1
      simp only at this
      rw [erase_insert hx2, h2, erase_insert hy2] at this
      exact this
    exact Sigma.ext e1 (heq_of_eq h2)

/-- The recursion `(k + 1) |PS_{k+1}| ≥ |PS_k| (binom(u,q) - k B)`. -/
theorem psFamily_recursion {q r : ℕ} (hrq : r ≤ q) (U : Finset V) (k : ℕ) :
    (psFamily q r k U).card * ((U.card.choose q) - k * (q.choose r * (U.card - r).choose (q - r)))
      ≤ (k + 1) * (psFamily q r (k + 1) U).card := by
  refine le_trans ?_ (sum_goodExt_le U)
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun P hP => ?_
  simp only [psFamily, mem_filter, mem_powersetCard] at hP
  have := card_goodExt_ge (U := U) hrq hP.2
  rwa [hP.1.2] at this

/-- `|PS_k| · k! ≥ ∏_{j<k} (binom(u,q) - j B)`. -/
theorem psFamily_prod {q r : ℕ} (hrq : r ≤ q) (U : Finset V) (k : ℕ) :
    ∏ j ∈ range k, ((U.card.choose q) - j * (q.choose r * (U.card - r).choose (q - r))) ≤
      (psFamily q r k U).card * k.factorial := by
  induction k with
  | zero =>
    simp only [range_zero, prod_empty, Nat.factorial_zero, mul_one]
    refine Nat.one_le_iff_ne_zero.2 (card_ne_zero.2 ⟨∅, ?_⟩)
    simp only [psFamily, mem_filter, mem_powersetCard, empty_subset, card_empty, true_and]
    exact isPartialSteinerSystem_empty q r
  | succ k ih =>
    rw [prod_range_succ, Nat.factorial_succ]
    have hrec := psFamily_recursion hrq U k
    calc _ ≤ (psFamily q r k U).card * k.factorial *
          ((U.card.choose q) - k * (q.choose r * (U.card - r).choose (q - r))) :=
          Nat.mul_le_mul_right _ ih
      _ = (psFamily q r k U).card *
          ((U.card.choose q) - k * (q.choose r * (U.card - r).choose (q - r))) * k.factorial := by
          ring
      _ ≤ (k + 1) * (psFamily q r (k + 1) U).card * k.factorial := Nat.mul_le_mul_right _ hrec
      _ = _ := by ring

/-- **Many partial Steiner systems.**  With `B = binom(q,r) binom(u - r, q - r)`, if
`2 k B ≤ binom(u, q)` there are at least `B^k` partial Steiner systems with `k` blocks inside
the `u`-set `U`. -/
theorem card_psFamily_ge {q r : ℕ} (hrq : r ≤ q) (U : Finset V) (k : ℕ)
    (hk : 2 * k * (q.choose r * (U.card - r).choose (q - r)) ≤ U.card.choose q) :
    (q.choose r * (U.card - r).choose (q - r)) ^ k ≤ (psFamily q r k U).card := by
  set B := q.choose r * (U.card - r).choose (q - r)
  set M := U.card.choose q
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [pow_zero]
    refine Nat.one_le_iff_ne_zero.2 (card_ne_zero.2 ⟨∅, ?_⟩)
    simp only [psFamily, mem_filter, mem_powersetCard, empty_subset, card_empty, true_and]
    exact isPartialSteinerSystem_empty q r
  have hprod := psFamily_prod hrq U k
  have hfac : (k * B) ^ k ≤ ∏ j ∈ range k, (M - j * B) := by
    rw [show (k * B) ^ k = ∏ _j ∈ range k, k * B by rw [prod_const, card_range]]
    refine prod_le_prod' fun j hj => ?_
    have : j * B ≤ k * B := Nat.mul_le_mul_right _ (mem_range.1 hj).le
    rw [mem_range] at hj
    have h2 : 2 * (k * B) ≤ M := by linarith
    omega
  have hkk : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
  have : k ^ k * B ^ k ≤ k ^ k * (psFamily q r k U).card := by
    rw [← mul_pow]
    calc (k * B) ^ k ≤ (psFamily q r k U).card * k.factorial := hfac.trans hprod
      _ ≤ (psFamily q r k U).card * k ^ k := Nat.mul_le_mul_left _ hkk
      _ = _ := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left this (by positivity)

end RefinedAbsorption.Extensions
