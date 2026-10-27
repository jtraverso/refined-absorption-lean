module
public import RequestProject.Basic

/-!
# Dangerous cliques with respect to a given packing

For a family `Pk` of `q`-sets in which every `r`-set lies in at most one member (a `K_q^r`-packing),
a `q`-set `Q` is *dangerous* if it meets some member of `Pk` in at least `r + 1` vertices.

`cliqueMult_dangerFam_le`: every `r`-set lies in at most `2^r q n^(q-r-1)` dangerous `q`-sets.
This is the counting step of the proof of Theorem 6.3 (the printed text of arXiv:2402.17855v1
states `O(n^(q-r+1))`, which would not be negligible against `n^(q-r)`; the bound proved here is
`O(n^(q-r-1))`).
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset

variable {n : ℕ}

/-- The dangerous `q`-sets with respect to `Pk`: those meeting a member of `Pk` in at least
`r + 1` vertices. -/
def dangerFam (q r : ℕ) (Pk : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (univ.powersetCard q).filter fun Q => ∃ P ∈ Pk, r + 1 ≤ (Q ∩ P).card

theorem mem_dangerFam {q r : ℕ} {Pk : Finset (Finset (Fin n))} {Q : Finset (Fin n)} :
    Q ∈ dangerFam q r Pk ↔ Q.card = q ∧ ∃ P ∈ Pk, r + 1 ≤ (Q ∩ P).card := by
  simp [dangerFam, mem_powersetCard]

/-- A `q`-set which is not dangerous meets every member of `Pk` in at most `r` vertices. -/
theorem inter_le_of_not_mem_dangerFam {q r : ℕ} {Pk : Finset (Finset (Fin n))}
    {Q : Finset (Fin n)} (hQ : Q.card = q) (hd : Q ∉ dangerFam q r Pk) :
    ∀ P ∈ Pk, (Q ∩ P).card ≤ r := by
  intro P hP
  by_contra h
  exact hd (mem_dangerFam.2 ⟨hQ, P, hP, by omega⟩)

/-- The number of `q`-sets containing a fixed set `Z`. -/
theorem card_supsets_le (q : ℕ) (Z : Finset (Fin n)) :
    ((univ.powersetCard q).filter fun Q => Z ⊆ Q).card ≤ n ^ (q - Z.card) := by
  have hinj : Set.InjOn (fun Q : Finset (Fin n) => Q \ Z)
      ↑((univ.powersetCard q).filter fun Q => Z ⊆ Q) := by
    intro Q₁ h₁ Q₂ h₂ heq
    have h₁' := (mem_filter.1 (mem_coe.1 h₁)).2
    have h₂' := (mem_filter.1 (mem_coe.1 h₂)).2
    simp only at heq
    rw [← sdiff_union_of_subset h₁', ← sdiff_union_of_subset h₂', heq]
  refine (card_le_card_of_injOn (t := univ.powersetCard (q - Z.card)) _ (fun Q hQ => ?_)
    hinj).trans ?_
  · simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hQ
    simp only [mem_coe, mem_powersetCard, subset_univ, true_and]
    rw [card_sdiff_of_subset hQ.2, hQ.1.2]
  · rw [card_powersetCard, card_univ, Fintype.card_fin]
    exact Nat.choose_le_pow n _

/-- No `q`-set contains a set with more than `q` elements. -/
theorem supsets_eq_empty {q : ℕ} {Z : Finset (Fin n)} (hZ : q < Z.card) :
    ((univ.powersetCard q).filter fun Q => Z ⊆ Q) = ∅ := by
  rw [filter_eq_empty_iff]
  intro Q hQ hZQ
  have := card_le_card hZQ
  rw [(mem_powersetCard.1 hQ).2] at this
  omega

/-- The covering of the dangerous `q`-sets through `e`. -/
theorem dangerFam_filter_subset {q r : ℕ} {Pk : Finset (Finset (Fin n))} {e : Finset (Fin n)}
    (he : e.card = r) :
    (dangerFam q r Pk).filter (fun Q => e ⊆ Q) ⊆
      e.powerset.biUnion fun A => ((univ \ e).powersetCard (r - A.card)).biUnion fun B =>
        (Pk.filter fun P => A ∪ B ⊆ P).biUnion fun P => (P \ (e ∪ B)).biUnion fun y =>
          (univ.powersetCard q).filter fun Q => insert y (e ∪ B) ⊆ Q := by
  intro Q hQ
  obtain ⟨hQd, heQ⟩ := mem_filter.1 hQ
  obtain ⟨hQc, P, hP, hQP⟩ := mem_dangerFam.1 hQd
  set A := P ∩ e with hA
  have hAe : A ⊆ e := inter_subset_right
  have hAc : A.card ≤ r := he ▸ card_le_card hAe
  -- the part of `Q ∩ P` outside `e`
  set O := (Q ∩ P) \ e with hO
  have hQPA : Q ∩ P = O ∪ A := by
    ext x
    simp only [hO, hA, mem_union, mem_sdiff, mem_inter]
    constructor
    · rintro ⟨hxQ, hxP⟩
      by_cases hxe : x ∈ e
      · exact Or.inr ⟨hxP, hxe⟩
      · exact Or.inl ⟨⟨hxQ, hxP⟩, hxe⟩
    · rintro (⟨⟨hxQ, hxP⟩, -⟩ | ⟨hxP, hxe⟩)
      · exact ⟨hxQ, hxP⟩
      · exact ⟨heQ hxe, hxP⟩
  have hOc : r + 1 - A.card ≤ O.card := by
    have : (Q ∩ P).card ≤ O.card + A.card := by rw [hQPA]; exact card_union_le _ _
    omega
  obtain ⟨B, hBO, hBc⟩ := exists_subset_card_eq (show r - A.card ≤ O.card by omega)
  obtain ⟨y, hyO, hyB⟩ : ∃ y ∈ O, y ∉ B := by
    by_contra hno
    push_neg at hno
    have : O ⊆ B := fun y hy => hno y hy
    have := card_le_card this
    omega
  have hyQ : y ∈ Q := (mem_inter.1 (mem_sdiff.1 hyO).1).1
  have hyP : y ∈ P := (mem_inter.1 (mem_sdiff.1 hyO).1).2
  have hye : y ∉ e := (mem_sdiff.1 hyO).2
  have hBQ : B ⊆ Q := fun x hx => (mem_inter.1 (mem_sdiff.1 (hBO hx)).1).1
  have hBP : B ⊆ P := fun x hx => (mem_inter.1 (mem_sdiff.1 (hBO hx)).1).2
  have hBe : B ⊆ univ \ e := fun x hx => mem_sdiff.2 ⟨mem_univ _, (mem_sdiff.1 (hBO hx)).2⟩
  refine mem_biUnion.2 ⟨A, mem_powerset.2 hAe, mem_biUnion.2 ⟨B, mem_powersetCard.2 ⟨hBe, hBc⟩,
    mem_biUnion.2 ⟨P, mem_filter.2 ⟨hP, union_subset inter_subset_left hBP⟩,
      mem_biUnion.2 ⟨y, mem_sdiff.2 ⟨hyP, ?_⟩, mem_filter.2 ⟨mem_powersetCard.2
        ⟨subset_univ _, hQc⟩, insert_subset hyQ (union_subset heQ hBQ)⟩⟩⟩⟩⟩
  rw [mem_union, not_or]
  exact ⟨hye, hyB⟩

/-- **Counting dangerous cliques.**  If every `r`-set lies in at most one member of `Pk` and the
members of `Pk` have `q` elements, then every `r`-set lies in at most `2^r q n^(q-r-1)` dangerous
`q`-sets. -/
theorem cliqueMult_dangerFam_le {q r : ℕ} (hrq : r < q) {Pk : Finset (Finset (Fin n))}
    (hcard : ∀ P ∈ Pk, P.card = q) (hmult : ∀ f : Finset (Fin n), f.card = r → cliqueMult Pk f ≤ 1)
    {e : Finset (Fin n)} (he : e.card = r) :
    cliqueMult (dangerFam q r Pk) e ≤ 2 ^ r * q * n ^ (q - r - 1) := by
  unfold cliqueMult
  refine (card_le_card (dangerFam_filter_subset he)).trans (card_biUnion_le.trans ?_)
  have key : ∀ A ∈ e.powerset, (((univ \ e).powersetCard (r - A.card)).biUnion fun B =>
        (Pk.filter fun P => A ∪ B ⊆ P).biUnion fun P => (P \ (e ∪ B)).biUnion fun y =>
          (univ.powersetCard q).filter fun Q => insert y (e ∪ B) ⊆ Q).card ≤
        q * n ^ (q - r - 1) := by
    intro A hA
    have hAe := mem_powerset.1 hA
    have hAc : A.card ≤ r := he ▸ card_le_card hAe
    refine card_biUnion_le.trans ?_
    -- the size of the forced set
    have hZ : ∀ B ∈ (univ \ e).powersetCard (r - A.card), ∀ y, y ∉ e ∪ B →
        (insert y (e ∪ B)).card = 2 * r + 1 - A.card := by
      intro B hB y hy
      obtain ⟨hBe, hBc⟩ := mem_powersetCard.1 hB
      have hdisj : Disjoint e B := by
        rw [disjoint_left]; intro x hxe hxB; exact (mem_sdiff.1 (hBe hxB)).2 hxe
      rw [card_insert_of_notMem hy, card_union_of_disjoint hdisj, he, hBc]
      omega
    by_cases hbig : q < 2 * r + 1 - A.card
    · -- nothing to count
      have : ∀ B ∈ (univ \ e).powersetCard (r - A.card),
          ((Pk.filter fun P => A ∪ B ⊆ P).biUnion fun P => (P \ (e ∪ B)).biUnion fun y =>
            (univ.powersetCard q).filter fun Q => insert y (e ∪ B) ⊆ Q).card = 0 := by
        intro B hB
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro Q hQ
        obtain ⟨P, -, hQ⟩ := mem_biUnion.1 hQ
        obtain ⟨y, hy, hQ⟩ := mem_biUnion.1 hQ
        rw [supsets_eq_empty (by rw [hZ B hB y (mem_sdiff.1 hy).2]; exact hbig)] at hQ
        simp at hQ
      rw [sum_congr rfl this, sum_const_zero]
      exact Nat.zero_le _
    · push_neg at hbig
      have hexp : r - A.card + (q - (2 * r + 1 - A.card)) = q - r - 1 := by omega
      have hB : ∀ B ∈ (univ \ e).powersetCard (r - A.card),
          ((Pk.filter fun P => A ∪ B ⊆ P).biUnion fun P => (P \ (e ∪ B)).biUnion fun y =>
            (univ.powersetCard q).filter fun Q => insert y (e ∪ B) ⊆ Q).card ≤
            q * n ^ (q - (2 * r + 1 - A.card)) := by
        intro B hB
        obtain ⟨hBe, hBc⟩ := mem_powersetCard.1 hB
        have hdisj : Disjoint A B := by
          rw [disjoint_left]; intro x hxA hxB; exact (mem_sdiff.1 (hBe hxB)).2 (hAe hxA)
        have hABc : (A ∪ B).card = r := by
          rw [card_union_of_disjoint hdisj, hBc]; omega
        have hP1 : (Pk.filter fun P => A ∪ B ⊆ P).card ≤ 1 := hmult _ hABc
        refine card_biUnion_le.trans ?_
        calc ∑ P ∈ Pk.filter (fun P => A ∪ B ⊆ P), ((P \ (e ∪ B)).biUnion fun y =>
              (univ.powersetCard q).filter fun Q => insert y (e ∪ B) ⊆ Q).card
            ≤ ∑ _P ∈ Pk.filter (fun P => A ∪ B ⊆ P), q * n ^ (q - (2 * r + 1 - A.card)) := by
              refine sum_le_sum fun P hP => card_biUnion_le.trans ?_
              calc ∑ y ∈ P \ (e ∪ B), ((univ.powersetCard q).filter
                    fun Q => insert y (e ∪ B) ⊆ Q).card
                  ≤ ∑ _y ∈ P \ (e ∪ B), n ^ (q - (2 * r + 1 - A.card)) := by
                    refine sum_le_sum fun y hy => ?_
                    have := card_supsets_le (n := n) q (insert y (e ∪ B))
                    rwa [hZ B hB y (mem_sdiff.1 hy).2] at this
                _ = (P \ (e ∪ B)).card * n ^ (q - (2 * r + 1 - A.card)) := by
                    rw [sum_const, smul_eq_mul]
                _ ≤ q * n ^ (q - (2 * r + 1 - A.card)) := by
                    apply Nat.mul_le_mul_right
                    rw [← hcard P (mem_filter.1 hP).1]
                    exact card_le_card sdiff_subset
          _ = (Pk.filter fun P => A ∪ B ⊆ P).card * (q * n ^ (q - (2 * r + 1 - A.card))) := by
              rw [sum_const, smul_eq_mul]
          _ ≤ 1 * (q * n ^ (q - (2 * r + 1 - A.card))) := Nat.mul_le_mul_right _ hP1
          _ = q * n ^ (q - (2 * r + 1 - A.card)) := one_mul _
      calc ∑ B ∈ (univ \ e).powersetCard (r - A.card),
            ((Pk.filter fun P => A ∪ B ⊆ P).biUnion fun P => (P \ (e ∪ B)).biUnion fun y =>
              (univ.powersetCard q).filter fun Q => insert y (e ∪ B) ⊆ Q).card
          ≤ ∑ _B ∈ (univ \ e).powersetCard (r - A.card), q * n ^ (q - (2 * r + 1 - A.card)) :=
            sum_le_sum hB
        _ = ((univ \ e).powersetCard (r - A.card)).card * (q * n ^ (q - (2 * r + 1 - A.card))) := by
            rw [sum_const, smul_eq_mul]
        _ ≤ n ^ (r - A.card) * (q * n ^ (q - (2 * r + 1 - A.card))) := by
            apply Nat.mul_le_mul_right
            rw [card_powersetCard]
            refine (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left ?_ _)
            exact (card_le_univ _).trans (by simp)
        _ = q * n ^ (q - r - 1) := by
            rw [← hexp, pow_add]; ring
  calc ∑ A ∈ e.powerset, _ ≤ ∑ _A ∈ e.powerset, q * n ^ (q - r - 1) := sum_le_sum key
    _ = 2 ^ r * q * n ^ (q - r - 1) := by
        rw [sum_const, card_powerset, he, smul_eq_mul, mul_assoc]

end RefinedAbsorption.Pending
