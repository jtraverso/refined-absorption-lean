module
public import RefinedAbsorption.MathlibImports

/-!
# Greedy balancing of choices

Mathematics: the standard deterministic averaging argument used for spreading (as in the proof of
the Partial Clique Embedding Lemma of M. Delcourt and L. Postle, arXiv:2402.17855).  Lean
formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Every item `t ∈ I` chooses a value `σ t` in a finite set `Z`, and touches a finite set `K t` of
*keys*.  The load of the key `k` at the value `v` is the number of items touching `k` that chose
`v`.  If every item touches at most `N` keys, every key is touched by at most `τ` items, and
`N · τ < |Z| · cap`, then the choices can be made so that every load is at most `cap`
(`greedy_balance`): items are processed one at a time, and a value is *bad* for a key if its load
already reached `cap`; there are fewer than `|Z| / N` bad values per key.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

/-- **Greedy balancing.** -/
theorem greedy_balance {ι κ V : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq V]
    (I : Finset ι) (Z : Finset V) (K : ι → Finset κ) (N τ cap : ℕ)
    (hK : ∀ t ∈ I, (K t).card ≤ N) (htot : ∀ k, (I.filter fun t => k ∈ K t).card ≤ τ)
    (hcap : N * τ < Z.card * cap) :
    ∃ σ : ι → V, (∀ t ∈ I, σ t ∈ Z) ∧
      ∀ k v, (I.filter fun t => k ∈ K t ∧ σ t = v).card ≤ cap := by
  have hZ : 0 < Z.card := by
    rcases Nat.eq_zero_or_pos Z.card with h | h
    · rw [h] at hcap; simp at hcap
    · exact h
  have hc : 0 < cap := by
    rcases Nat.eq_zero_or_pos cap with h | h
    · rw [h] at hcap; simp at hcap
    · exact h
  obtain ⟨v₀, hv₀⟩ := card_pos.1 hZ
  have key : ∀ s ⊆ I, ∃ σ : ι → V, (∀ t ∈ s, σ t ∈ Z) ∧
      ∀ k v, (s.filter fun t => k ∈ K t ∧ σ t = v).card ≤ cap := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨fun _ => v₀, by simp, by simp⟩
    | insert t s hts ih =>
      intro hsI
      obtain ⟨σ, hσZ, hσ⟩ := ih ((subset_insert t s).trans hsI)
      have htI : t ∈ I := hsI (mem_insert_self t s)
      set bad : κ → Finset V := fun k =>
        Z.filter fun v => cap ≤ (s.filter fun u => k ∈ K u ∧ σ u = v).card with hbad
      have hbadk : ∀ k, N * (bad k).card < Z.card := by
        intro k
        have h1 : (bad k).card * cap ≤ τ := by
          calc (bad k).card * cap = ∑ _v ∈ bad k, cap := by rw [sum_const, smul_eq_mul]
            _ ≤ ∑ v ∈ bad k, (s.filter fun u => k ∈ K u ∧ σ u = v).card :=
                sum_le_sum fun v hv => (mem_filter.1 hv).2
            _ = ∑ v ∈ bad k, ((s.filter fun u => k ∈ K u).filter fun u => σ u = v).card := by
                simp only [filter_filter]
            _ = ((s.filter fun u => k ∈ K u).filter fun u => σ u ∈ bad k).card :=
                sum_card_fiberwise_eq_card_filter _ _ _
            _ ≤ (s.filter fun u => k ∈ K u).card := card_filter_le _ _
            _ ≤ (I.filter fun u => k ∈ K u).card :=
                card_le_card (filter_subset_filter _ ((subset_insert t s).trans hsI))
            _ ≤ τ := htot k
        have h2 : N * (bad k).card * cap < Z.card * cap := by
          calc N * (bad k).card * cap = N * ((bad k).card * cap) := by ring
            _ ≤ N * τ := Nat.mul_le_mul_left _ h1
            _ < _ := hcap
        exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
      have hsum : ((K t).biUnion bad).card < Z.card := by
        refine lt_of_le_of_lt card_biUnion_le ?_
        rcases Nat.eq_zero_or_pos N with hN | hN
        · have : K t = ∅ := card_eq_zero.1 (by have := hK t htI; omega)
          rw [this, sum_empty]; exact hZ
        · have : N * ∑ k ∈ K t, (bad k).card ≤ N * (Z.card - 1) := by
            rw [mul_sum]
            calc ∑ k ∈ K t, N * (bad k).card ≤ ∑ _k ∈ K t, (Z.card - 1) :=
                  sum_le_sum fun k _ => by have := hbadk k; omega
              _ = (K t).card * (Z.card - 1) := by rw [sum_const, smul_eq_mul]
              _ ≤ N * (Z.card - 1) := Nat.mul_le_mul_right _ (hK t htI)
          have := Nat.le_of_mul_le_mul_left this hN
          omega
      obtain ⟨v, hvZ, hvbad⟩ := exists_mem_notMem_of_card_lt_card hsum
      refine ⟨Function.update σ t v, ?_, ?_⟩
      · intro u hu
        rcases mem_insert.1 hu with rfl | hu'
        · simpa using hvZ
        · rw [Function.update_of_ne (by rintro rfl; exact hts hu')]; exact hσZ u hu'
      · intro k w
        have hfs : (s.filter fun u => k ∈ K u ∧ Function.update σ t v u = w) =
            s.filter fun u => k ∈ K u ∧ σ u = w :=
          filter_congr fun u hu => by
            rw [Function.update_of_ne (by rintro rfl; exact hts hu)]
        rw [filter_insert, Function.update_self]
        split_ifs with h
        · obtain ⟨hk, rfl⟩ := h
          rw [card_insert_of_notMem (by simp [hts]), hfs]
          have : ¬ cap ≤ (s.filter fun u => k ∈ K u ∧ σ u = v).card := by
            intro hle
            exact hvbad (mem_biUnion.2 ⟨k, hk, mem_filter.2 ⟨hvZ, hle⟩⟩)
          omega
        · rw [hfs]; exact hσ k w
  obtain ⟨σ, h1, h2⟩ := key I subset_rfl
  exact ⟨σ, h1, h2⟩

end RefinedAbsorption.Placement
