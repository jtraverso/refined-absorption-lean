module
public import RefinedAbsorption.MathlibImports

/-!
# A greedy balanced colouring

Every element `e` of a finite set `E` touches at most two *rows* and forbids at most two colours.
If every row is touched at most `Δ` times and `2 + 2 ⌊Δ / L⌋ < C`, the elements can be coloured with
colours `< C`, avoiding the forbidden ones, so that every row sees every colour at most `L` times.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset

theorem greedy_color {α : Type*} [DecidableEq α] (rows forb : α → Finset ℕ) {C L Δ : ℕ}
    (hL : 0 < L) (hC : 2 + 2 * (Δ / L) < C) (E : Finset α)
    (hrows : ∀ e ∈ E, (rows e).card ≤ 2) (hforb : ∀ e ∈ E, (forb e).card ≤ 2)
    (hΔ : ∀ ρ, (E.filter (fun e => ρ ∈ rows e)).card ≤ Δ) :
    ∃ col : α → ℕ, (∀ e ∈ E, col e < C ∧ col e ∉ forb e) ∧
      ∀ ρ x, (E.filter (fun e => ρ ∈ rows e ∧ col e = x)).card ≤ L := by
  induction E using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | @insert e E' he ih =>
    obtain ⟨col', hc', hl'⟩ := ih (fun e he => hrows e (mem_insert_of_mem he))
      (fun e he => hforb e (mem_insert_of_mem he)) (fun ρ =>
      (card_le_card (filter_subset_filter _ (subset_insert _ _))).trans (hΔ ρ))
    set full : ℕ → Finset ℕ := fun ρ =>
      (range C).filter (fun x => L ≤ (E'.filter (fun e => ρ ∈ rows e ∧ col' e = x)).card)
    have hfull : ∀ ρ, (full ρ).card ≤ Δ / L := by
      intro ρ
      rw [Nat.le_div_iff_mul_le hL]
      have hdisj : (↑(full ρ) : Set ℕ).PairwiseDisjoint
          (fun x => E'.filter (fun e => ρ ∈ rows e ∧ col' e = x)) := by
        intro x _ y _ hxy
        simp only [Function.onFun]
        rw [disjoint_filter]
        rintro a - ⟨-, rfl⟩ ⟨-, h⟩
        exact hxy h
      calc (full ρ).card * L = ∑ x ∈ full ρ, L := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ full ρ, (E'.filter (fun e => ρ ∈ rows e ∧ col' e = x)).card :=
            sum_le_sum fun x hx => (mem_filter.1 hx).2
        _ = ((full ρ).biUnion (fun x => E'.filter (fun e => ρ ∈ rows e ∧ col' e = x))).card :=
            (card_biUnion hdisj).symm
        _ ≤ (E'.filter (fun e => ρ ∈ rows e)).card := by
            apply card_le_card
            intro a ha
            obtain ⟨x, -, ha⟩ := mem_biUnion.1 ha
            obtain ⟨ha, hρ, -⟩ := mem_filter.1 ha
            exact mem_filter.2 ⟨ha, hρ⟩
        _ ≤ (( insert e E').filter (fun e => ρ ∈ rows e)).card :=
            card_le_card (filter_subset_filter _ (subset_insert _ _))
        _ ≤ Δ := hΔ ρ
    set B := forb e ∪ (rows e).biUnion full
    have hB : B.card < (range C).card := by
      rw [card_range]
      calc B.card ≤ (forb e).card + ((rows e).biUnion full).card := card_union_le _ _
        _ ≤ 2 + ∑ ρ ∈ rows e, (full ρ).card := add_le_add (hforb e (mem_insert_self _ _)) card_biUnion_le
        _ ≤ 2 + ∑ ρ ∈ rows e, Δ / L := by gcongr with ρ; exact hfull ρ
        _ = 2 + (rows e).card * (Δ / L) := by rw [sum_const, smul_eq_mul]
        _ ≤ 2 + 2 * (Δ / L) := by gcongr; exact hrows e (mem_insert_self _ _)
        _ < C := hC
    obtain ⟨x, hx, hxB⟩ := exists_mem_notMem_of_card_lt_card hB
    refine ⟨Function.update col' e x, ?_, ?_⟩
    · intro e'' he''
      rcases mem_insert.1 he'' with rfl | he''
      · simp only [Function.update_self]
        exact ⟨mem_range.1 hx, fun h => hxB (mem_union_left _ h)⟩
      · have hne : e'' ≠ e := fun h => he (h ▸ he'')
        rw [Function.update_of_ne hne]
        exact hc' e'' he''
    · intro ρ x'
      have heq : E'.filter (fun a => ρ ∈ rows a ∧ Function.update col' e x a = x') =
          E'.filter (fun a => ρ ∈ rows a ∧ col' a = x') := by
        apply filter_congr
        intro a ha
        have hne : a ≠ e := fun h => he (h ▸ ha)
        rw [Function.update_of_ne hne]
      rw [filter_insert]
      split_ifs with hp
      · simp only [Function.update_self] at hp
        obtain ⟨hρ, rfl⟩ := hp
        rw [heq]
        have hlt : (E'.filter (fun a => ρ ∈ rows a ∧ col' a = x)).card < L := by
          by_contra hcon
          apply hxB
          refine mem_union_right _ (mem_biUnion.2 ⟨ρ, hρ, mem_filter.2 ⟨hx, ?_⟩⟩)
          omega
        calc _ ≤ (E'.filter (fun a => ρ ∈ rows a ∧ col' a = x)).card + 1 := card_insert_le _ _
          _ ≤ L := hlt
      · rw [heq]; exact hl' ρ x'

end RefinedAbsorption.OddGrid
