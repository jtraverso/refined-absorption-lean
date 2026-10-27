module
public import RequestProject.MathlibImports

/-!
# Colouring the new copies so that no piece contains two copies of the same colour

If every copy lies in at most `C` pieces and every piece has at most `C` copies, the copies of `R`
can be coloured with `C² + 1` colours so that the copies of `R` in a common piece have distinct
colours (greedy colouring).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset

/-- **Greedy colouring of the copies by the pieces.** -/
theorem exists_piece_coloring {E : Type*} [DecidableEq E] (R : Finset E) (𝒲 : Finset (Finset E))
    (C : ℕ) (hm : ∀ c ∈ R, (𝒲.filter fun W => c ∈ W).card ≤ C) (hc : ∀ W ∈ 𝒲, W.card ≤ C) :
    ∃ col : E → ℕ, (∀ c ∈ R, col c < C * C + 1) ∧
      ∀ W ∈ 𝒲, ∀ c ∈ W, ∀ c' ∈ W, c ∈ R → c' ∈ R → col c = col c' → c = c' := by
  classical
  suffices key : ∀ s ⊆ R, ∃ col : E → ℕ, (∀ c ∈ s, col c < C * C + 1) ∧
      ∀ W ∈ 𝒲, ∀ c ∈ W, ∀ c' ∈ W, c ∈ s → c' ∈ s → col c = col c' → c = c' from key R subset_rfl
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => 0, by simp, by simp⟩
  | insert a s has ih =>
    intro hsR
    obtain ⟨col, hcol, hprop⟩ := ih ((subset_insert a s).trans hsR)
    set conf := (𝒲.filter fun W => a ∈ W).biUnion id with hconf
    have hconfc : conf.card ≤ C * C := by
      refine card_biUnion_le.trans ?_
      refine (sum_le_sum fun W hW => hc W (mem_filter.1 hW).1).trans ?_
      rw [sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (hm a (hsR (mem_insert_self a s)))
    have hfree : ((range (C * C + 1)) \ ((conf.erase a).image col)).Nonempty := by
      rw [← card_pos]
      have h1 := le_card_sdiff ((conf.erase a).image col) (range (C * C + 1))
      have h2 : ((conf.erase a).image col).card ≤ C * C :=
        card_image_le.trans ((card_le_card (erase_subset a conf)).trans hconfc)
      rw [card_range] at h1
      omega
    obtain ⟨j, hj⟩ := hfree
    obtain ⟨hjr, hjc⟩ := mem_sdiff.1 hj
    refine ⟨Function.update col a j, ?_, ?_⟩
    · intro c hc'
      rcases mem_insert.1 hc' with rfl | hcs
      · rw [Function.update_self]; exact mem_range.1 hjr
      · have hca : c ≠ a := fun h => has (h ▸ hcs)
        rw [Function.update_of_ne hca]; exact hcol c hcs
    · intro W hW c hcW c' hc'W hcs0 hcs0' heq
      have hne : ∀ x ∈ s, x ≠ a := fun x hx h => has (h ▸ hx)
      rcases mem_insert.1 hcs0 with h1 | hcs <;> rcases mem_insert.1 hcs0' with h2 | hc's
      · rw [h1, h2]
      · exfalso
        subst h1
        rw [Function.update_self, Function.update_of_ne (hne c' hc's)] at heq
        apply hjc
        refine mem_image.2 ⟨c', mem_erase.2 ⟨hne c' hc's, ?_⟩, heq.symm⟩
        exact mem_biUnion.2 ⟨W, mem_filter.2 ⟨hW, hcW⟩, hc'W⟩
      · exfalso
        subst h2
        rw [Function.update_self, Function.update_of_ne (hne c hcs)] at heq
        apply hjc
        refine mem_image.2 ⟨c, mem_erase.2 ⟨hne c hcs, ?_⟩, heq⟩
        exact mem_biUnion.2 ⟨W, mem_filter.2 ⟨hW, hc'W⟩, hcW⟩
      · rw [Function.update_of_ne (hne c hcs), Function.update_of_ne (hne c' hc's)] at heq
        exact hprop W hW c hcW c' hc'W hcs hc's heq

end RefinedAbsorption.General
