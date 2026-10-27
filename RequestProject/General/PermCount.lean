module
public import Mathlib

/-!
# Uniformly random permutations of a set of new vertices

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1 (every local refiner
is moved by an independent uniformly random permutation of the new vertices).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`PermOn P` is the group of permutations of `Fin n` fixing every vertex outside `P`; it has
`|P|!` elements (`card_permOn`).  The key count (`card_perm_cover_le`): for `S ⊆ P` with `|S| = t`
and any set `A`, at most `|A|^t (|P| - t)!` of these permutations map `A` onto a superset of `S`;
in other words the probability that a random permutation covers `S` by the image of `A` is at most
`|A|^t / (|P| - t + 1)^t` (`card_perm_cover_mul_le`).
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset

variable {n : ℕ}

/-- The permutations of `Fin n` fixing every vertex outside `P`. -/
abbrev PermOn (P : Finset (Fin n)) := {σ : Equiv.Perm (Fin n) // ∀ x, x ∉ P → σ x = x}

theorem card_permOn (P : Finset (Fin n)) : Fintype.card (PermOn P) = P.card.factorial := by
  classical
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin n => x ∈ P)
  rw [← Fintype.card_congr e, Fintype.card_perm, Fintype.card_coe]

theorem permOn_mem {P : Finset (Fin n)} (σ : PermOn P) {x : Fin n} (hx : x ∈ P) : σ.1 x ∈ P := by
  by_contra h
  have h1 := σ.2 _ h
  exact h (by rwa [σ.1.injective h1])

theorem permOn_not_mem {P : Finset (Fin n)} (σ : PermOn P) {x : Fin n} (hx : x ∉ P) :
    σ.1 x ∉ P := by rw [σ.2 x hx]; exact hx

/-- **The covering count.** -/
theorem card_perm_cover_le (P S A : Finset (Fin n)) (hSP : S ⊆ P) :
    (univ.filter fun σ : PermOn P => S ⊆ A.image σ.1).card ≤
      A.card ^ S.card * (P.card - S.card).factorial := by
  classical
  set Fl := univ.filter fun σ : PermOn P => S ⊆ A.image σ.1 with hFl
  set f : PermOn P → (S → Fin n) := fun σ y => σ.1.symm y.1 with hf
  have himg : Fl.image f ⊆ Fintype.piFinset fun _ : S => A := by
    intro b hb
    obtain ⟨σ, hσ, rfl⟩ := mem_image.1 hb
    rw [Fintype.mem_piFinset]
    intro y
    obtain ⟨a, ha, hay⟩ := mem_image.1 ((mem_filter.1 hσ).2 y.2)
    show σ.1.symm y.1 ∈ A
    rw [← hay, Equiv.symm_apply_apply]; exact ha
  have hcardpi : (Fintype.piFinset fun _ : S => A).card = A.card ^ S.card := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_coe]
  -- the fibres
  have hfib : ∀ b ∈ Fl.image f, (Fl.filter fun σ => f σ = b).card ≤
      (P.card - S.card).factorial := by
    intro b hb
    obtain ⟨σ₀, hσ₀, rfl⟩ := mem_image.1 hb
    have hQ : (P \ S).card = P.card - S.card := card_sdiff_of_subset hSP
    rw [← hQ, ← card_permOn (P \ S), Fintype.card_subtype]
    refine card_le_card_of_injOn (fun σ => σ₀.1 * σ.1⁻¹) ?_ ?_
    · intro σ hσ
      obtain ⟨-, hσf⟩ := mem_filter.1 hσ
      refine mem_filter.2 ⟨mem_univ _, fun x hx => ?_⟩
      rw [mem_sdiff, not_and_or, not_not] at hx
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rcases hx with hxP | hxS
      · have h1 : σ.1⁻¹ x = x := by
          rw [Equiv.Perm.inv_eq_iff_eq]; exact (σ.2 x hxP).symm
        rw [h1]; exact σ₀.2 x hxP
      · have h1 := congrFun hσf ⟨x, hxS⟩
        simp only [hf] at h1
        have h2 : σ.1⁻¹ x = σ₀.1⁻¹ x := h1
        rw [h2]; exact σ₀.1.apply_symm_apply x
    · intro σ₁ _ σ₂ _ heq
      have : σ₁.1⁻¹ = σ₂.1⁻¹ := mul_left_cancel heq
      exact Subtype.ext (inv_injective this)
  calc Fl.card ≤ (P.card - S.card).factorial * (Fl.image f).card :=
        card_le_mul_card_image Fl _ hfib
    _ ≤ (P.card - S.card).factorial * (A.card ^ S.card) :=
        Nat.mul_le_mul_left _ ((card_le_card himg).trans hcardpi.le)
    _ = A.card ^ S.card * (P.card - S.card).factorial := mul_comm _ _

/-- **The covering probability.** -/
theorem card_perm_cover_mul_le (P S A : Finset (Fin n)) (hSP : S ⊆ P) :
    (univ.filter fun σ : PermOn P => S ⊆ A.image σ.1).card * (P.card - S.card + 1) ^ S.card ≤
      A.card ^ S.card * Fintype.card (PermOn P) := by
  rw [card_permOn]
  have h1 := card_perm_cover_le P S A hSP
  have h2 : (P.card - S.card).factorial * (P.card - S.card + 1) ^ S.card ≤ P.card.factorial := by
    have := Nat.factorial_mul_pow_le_factorial (m := P.card - S.card) (n := S.card)
    rwa [Nat.sub_add_cancel (card_le_card hSP)] at this
  calc (univ.filter fun σ : PermOn P => S ⊆ A.image σ.1).card * (P.card - S.card + 1) ^ S.card
      ≤ A.card ^ S.card * (P.card - S.card).factorial * (P.card - S.card + 1) ^ S.card :=
        Nat.mul_le_mul_right _ h1
    _ = A.card ^ S.card * ((P.card - S.card).factorial * (P.card - S.card + 1) ^ S.card) := by ring
    _ ≤ A.card ^ S.card * P.card.factorial := Nat.mul_le_mul_left _ h2

end RefinedAbsorption.General
