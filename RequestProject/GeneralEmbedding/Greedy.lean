module
public import RequestProject.GeneralEmbedding.Good

/-!
# The greedy embedding

Embedding the supergraphs `W_H` one at a time, always choosing a good embedding
(`exists_good_embedding`), keeps the accidental degrees below the thresholds.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {n r C : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ends : ι → Finset (Fin n)} {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
  {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}

omit [Fintype ι] [DecidableEq ι] in
theorem newPairs_empty : newPairs W (∅ : Finset (Finset ι)) = ∅ := by
  simp [newPairs]

open Classical in
theorem greedy_embedding {G : Finset (Finset (Fin n))} {Q D C' γ : ℝ} (hγ : 0 < γ)
    (hQ : 2 ≤ Q) (hD1 : 1 ≤ D) (hn : 1 ≤ n) (hr : 1 ≤ r) (hC1 : 1 ≤ C)
    (hends : ∀ x, (ends x).card = r)
    (hdeg : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D)
    (href : IsCRefinedFamily C ℋ) (hsys : IsSupergraphSystem r ends ℋ m W)
    (hint : IsEdgeIntersecting ends ℋ m W)
    (hbd : ∀ H ∈ ℋ, (W H).card ≤ C)
    (hC'0 : 0 < C') (hDn : D ≤ n / C')
    (hC' : 4 * (C * ((C : ℝ) ^ 2 + Kseq Q ((C : ℝ) ^ 2) (r - 1)) * (r : ℝ) ^ r) ≤ γ * C')
    (hQγ : 4 * (C * 2 ^ (3 * r + 1) * (r : ℝ) ^ r) ≤ γ * Q)
    (hcount : ∀ H ∈ ℋ, γ * (n : ℝ) ^ (m H) ≤
      ((univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)).card : ℝ))
    (𝒮 : Finset (Finset ι)) (h𝒮 : 𝒮 ⊆ ℋ) :
    ∃ φ : (H : Finset ι) → Fin (m H) → Fin n,
      (∀ A : Finset (Fin n), A.card + 1 ≤ r →
        (accDeg W 𝒮 φ A : ℝ) ≤ thr Q ((C : ℝ) ^ 2) D n r A.card) ∧
      (∀ H ∈ 𝒮, IsHostEmbedding G ends H (W H) (φ H)) ∧
      (∀ H₁ ∈ 𝒮, ∀ H₂ ∈ 𝒮, H₁ ≠ H₂ → ∀ e₁ ∈ W H₁, ∀ e₂ ∈ W H₂,
        e₁.toRight.Nonempty → e₂.toRight.Nonempty →
          embedEdge (φ H₁) e₁ ≠ embedEdge (φ H₂) e₂) := by
  induction 𝒮 using Finset.induction_on with
  | empty =>
    refine ⟨fun _ _ => ⟨0, hn⟩, ?_, by simp, by simp⟩
    intro A _
    have h0 : accDeg W ∅ (fun _ _ => (⟨0, hn⟩ : Fin n)) A = 0 := by
      unfold accDeg; rw [newPairs_empty]; rfl
    rw [h0, Nat.cast_zero]
    unfold thr
    have := Kseq_nonneg (by linarith : (0 : ℝ) ≤ Q) (by positivity : (0 : ℝ) ≤ (C : ℝ) ^ 2)
      A.card
    have : (0 : ℝ) ≤ D := by linarith
    positivity
  | @insert H 𝒮 hH ih =>
    have h𝒮' : 𝒮 ⊆ ℋ := (subset_insert _ _).trans h𝒮
    have hHℋ : H ∈ ℋ := h𝒮 (mem_insert_self _ _)
    obtain ⟨φ, hacc, hemb, hdist⟩ := ih h𝒮'
    obtain ⟨f, hf, hfnew, hfacc⟩ := exists_good_embedding hγ hQ hD1 hn hr hC1 hends hdeg href
      hsys hint hbd h𝒮' hacc hC'0 hDn hC' hQγ hHℋ (hcount H hHℋ)
    refine ⟨Function.update φ H f, ?_, ?_, ?_⟩
    · intro A hA
      have h1 := accDeg_insert_le W hH φ f A
      rcases ((W H).filter (fun e => e.toRight.Nonempty ∧ A ⊆ embedEdge f e ∧
          ¬ A ⊆ e.toLeft)).eq_empty_or_nonempty with h | ⟨e, he⟩
      · rw [h, card_empty, add_zero] at h1
        exact (Nat.cast_le.2 h1).trans (hacc A hA)
      · obtain ⟨he1, hne, hAe, hAL⟩ := mem_filter.1 he
        have h2 := hfacc e he1 hne A hAe hA hAL
        have h3 : ((W H).filter (fun e => e.toRight.Nonempty ∧ A ⊆ embedEdge f e ∧
            ¬ A ⊆ e.toLeft)).card ≤ C := (card_filter_le _ _).trans (hbd H hHℋ)
        have h4 : (accDeg W (insert H 𝒮) (Function.update φ H f) A : ℝ) ≤
            accDeg W 𝒮 φ A + C := by
          have := Nat.cast_le (α := ℝ) |>.2 (h1.trans (Nat.add_le_add_left h3 _))
          push_cast at this
          exact this
        linarith
    · intro H' hH'
      rcases mem_insert.1 hH' with h | h
      · subst h; rw [Function.update_self]; exact hf
      · have hne : H' ≠ H := fun h' => hH (h' ▸ h)
        rw [Function.update_of_ne hne]; exact hemb H' h
    · intro H₁ hH₁ H₂ hH₂ h12 e₁ he₁ e₂ he₂ hn₁ hn₂
      rcases mem_insert.1 hH₁ with h1 | h1 <;> rcases mem_insert.1 hH₂ with h2 | h2
      · exact absurd (h1.trans h2.symm) h12
      · subst h1
        have hne : H₂ ≠ H₁ := fun h' => hH (h' ▸ h2)
        rw [Function.update_self, Function.update_of_ne hne]
        exact hfnew e₁ he₁ hn₁ ⟨H₂, e₂⟩
          (mem_filter.2 ⟨mem_sigma.2 ⟨h2, he₂⟩, hn₂⟩)
      · subst h2
        have hne : H₁ ≠ H₂ := fun h' => hH (h' ▸ h1)
        rw [Function.update_self, Function.update_of_ne hne]
        exact (hfnew e₂ he₂ hn₂ ⟨H₁, e₁⟩
          (mem_filter.2 ⟨mem_sigma.2 ⟨h1, he₁⟩, hn₁⟩)).symm
      · have hne1 : H₁ ≠ H := fun h' => hH (h' ▸ h1)
        have hne2 : H₂ ≠ H := fun h' => hH (h' ▸ h2)
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hdist H₁ h1 H₂ h2 h12 e₁ he₁ e₂ he₂ hn₁ hn₂

end RefinedAbsorption
