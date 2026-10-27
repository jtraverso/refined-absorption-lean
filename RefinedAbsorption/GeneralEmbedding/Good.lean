module
public import RefinedAbsorption.GeneralEmbedding.Bad

/-!
# Existence of a good embedding of one more supergraph
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {n r C : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ends : ι → Finset (Fin n)} {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
  {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}

open Classical in
theorem exists_good_embedding {G : Finset (Finset (Fin n))} {Q D C' γ : ℝ} (hγ : 0 < γ)
    (hQ : 2 ≤ Q) (hD1 : 1 ≤ D) (hn : 1 ≤ n) (hr : 1 ≤ r) (hC1 : 1 ≤ C)
    (hends : ∀ x, (ends x).card = r)
    (hdeg : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D)
    (href : IsCRefinedFamily C ℋ) (hsys : IsSupergraphSystem r ends ℋ m W)
    (hint : IsEdgeIntersecting ends ℋ m W)
    (hbd : ∀ H ∈ ℋ, (W H).card ≤ C) {𝒮 : Finset (Finset ι)} (h𝒮 : 𝒮 ⊆ ℋ)
    {φ : (H : Finset ι) → Fin (m H) → Fin n}
    (hacc : ∀ A : Finset (Fin n), A.card + 1 ≤ r →
      (accDeg W 𝒮 φ A : ℝ) ≤ thr Q ((C : ℝ) ^ 2) D n r A.card)
    (hC'0 : 0 < C') (hDn : D ≤ n / C')
    (hC' : 4 * (C * ((C : ℝ) ^ 2 + Kseq Q ((C : ℝ) ^ 2) (r - 1)) * (r : ℝ) ^ r) ≤ γ * C')
    (hQγ : 4 * (C * 2 ^ (3 * r + 1) * (r : ℝ) ^ r) ≤ γ * Q)
    {H : Finset ι} (hH : H ∈ ℋ)
    (hcount : γ * (n : ℝ) ^ (m H) ≤
      ((univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)).card : ℝ)) :
    ∃ f : Fin (m H) → Fin n, IsHostEmbedding G ends H (W H) f ∧
      (∀ e ∈ W H, e.toRight.Nonempty → ∀ p ∈ newPairs W 𝒮, embedEdge f e ≠ pimg φ p) ∧
      (∀ e ∈ W H, e.toRight.Nonempty → ∀ A ⊆ embedEdge f e, A.card + 1 ≤ r →
        ¬ A ⊆ e.toLeft → (accDeg W 𝒮 φ A : ℝ) + C ≤ thr Q ((C : ℝ) ^ 2) D n r A.card) := by
  have hb1 := card_bad1_le hγ (by linarith) (by linarith) hn hr hends hdeg href hint
    hsys.uniform hbd h𝒮 hacc hC'0 hDn hC' hH
  have hb2 := card_bad2_le hγ hQ hD1 hn hr hC1 hends hdeg href hint hsys.uniform hbd h𝒮 hacc
    hQγ hH
  set Good := univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)
  have hex : ∃ f ∈ Good, f ∉ bad1Set W 𝒮 φ H ∧ f ∉ bad2Set W 𝒮 φ Q D C r H := by
    by_contra hcon
    push_neg at hcon
    have hsub : Good ⊆ bad1Set W 𝒮 φ H ∪ bad2Set W 𝒮 φ Q D C r H := by
      intro f hf
      by_cases h1 : f ∈ bad1Set W 𝒮 φ H
      · exact mem_union_left _ h1
      · exact mem_union_right _ (hcon f hf h1)
    have hc : (Good.card : ℝ) ≤ (bad1Set W 𝒮 φ H).card + (bad2Set W 𝒮 φ Q D C r H).card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have hpos : 0 < γ * (n : ℝ) ^ (m H) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    linarith
  obtain ⟨f, hfG, hf1, hf2⟩ := hex
  have hf : IsHostEmbedding G ends H (W H) f := (mem_filter.1 hfG).2
  obtain ⟨hinj, havoid, _⟩ := id hf
  have hnotL : ∀ e ∈ W H, ∀ i, f i ∉ e.toLeft := fun e he i h =>
    havoid i (hsys.roots H hH e he h)
  refine ⟨f, hf, ?_, ?_⟩
  · intro e he hne p hp heq
    apply hf1
    unfold bad1Set
    refine mem_biUnion.2 ⟨e, mem_filter.2 ⟨he, hne⟩, mem_biUnion.2 ⟨p, ?_, ?_⟩⟩
    · exact mem_filter.2 ⟨hp, heq ▸ toLeft_subset_embedEdge f e⟩
    · refine mem_filter.2 ⟨mem_univ _, fun i hi => ?_⟩
      refine Finset.mem_sdiff.2 ⟨?_, hnotL e he i⟩
      rw [← heq]
      exact mem_embedEdge.2 (Or.inr ⟨i, hi, rfl⟩)
  · intro e he hne A hA hAr hAL
    by_contra hlt
    push_neg at hlt
    apply hf2
    set A' := A ∩ e.toLeft with hA'
    set B' := e.toRight.filter (fun i => f i ∈ A) with hB'
    set T := B'.image f with hT
    have hTA : T ⊆ A := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
      exact (mem_filter.1 hi).2
    have hdisj : Disjoint T A' := by
      rw [disjoint_left]
      intro y hy hyA
      obtain ⟨i, _, rfl⟩ := mem_image.1 hy
      exact hnotL e he i (mem_inter.1 hyA).2
    have hAeq : A' ∪ T = A := by
      ext x
      constructor
      · intro hx
        rcases mem_union.1 hx with h | h
        · exact (mem_inter.1 h).1
        · exact hTA h
      · intro hx
        by_cases hxL : x ∈ e.toLeft
        · exact mem_union_left _ (mem_inter.2 ⟨hx, hxL⟩)
        · rcases mem_embedEdge.1 (hA hx) with h | ⟨i, hi, rfl⟩
          · exact absurd h hxL
          · exact mem_union_right _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hx⟩, rfl⟩)
    have hTc : T.card = B'.card := card_image_of_injective _ hinj
    have hAc : A'.card + B'.card = A.card := by
      rw [← hTc, ← card_union_of_disjoint hdisj.symm, hAeq]
    have hB'ne : B'.Nonempty := by
      obtain ⟨x, hxA, hxL⟩ := not_subset.1 hAL
      rcases mem_embedEdge.1 (hA hxA) with h | ⟨i, hi, rfl⟩
      · exact absurd h hxL
      · exact ⟨i, mem_filter.2 ⟨hi, hxA⟩⟩
    unfold bad2Set
    refine mem_biUnion.2 ⟨e, mem_filter.2 ⟨he, hne⟩, mem_biUnion.2 ⟨A',
      mem_powerset.2 inter_subset_right, mem_biUnion.2 ⟨B',
        mem_filter.2 ⟨mem_powerset.2 (filter_subset _ _), hB'ne⟩,
        mem_biUnion.2 ⟨T, ?_, mem_filter.2 ⟨mem_univ _, fun i hi => mem_image_of_mem f hi⟩⟩⟩⟩⟩
    unfold satSets
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hTc⟩, hdisj, by omega, ?_⟩
    rw [hAc, hAeq]
    exact hlt

end RefinedAbsorption
