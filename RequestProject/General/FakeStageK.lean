module
public import RequestProject.General.FakeRounds

/-!
# Fake edges for the new copies of a local refiner, uniformity `k`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Theorem 1.11 (fake edges
embedded with the Partial Clique Embedding Lemma 5.2).  Lean formalization: Juan Pablo Traverso
Gianini, Apache-2.0.

**`fakeStageK`**: `fakeStage` (`FlatOmni/Fakes.lean`) in uniformity `k`.  Every new copy of a
multi-refiner whose new copies lie in `Y ∪ P` is replaced by a fake edge whose auxiliary vertices
lie in the reserve `P`; the new edges form a simple `k`-graph `F` whose edges all meet `P`, and
the `(k-1)`-degrees of `F` and of the new pieces stay `O(B)`.  The gadgets are placed in rounds
(`fakeRoundsAll`), which keeps the pieces sparse.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.RefineDown
  RefinedAbsorption.FlatDown RefinedAbsorption.FlatOmni

/-- **Fake edges for the new copies of a local refiner, uniformity `k`.** -/
theorem fakeStageK {q k : ℕ} (hk : 2 ≤ k) (hkq : k < q) (C K : ℕ) :
    ∃ Cf C₂ : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (X R : Finset E) (𝒲 : Finset (Finset E)) (Y P : Finset (Fin n)) (B : ℕ),
      IsMultiRefiner q k C ends X R 𝒲 → (∀ c ∈ X, ends c ⊆ Y) → (∀ c ∈ R, ends c ⊆ Y ∪ P) →
      Disjoint Y P → (∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1) →
      (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends R S ≤ B) →
      (∀ S : Finset (Fin n), S.card = k - 1 → pdeg ends 𝒲 S ≤ B) →
      Y.card ≤ K * P.card → Cf * B ≤ P.card → 0 < P.card →
      ∃ (F : Finset (Finset (Fin n))) (𝒱 : Finset (Finset (E ⊕ Finset (Fin n)))),
        IsMultiRefiner q k C₂ (Sum.elim ends id) (X.image Sum.inl) (F.image Sum.inr) 𝒱 ∧
        (∀ f ∈ F, f ⊆ Y ∪ P ∧ (f ∩ P).Nonempty) ∧
        (∀ S : Finset (Fin n), S.card = k - 1 → deg F S ≤ C₂ * B) ∧
        (∀ S : Finset (Fin n), S.card = k - 1 → pdeg (Sum.elim ends id) 𝒱 S ≤ C₂ * B) ∧
        (∀ W ∈ 𝒱, Set.InjOn (Sum.elim ends id) ↑W) ∧
        (∀ W ∈ 𝒱, (W.filter fun y => y ∈ X.image Sum.inl).card ≤ 1) := by
  classical
  obtain ⟨Cs, Cr, hrounds⟩ := fakeRoundsAll k (fakeAux q k) C K (C * C + 1)
  set B₀ := fakeCount q k * q.choose k with hB₀
  refine ⟨Cs, C * (1 + B₀) + Cr + 1, ?_⟩
  intro n E _ ends X R 𝒲 Y P B h hXY hRYP hYP hone hdegR hpd hYK hCB hP
  have hRr : ∀ c ∈ R, (ends c).card = k := fun c hc => h.rgraph c (mem_union_right _ hc)
  have hr : ∀ c ∈ X ∪ R, (ends c).card = k := fun c hc => h.rgraph c hc
  have hYPc : (Y ∪ P).card ≤ (K + 1) * P.card :=
    (card_union_le Y P).trans (by rw [add_mul, one_mul]; omega)
  have hXRU : ∀ c ∈ X ∪ R, ends c ⊆ Y ∪ P := by
    intro c hc
    rcases mem_union.1 hc with hc | hc
    · exact (hXY c hc).trans subset_union_left
    · exact hRYP c hc
  obtain ⟨col, hcolN, hcol⟩ := exists_piece_coloring R 𝒲 C
    (fun c hc => h.mult_le c (mem_union_right _ hc)) (fun W hW => h.card_le W hW)
  set Tt : E → Finset (Finset (Fin n ⊕ Fin (fakeAux q k))) := fun c => fakeTemplate q k (ends c)
    with hTt
  obtain ⟨Φ, hΦ⟩ := hrounds n ends X R 𝒲 col Tt (Y ∪ P) P B subset_union_right hYPc hP hr hXRU
    (fun W hW => h.subset W hW) (fun c hc => h.mult_le c (mem_union_right _ hc))
    (fun W hW => h.card_le W hW) (fun c hc => fakeTemplate_wf (hRr c hc)) hcol hcolN hdegR hpd
    hCB
  have hvalid : ∀ c ∈ R, ValidPlacement (ends c) (Φ c) := fun c hc => hΦ.valid c hc (hcolN c hc)
  have hrange : ∀ c ∈ R, ∀ p, Φ c p ∈ P := fun c hc => hΦ.range c hc (hcolN c hc)
  set NE : E → Finset (Finset (Fin n)) := fun c => newEdges (Tt c) (Φ c) with hNEdef
  have hNE : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → Disjoint (NE c) (NE c') :=
    fun c hc c' hc' hcc' => hΦ.disj c hc c' hc' (hcolN c hc) (hcolN c' hc') hcc'
  have hNEr : ∀ c ∈ R, ∀ f ∈ NE c, f.card = k := fun c hc f hf =>
    card_of_mem_newEdges (fakeTemplate_wf (hRr c hc)) (hvalid c hc) hf
  have hNEc : ∀ c ∈ R, (NE c).card ≤ B₀ := fun c hc => by
    rw [hNEdef]
    simp only
    rw [card_newEdges (fakeTemplate_wf (hRr c hc)) (hvalid c hc)]
    exact card_fakeTemplate_le (by omega) (hRr c hc)
  have hNEdiv : ∀ c ∈ R, ∀ S : Finset (Fin n), S.card < k →
      ((deg (NE c) S : ℕ) : ZMod ((q - S.card).choose (k - S.card))) =
        if S ⊆ ends c then 1 else 0 := fun c hc S hS =>
    deg_placedFake_cast (by omega) (hRr c hc) (hvalid c hc) S hS
  have href := fakePiece_refinerK h hNE hNEr hNEc hNEdiv
  have hsubF : ∀ c ∈ R, ∀ f ∈ NE c, f ⊆ ends c ∪ auxImage (Φ c) := by
    intro c hc f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hf
    exact placeEdge_subset (fakeTemplate_wf (hRr c hc)) (Φ c) ht
  have haux : ∀ c ∈ R, auxImage (Φ c) ⊆ P := by
    intro c hc v hv
    obtain ⟨p, -, rfl⟩ := mem_image.1 hv
    exact hrange c hc p
  have hflat : ∀ f ∈ R.biUnion NE, f ⊆ Y ∪ P ∧ (f ∩ P).Nonempty := by
    intro f hf
    obtain ⟨c, hc, hfc⟩ := mem_biUnion.1 hf
    refine ⟨(hsubF c hc f hfc).trans (union_subset (hRYP c hc)
      ((haux c hc).trans subset_union_right)), ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hfc
    obtain ⟨p, hp⟩ := (fakeTemplate_wf (hRr c hc)).edge_aux t ht
    exact ⟨Φ c p, mem_inter.2 ⟨mem_image.2 ⟨Sum.inr p, hp, rfl⟩, hrange c hc p⟩⟩
  have hFeq : R.biUnion NE = (R.filter fun c => col c < C * C + 1).biUnion NE := by
    rw [filter_true_of_mem fun c hc => hcolN c hc]
  have hC₂ : C * (1 + B₀) ≤ C * (1 + B₀) + Cr + 1 := by omega
  have hCr : Cr * B ≤ (C * (1 + B₀) + Cr + 1) * B := Nat.mul_le_mul_right _ (by omega)
  refine ⟨R.biUnion NE, 𝒲.image (fakePiece X R NE), href.mono hC₂, hflat, fun S hS => ?_,
    fun S hS => ?_, ?_, ?_⟩
  · rw [hFeq]
    exact (hΦ.deg S hS).trans hCr
  · -- piece degrees: the span of a fake piece lies in the final round span
    have hspan : ∀ W ∈ 𝒲, (fakePiece X R NE W).biUnion (Sum.elim ends id) ⊆
        roundSpan ends R col Φ (C * C + 1) W := by
      intro W _ v hv
      obtain ⟨y, hy, hvy⟩ := mem_biUnion.1 hv
      rcases y with x | f
      · obtain ⟨hxW, -⟩ := inl_mem_fakePiece.1 hy
        exact mem_union_left _ (mem_biUnion.2 ⟨x, hxW, hvy⟩)
      · obtain ⟨c, hcW, hcR, hfc⟩ := inr_mem_fakePiece.1 hy
        rcases mem_union.1 (hsubF c hcR f hfc hvy) with h1 | h1
        · exact mem_union_left _ (mem_biUnion.2 ⟨c, hcW, h1⟩)
        · exact mem_union_right _ (mem_biUnion.2 ⟨c, mem_filter.2 ⟨hcW, hcR, hcolN c hcR⟩, h1⟩)
    unfold pdeg
    rw [filter_image]
    refine card_image_le.trans ((card_le_card fun W hW => ?_).trans ((hΦ.pdeg S hS).trans hCr))
    obtain ⟨hW𝒲, hSW⟩ := mem_filter.1 hW
    exact mem_filter.2 ⟨hW𝒲, hSW.trans (hspan W hW𝒲)⟩
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    intro y₁ hy₁ y₂ hy₂ heq
    rcases y₁ with x₁ | f₁ <;> rcases y₂ with x₂ | f₂
    · obtain ⟨hx₁W, hx₁X⟩ := inl_mem_fakePiece.1 hy₁
      obtain ⟨hx₂W, hx₂X⟩ := inl_mem_fakePiece.1 hy₂
      rw [card_le_one.1 (hone W hW) x₁ (mem_filter.2 ⟨hx₁W, hx₁X⟩) x₂
        (mem_filter.2 ⟨hx₂W, hx₂X⟩)]
    · exfalso
      obtain ⟨-, hx₁X⟩ := inl_mem_fakePiece.1 hy₁
      obtain ⟨c, -, hcR, hfc⟩ := inr_mem_fakePiece.1 hy₂
      obtain ⟨z, hz⟩ := (hflat f₂ (mem_biUnion.2 ⟨c, hcR, hfc⟩)).2
      have hzf := (mem_inter.1 hz).1
      change ends x₁ = f₂ at heq
      rw [← heq] at hzf
      exact disjoint_left.1 hYP (hXY x₁ hx₁X hzf) (mem_inter.1 hz).2
    · exfalso
      obtain ⟨-, hx₂X⟩ := inl_mem_fakePiece.1 hy₂
      obtain ⟨c, -, hcR, hfc⟩ := inr_mem_fakePiece.1 hy₁
      obtain ⟨z, hz⟩ := (hflat f₁ (mem_biUnion.2 ⟨c, hcR, hfc⟩)).2
      have hzf := (mem_inter.1 hz).1
      change f₁ = ends x₂ at heq
      rw [heq] at hzf
      exact disjoint_left.1 hYP (hXY x₂ hx₂X hzf) (mem_inter.1 hz).2
    · change f₁ = f₂ at heq
      rw [heq]
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    refine le_trans (card_le_card (t := (W.filter (· ∈ X)).image
      (Sum.inl : E → E ⊕ Finset (Fin n))) ?_) (card_image_le.trans (hone W hW))
    · intro y hy
      obtain ⟨hyW, hyX⟩ := mem_filter.1 hy
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hyX
      exact mem_image.2 ⟨x, mem_filter.2 ⟨(inl_mem_fakePiece.1 hyW).1, hx⟩, rfl⟩

end RefinedAbsorption.General
