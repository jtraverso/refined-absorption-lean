module
public import RequestProject.General.CliquePiecesK
public import RequestProject.FlatOmni.Attach

/-!
# Attaching bounded absorbers to the pieces inside the reserve, uniformity `k`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Theorem 3.7 from Theorem 3.8: every
piece of the refiner receives a private bounded absorber, embedded with Lemma 5.2).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`absStageK` is `absStage` (`FlatOmni/Attach.lean`) in uniformity `k`.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.FlatDown
  RefinedAbsorption.Absorber17 RefinedAbsorption.FlatOmni

section Pieces

variable {n : ℕ}

/-- Root density for gadgets in uniformity `k` whose roots lie in a set `U` with
`|U| ≤ (K + 1) |P|`. -/
theorem rootDensityK {k : ℕ} {ι : Type*} [DecidableEq ι] (I : Finset ι) (Rt : ι → Finset (Fin n))
    (U P : Finset (Fin n)) (K B : ℕ) (hRU : ∀ i ∈ I, Rt i ⊆ U)
    (hR1 : ∀ i ∈ I, k - 1 ≤ (Rt i).card)
    (hD : ∀ S : Finset (Fin n), S.card = k - 1 → (I.filter fun i => S ⊆ Rt i).card ≤ B)
    (hU : U.card ≤ (K + 1) * P.card) :
    ∀ J : Finset (Fin n), J.card ≤ k - 1 →
      (I.filter fun i => J ⊆ Rt i).card ≤ ((K + 1) ^ (k - 1) * B) * P.card ^ (k - 1 - J.card) := by
  intro J hJ
  refine (rootIncidence_of_subset (r := k) I Rt U B hRU hR1 hD J hJ).trans ?_
  calc B * U.card ^ (k - 1 - J.card) ≤ B * ((K + 1) * P.card) ^ (k - 1 - J.card) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU _)
    _ = B * ((K + 1) ^ (k - 1 - J.card) * P.card ^ (k - 1 - J.card)) := by rw [mul_pow]
    _ ≤ B * ((K + 1) ^ (k - 1) * P.card ^ (k - 1 - J.card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega)))
    _ = ((K + 1) ^ (k - 1) * B) * P.card ^ (k - 1 - J.card) := by ring

end Pieces

/-- **Attached absorbers inside the reserve** (see the module docstring). -/
theorem absStageK {q k : ℕ} (hk : 2 ≤ k) (hkq : k < q) (C₂ K : ℕ) :
    ∃ Ca : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n)) (X : Finset E)
      (F : Finset (Finset (Fin n))) (𝒱 : Finset (Finset (E ⊕ Finset (Fin n))))
      (U P : Finset (Fin n)) (B : ℕ),
      IsMultiRefiner q k C₂ (Sum.elim ends id) (X.image Sum.inl) (F.image Sum.inr) 𝒱 →
      (∀ W ∈ 𝒱, Set.InjOn (Sum.elim ends id) ↑W) →
      (∀ W ∈ 𝒱, W.biUnion (Sum.elim ends id) ⊆ U) → U.card ≤ (K + 1) * P.card →
      (∀ S : Finset (Fin n), S.card = k - 1 → deg (X.image ends ∪ F) S ≤ B) →
      (∀ S : Finset (Fin n), S.card = k - 1 → pdeg (Sum.elim ends id) 𝒱 S ≤ B) →
      Ca * B ≤ P.card → 0 < P.card →
      ∃ AW Qon Qoff : Finset (E ⊕ Finset (Fin n)) → Finset (Finset (Fin n)),
        AbsDataK q k ends X F 𝒱 AW Qon Qoff ∧
        (∀ W ∈ 𝒱, ∀ f ∈ AW W, f ⊆ U ∪ P ∧ (f ∩ P).Nonempty) ∧
        (∀ S : Finset (Fin n), S.card = k - 1 → deg (𝒱.biUnion AW) S ≤ Ca * B) := by
  classical
  set Bl := libraryBound q k (by omega) hkq C₂ with hBl
  obtain ⟨Ce, hCe, hemb⟩ := reserveCliqueEmbedding k Bl (k * C₂)
  refine ⟨Ce * ((K + 1) ^ (k - 1)), ?_⟩
  intro n E _ ends X F 𝒱 U P B h hinj hspan hU hdeg hpd hCB hP
  set e₂ : E ⊕ Finset (Fin n) → Finset (Fin n) := Sum.elim ends id with he₂
  set I := 𝒱.filter fun W => W.Nonempty with hI
  have hgad : ∀ W ∈ I, ∃ T Ton Toff : Finset (Finset (Fin n ⊕ Fin Bl)),
      GadgetWF k (k * C₂) (vertexSet (W.image e₂)) T ∧
      ∀ φ, ValidPlacement (vertexSet (W.image e₂)) φ →
        IsBoundedAbsorber q k Bl (W.image e₂) (newEdges T φ) (newEdges Ton φ)
          (newEdges Toff φ) := by
    intro W hW
    obtain ⟨hWV, hWne⟩ := mem_filter.1 hW
    refine exists_absorberGadget (by omega) hkq C₂ (W.image e₂) ?_ ?_ ?_ (hWne.image _)
    · intro f hf
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hf
      exact h.rgraph y (h.subset W hWV hy)
    · intro S hS
      rw [← mdeg_eq_deg_image (hinj W hWV)]
      exact h.divisible W hWV S hS
    · exact card_image_le.trans (h.card_le W hWV)
  choose! T Ton Toff hTw hTabs using hgad
  have hvs : ∀ W : Finset (E ⊕ Finset (Fin n)), ∀ x,
      x ∈ vertexSet (W.image e₂) ↔ x ∈ W.biUnion e₂ := by
    intro W x
    rw [mem_vertexSet_iff', mem_biUnion]
    constructor
    · rintro ⟨e, he, hx⟩
      obtain ⟨y, hy, rfl⟩ := mem_image.1 he
      exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, hx⟩
      exact ⟨e₂ y, mem_image_of_mem _ hy, hx⟩
  have hRU : ∀ W ∈ I, vertexSet (W.image e₂) ⊆ U := fun W hW x hx =>
    hspan W (mem_filter.1 hW).1 ((hvs W x).1 hx)
  have hR1 : ∀ W ∈ I, k - 1 ≤ (vertexSet (W.image e₂)).card := by
    intro W hW
    obtain ⟨hWV, ⟨y, hy⟩⟩ := mem_filter.1 hW
    have h2 := h.rgraph y (h.subset W hWV hy)
    refine le_trans ?_ (card_le_card (subset_vertexSet (mem_image_of_mem e₂ hy)))
    change k - 1 ≤ (e₂ y).card
    omega
  have hD : ∀ S : Finset (Fin n), S.card = k - 1 →
      (I.filter fun W => S ⊆ vertexSet (W.image e₂)).card ≤ B := by
    intro S hS
    refine le_trans (card_le_card ?_) (hpd S hS)
    intro W hW
    obtain ⟨hWI, hv⟩ := mem_filter.1 hW
    refine mem_filter.2 ⟨(mem_filter.1 hWI).1, ?_⟩
    intro x hx
    exact (hvs W x).1 (hv hx)
  have hroot := rootDensityK (k := k) I (fun W => vertexSet (W.image e₂)) U P K B hRU hR1 hD hU
  have hhostdeg : ∀ S : Finset (Fin n), S.card = k - 1 →
      Ce * deg (X.image ends ∪ F) S ≤ P.card := by
    intro S hS
    refine le_trans (Nat.mul_le_mul_left _ (hdeg S hS)) (le_trans ?_ hCB)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨Φ, hvalid, hrange, hdisj, hhost, hdegA, -⟩ := hemb n I
    (fun W => vertexSet (W.image e₂)) T (X.image ends ∪ F) P ((K + 1) ^ (k - 1) * B) hTw hhostdeg
    (by rw [← mul_assoc]; exact hCB) hroot hP
  set AW : Finset (E ⊕ Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (T W) (Φ W) else ∅ with hAW
  set Qon : Finset (E ⊕ Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (Ton W) (Φ W) else ∅ with hQon
  set Qoff : Finset (E ⊕ Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (Toff W) (Φ W) else ∅ with hQoff
  have hbd : ∀ W ∈ 𝒱, IsBoundedAbsorber q k Bl (W.image e₂) (AW W) (Qon W) (Qoff W) := by
    intro W hW
    by_cases hWI : W ∈ I
    · simp only [hAW, hQon, hQoff, if_pos hWI]
      exact hTabs W hWI (Φ W) (hvalid W hWI)
    · have hW0 : W = ∅ := by
        by_contra hne
        exact hWI (mem_filter.2 ⟨hW, nonempty_iff_ne_empty.2 hne⟩)
      simp only [hAW, hQon, hQoff, if_neg hWI]
      rw [hW0, image_empty]
      exact isBoundedAbsorber_empty
  refine ⟨AW, Qon, Qoff, ⟨fun W hW => (hbd W hW).on, fun W hW => (hbd W hW).off, ?_, ?_, hinj⟩,
    ?_, ?_⟩
  · intro W hW W' hW' hne
    simp only [hAW]
    split_ifs with h1 h2 h2
    · exact hdisj W h1 W' h2 hne
    · exact disjoint_empty_right _
    · exact disjoint_empty_left _
    · exact disjoint_empty_left _
  · intro W _
    simp only [hAW]
    split_ifs with hWI
    · exact hhost W hWI
    · exact disjoint_empty_left _
  · intro W hW f hf
    simp only [hAW] at hf
    split_ifs at hf with hWI
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hf
      refine ⟨?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
        rcases y with a | p
        · exact mem_union_left _ (hRU W hWI ((hTw W hWI).edge_roots t ht a hy))
        · exact mem_union_right _ (hrange W hWI p)
      · obtain ⟨p, hp⟩ := (hTw W hWI).edge_aux t ht
        exact ⟨Φ W p, mem_inter.2 ⟨mem_image.2 ⟨Sum.inr p, hp, rfl⟩, hrange W hWI p⟩⟩
    · simp at hf
  · intro S hS
    have hsub : 𝒱.biUnion AW ⊆ I.biUnion fun W => newEdges (T W) (Φ W) := by
      intro f hf
      obtain ⟨W, hW, hfW⟩ := mem_biUnion.1 hf
      simp only [hAW] at hfW
      split_ifs at hfW with hWI
      · exact mem_biUnion.2 ⟨W, hWI, hfW⟩
      · simp at hfW
    refine le_trans (card_le_card (filter_subset_filter _ hsub)) ?_
    refine (hdegA S hS).trans ?_
    rw [mul_assoc]

end RefinedAbsorption.General
