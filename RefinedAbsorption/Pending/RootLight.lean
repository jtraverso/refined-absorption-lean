module
public import RefinedAbsorption.Faithful2024.Section6

/-!
# A uniformly bounded library of root-light absorbers

`rootLightLibrary`: for `q > r ≥ 1` and every bound `K` there is `B` such that every divisible
`r`-graph `LS` on `Fin k` (`k ≤ K`) whose vertex set is all of `Fin k` has an absorber on
`Fin k ⊕ Fin B` with an on-mode decomposition (of `A ∪ LS`) and an off-mode decomposition (of
`A`) all of whose cliques meet the roots `Fin k` in at most `r` vertices.

The on-mode comes from Lemma 6.4 (`Faithful2024.lemma_6_4`); for the off-mode, independence of the
roots forces at most `r - 1` root vertices.  The uniform bound is obtained by summing the sizes
over the finitely many `r`-graphs on `Fin k`, `k ≤ K`, and padding with isolated new vertices.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Absorber17

/-- The cliques of a decomposition of an absorber independent of its roots meet the roots in at
most `r - 1` vertices. -/
theorem off_inter_lt {q r k h : ℕ} {L A Qoff : Finset (Finset (Fin k ⊕ Fin h))}
    (hA : IsAbsorber q r L A) (hV : vertexSet L = univ.map Function.Embedding.inl)
    (hoff : IsDecomposition q r A Qoff) {P : Finset (Fin k ⊕ Fin h)} (hP : P ∈ Qoff) :
    (P ∩ univ.map Function.Embedding.inl).card < r := by
  by_contra hge
  push_neg at hge
  obtain ⟨t, htP, htc⟩ := exists_subset_card_eq hge
  have htA : t ∈ A := hoff.cliqueEdges_subset hP
    (mem_powersetCard.2 ⟨htP.trans inter_subset_left, htc⟩)
  exact hA.independent t htA (by rw [hV]; exact htP.trans inter_subset_right)

/-- Root intersections are preserved by padding the new vertices. -/
theorem card_inter_map_le {k h B : ℕ} (f : Fin k ⊕ Fin h ↪ Fin k ⊕ Fin B)
    (hf' : ∀ p, ∃ p', f (Sum.inr p) = Sum.inr p')
    (P : Finset (Fin k ⊕ Fin h)) :
    (P.map f ∩ univ.map Function.Embedding.inl).card ≤
      (P ∩ univ.map Function.Embedding.inl).card := by
  rw [← card_map f]
  apply card_le_card
  intro y hy
  obtain ⟨hyP, hyl⟩ := mem_inter.1 hy
  obtain ⟨x, hxP, rfl⟩ := mem_map.1 hyP
  obtain ⟨a, -, ha⟩ := mem_map.1 hyl
  refine mem_map_of_mem _ (mem_inter.2 ⟨hxP, ?_⟩)
  rcases x with b | p
  · exact mem_map_of_mem _ (mem_univ b)
  · obtain ⟨p', hp'⟩ := hf' p
    rw [hp'] at ha
    exact absurd ha Sum.inl_ne_inr

/-- The padding embedding. -/
def padEmb {k h B : ℕ} (hle : h ≤ B) : Fin k ⊕ Fin h ↪ Fin k ⊕ Fin B :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hle)

open Classical in
/-- The size of the Lemma 6.4 absorber chosen for `LS` (or `0`). -/
noncomputable def rlSize (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) (k : ℕ)
    (LS : Finset (Finset (Fin k))) : ℕ :=
  if h : IsRGraph r LS ∧ IsDivisible q r LS then
    Classical.choose (Faithful2024.lemma_6_4 q r hr hrq k LS h.1 h.2) else 0

/-- **The root-light library.** -/
theorem rootLightLibrary {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (K : ℕ) :
    ∃ B : ℕ, ∀ (k : ℕ) (LS : Finset (Finset (Fin k))), k ≤ K → IsRGraph r LS →
      IsDivisible q r LS → vertexSet LS = univ →
      ∃ A Qon Qoff : Finset (Finset (Fin k ⊕ Fin B)),
        IsAbsorber q r (RefinedAbsorption.gmap Function.Embedding.inl LS) A ∧
        IsDecomposition q r (A ∪ RefinedAbsorption.gmap Function.Embedding.inl LS) Qon ∧
        IsDecomposition q r A Qoff ∧
        ∀ P ∈ Qon ∪ Qoff, (P ∩ univ.map Function.Embedding.inl).card ≤ r := by
  classical
  refine ⟨∑ k ∈ range (K + 1), ∑ LS : Finset (Finset (Fin k)), rlSize q r hr hrq k LS, ?_⟩
  intro k LS hk hLr hdiv hV
  set B := ∑ k ∈ range (K + 1), ∑ LS : Finset (Finset (Fin k)), rlSize q r hr hrq k LS
  have hc : IsRGraph r LS ∧ IsDivisible q r LS := ⟨hLr, hdiv⟩
  set h₀ := rlSize q r hr hrq k LS with hh₀
  have hle : h₀ ≤ B := by
    have h1 : h₀ ≤ ∑ LS' : Finset (Finset (Fin k)), rlSize q r hr hrq k LS' :=
      single_le_sum (f := fun LS' => rlSize q r hr hrq k LS') (fun _ _ => Nat.zero_le _)
        (mem_univ LS)
    refine h1.trans ?_
    exact single_le_sum (f := fun k' => ∑ LS' : Finset (Finset (Fin k')),
      rlSize q r hr hrq k' LS') (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))
  have hspec := Classical.choose_spec (Faithful2024.lemma_6_4 q r hr hrq k LS hc.1 hc.2)
  have hh₀' : h₀ = Classical.choose (Faithful2024.lemma_6_4 q r hr hrq k LS hc.1 hc.2) := by
    rw [hh₀, rlSize, dif_pos hc]
  obtain ⟨A, Q, hA, hQ, hQr⟩ := hspec
  obtain ⟨Qoff, hoff⟩ := hA.decomp
  -- transport along the padding
  set f : Fin k ⊕ Fin (Classical.choose (Faithful2024.lemma_6_4 q r hr hrq k LS hc.1 hc.2)) ↪
    Fin k ⊕ Fin B := padEmb (hh₀' ▸ hle)
  have hfr : ∀ p, ∃ p', f (Sum.inr p) = Sum.inr p' := fun p => ⟨_, rfl⟩
  have hinl : Function.Embedding.inl.trans f = Function.Embedding.inl := by
    ext a; rfl
  have hVL : vertexSet (RefinedAbsorption.gmap
      (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin (Classical.choose
        (Faithful2024.lemma_6_4 q r hr hrq k LS hc.1 hc.2))) LS) =
      univ.map Function.Embedding.inl := by
    rw [vertexSet_gmap, hV]
  refine ⟨RefinedAbsorption.gmap f A, RefinedAbsorption.gmap f Q,
    RefinedAbsorption.gmap f Qoff, ?_, ?_, hoff.gmap f, ?_⟩
  · have := hA.gmap f
    rwa [gmap_gmap, hinl] at this
  · have := hQ.gmap f
    rwa [gmap_union, gmap_gmap, hinl] at this
  · intro P hP
    rcases mem_union.1 hP with hP | hP
    · obtain ⟨P₀, hP₀, rfl⟩ := mem_gmap.1 hP
      exact (card_inter_map_le f hfr P₀).trans (hQr P₀ hP₀).1
    · obtain ⟨P₀, hP₀, rfl⟩ := mem_gmap.1 hP
      exact (card_inter_map_le f hfr P₀).trans (off_inter_lt hA hVL hoff hP₀).le

end RefinedAbsorption.Pending
