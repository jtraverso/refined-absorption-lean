module
public import RefinedAbsorption.Placement.Cluster
public import RefinedAbsorption.Placement.FakeGadget
public import RefinedAbsorption.Placement.ImageRefiner
public import RefinedAbsorption.Placement.Interface

/-!
# Multiplicity reduction inside `K_n^r`

We apply the (clustered) Partial Clique Embedding Lemma to fake edges.  Starting from a strong
multi-refiner on `Fin n` (copies labelled by `E`, kept copies `K ⊇ X`), every copy of `R` outside
`K` is replaced by a fake edge placed *inside `Fin n`*.  Different fake edges may share vertices;
their edges are pairwise disjoint and disjoint from the kept copies.  The result is a strong
(simple) refiner on `Fin n` with the same degree budget up to a constant
(`placedMultiplicityReduction`).

The pieces of the refiner are the clusters of the placement (together with one singleton cluster
per fake edge), so the refinement-degree invariant (`pieceDeg`) survives the placement.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Absorber17

theorem card_filter_disjSum_le {α β : Type*} (s : Finset α) (t : Finset β) (f : α ⊕ β → Prop)
    [DecidablePred f] :
    ((s.disjSum t).filter f).card ≤ (s.filter (f ∘ Sum.inl)).card +
      (t.filter (f ∘ Sum.inr)).card := by
  rw [← card_disjSum]
  apply card_le_card
  intro x hx
  rw [mem_filter, mem_disjSum] at hx
  rcases hx with ⟨⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩, hf⟩
  · exact inl_mem_disjSum.2 (mem_filter.2 ⟨ha, hf⟩)
  · exact inr_mem_disjSum.2 (mem_filter.2 ⟨hb, hf⟩)

theorem mdeg_union_le {V E : Type*} [DecidableEq V] [DecidableEq E] (ends : E → Finset V)
    (G H : Finset E) (S : Finset V) : mdeg ends (G ∪ H) S ≤ mdeg ends G S + mdeg ends H S := by
  unfold mdeg; rw [filter_union]; exact card_union_le _ _

theorem card_biUnion_ends_le {V E : Type*} [DecidableEq V] {r : ℕ} (ends : E → Finset V)
    (W : Finset E) (hW : ∀ i ∈ W, (ends i).card = r) : (W.biUnion ends).card ≤ W.card * r := by
  refine card_biUnion_le.trans ?_
  rw [sum_congr rfl hW, sum_const, smul_eq_mul]

theorem deg_le_mdeg_of_subset_image {V E : Type*} [DecidableEq V] (ends : E → Finset V)
    {G : Finset E} {H : Finset (Finset V)} (hH : H ⊆ G.image ends) (S : Finset V) :
    deg H S ≤ mdeg ends G S := by
  classical
  unfold deg mdeg
  refine le_trans (card_le_card (t := (G.filter fun i => S ⊆ ends i).image ends) ?_)
    card_image_le
  intro f hf
  obtain ⟨hfH, hSf⟩ := mem_filter.1 hf
  obtain ⟨i, hi, rfl⟩ := mem_image.1 (hH hfH)
  exact mem_image.2 ⟨i, mem_filter.2 ⟨hi, hSf⟩, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **Multiplicity reduction inside `K_n^r`.**  Fix `2 ≤ r < q` and `C ≥ 1`.  There is `C'` such
that every strong `C`-refined multi-refiner on `Fin n` with degree budget `D`, `C' · D ≤ n`,
yields a strong `C'`-refined (simple) refiner on `Fin n` of the image of `X`, with the same
budget `D`: the duplicate copies are replaced by fake edges placed inside `Fin n`. -/
theorem placedMultiplicityReduction {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) (C : ℕ) (hC : 1 ≤ C) :
    ∃ C' : ℕ, 0 < C' ∧ ∀ (n : ℕ) {E : Type*} [DecidableEq E] (ends : E → Finset (Fin n))
      (K X R : Finset E) (𝒲 : Finset (Finset E)) (D : ℕ),
      IsStrongMultiRefiner q r C ends K X R 𝒲 D → C' * D ≤ n → 0 < n →
      ∃ (R' : Finset (Finset (Fin n))) (𝒲' : Finset (Finset (Finset (Fin n)))),
        IsStrongRefiner q r C' (X.image ends) R' 𝒲' D := by
  classical
  obtain ⟨Ccl, hCcl, hcl⟩ := clusteredPlacement r (fakeAux q r) r (C * r) (C + 1)
  set C' := C * fakeBound q r + C + Ccl * (1 + 2 * C) + 1 with hC'def
  refine ⟨C', by omega, ?_⟩
  intro n E _ ends K X R 𝒲 D hS hCD hn
  have hM := hS.refiner
  have hrg : ∀ i ∈ X ∪ R, (ends i).card = r := hM.rgraph
  set I := R.filter (· ∉ K)
  have hIR : I ⊆ R := filter_subset _ _
  have hInK : ∀ i ∈ I, i ∉ K := fun i hi => (mem_filter.1 hi).2
  set T : E → Finset (Finset (Fin n ⊕ Fin (fakeAux q r))) := fun i => fakeTemplate q r (ends i)
  set P : Finset (Finset E ⊕ E) := (𝒲.filter fun W => W.Nonempty).disjSum I
  set V₀ : Finset E ⊕ E → Finset (Fin n) := Sum.elim (fun W => W.biUnion ends) ends
  set Mem : Finset E ⊕ E → Finset E := Sum.elim id (fun i => {i})
  set G : Finset (Finset (Fin n)) := ((X ∪ R).filter (· ∈ K)).image ends
  set Dp := (1 + 2 * C) * D
  have hw : ∀ i ∈ I, GadgetWF r r (ends i) (T i) := fun i hi =>
    fakeTemplate_wf (hrg i (mem_union_right _ (hIR hi)))
  have hP : ∀ p ∈ P, (V₀ p).card ≤ C * r ∧ r - 1 ≤ (V₀ p).card ∧ (Mem p).card ≤ C + 1 := by
    intro p hp
    rcases mem_disjSum.1 hp with ⟨W, hW, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨hW𝒲, ⟨j, hj⟩⟩ := mem_filter.1 hW
      have hWsub := hM.subset W hW𝒲
      refine ⟨?_, ?_, ?_⟩
      · exact (card_biUnion_ends_le ends W fun i hi => hrg i (hWsub hi)).trans
          (Nat.mul_le_mul_right _ (hM.card_le W hW𝒲))
      · calc r - 1 ≤ (ends j).card := by rw [hrg j (hWsub hj)]; omega
          _ ≤ _ := card_le_card (subset_biUnion_of_mem ends hj)
      · exact (hM.card_le W hW𝒲).trans (Nat.le_succ _)
    · have := hrg i (mem_union_right _ (hIR hi))
      refine ⟨?_, ?_, ?_⟩
      · show (ends i).card ≤ C * r
        rw [this]; exact Nat.le_mul_of_pos_left _ hC
      · show r - 1 ≤ (ends i).card
        omega
      · show ({i} : Finset E).card ≤ C + 1
        simp
  have hmem : ∀ i ∈ I, (P.filter fun p => i ∈ Mem p).card ≤ C + 1 := by
    intro i hi
    refine (card_filter_disjSum_le _ _ _).trans (Nat.add_le_add ?_ ?_)
    · refine le_trans (card_le_card ?_) (hM.mult_le i (mem_union_right _ (hIR hi)))
      intro W hW
      simp only [mem_filter, Function.comp, Mem, Sum.elim_inl, id] at hW ⊢
      exact ⟨hW.1.1, hW.2⟩
    · refine le_trans (card_le_card ?_) (card_singleton i).le
      intro j hj
      simp only [mem_filter, Function.comp, Mem, Sum.elim_inr, mem_singleton] at hj
      simp [hj.2]
  have hcover : ∀ i ∈ I, ∃ p ∈ P, i ∈ Mem p ∧ ends i ⊆ V₀ p := fun i hi =>
    ⟨Sum.inr i, inr_mem_disjSum.2 hi, by simp [Mem], subset_rfl⟩
  have hdegXR : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends (X ∪ R) S ≤ (1 + C) * D := by
    intro S hS'
    refine (mdeg_union_le ends X R S).trans ?_
    have := hS.degX S hS'
    have := hS.degR S hS'
    nlinarith
  have hGdeg : ∀ S : Finset (Fin n), S.card = r - 1 → deg G S ≤ (1 + C) * D := by
    intro S hS'
    refine le_trans (deg_le_mdeg_of_subset_image ends (image_subset_image (filter_subset _ _)) S)
      (hdegXR S hS')
  have hCclDp : Ccl * Dp ≤ n := by
    refine le_trans ?_ hCD
    simp only [Dp, hC'def, ← mul_assoc]
    apply Nat.mul_le_mul_right
    omega
  have hG : ∀ S : Finset (Fin n), S.card = r - 1 → Ccl * deg G S ≤ n := by
    intro S hS'
    refine le_trans (Nat.mul_le_mul_left _ ((hGdeg S hS').trans ?_)) hCclDp
    simp only [Dp]
    exact Nat.mul_le_mul_right _ (by omega)
  have hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (P.filter fun p => S ⊆ V₀ p).card ≤ Dp := by
    intro S hS'
    refine (card_filter_disjSum_le _ _ _).trans ?_
    have h1 : ((𝒲.filter fun W => W.Nonempty).filter ((fun p => S ⊆ V₀ p) ∘ Sum.inl)).card ≤
        C * D := by
      refine le_trans (card_le_card ?_) (hS.pieceDeg S hS')
      intro W hW
      simp only [mem_filter, Function.comp, V₀, Sum.elim_inl] at hW ⊢
      exact ⟨hW.1.1, hW.2⟩
    have h2 : (I.filter ((fun p => S ⊆ V₀ p) ∘ Sum.inr)).card ≤ C * D := by
      refine le_trans (card_le_card ?_) (hS.degR S hS')
      intro i hi
      simp only [mem_filter, Function.comp, V₀, Sum.elim_inr] at hi ⊢
      exact ⟨hIR hi.1, hi.2⟩
    simp only [Dp]
    nlinarith
  obtain ⟨Φ, hvalid, hdisj, hhost, hdegnew, hpiece⟩ :=
    hcl n I ends T P V₀ Mem G Dp hw hP hmem hcover hG hDeg hCclDp hn
  -- the images of the copies
  set img : E → Finset (Finset (Fin n)) := fun i =>
    if i ∈ K then {ends i} else newEdges (T i) (Φ i)
  have hI_of : ∀ i ∈ X ∪ R, i ∉ K → i ∈ I := by
    intro i hi hiK
    rcases mem_union.1 hi with h | h
    · exact absurd (hS.keep h) hiK
    · exact mem_filter.2 ⟨h, hiK⟩
  have himg : IsImageSystem q r (fakeBound q r) ends K (X ∪ R) img := by
    refine ⟨fun i hi => by simp [img, hi], ?_, ?_, ?_, ?_⟩
    · intro i hi f hf
      by_cases hiK : i ∈ K
      · simp only [img, if_pos hiK, mem_singleton] at hf
        rw [hf]; exact hrg i hi
      · simp only [img, if_neg hiK] at hf
        have hiI := hI_of i hi hiK
        exact card_of_mem_newEdges (hw i hiI) (hvalid i hiI) hf
    · intro i hi j hj hij
      by_cases hiK : i ∈ K <;> by_cases hjK : j ∈ K
      · simp only [img, if_pos hiK, if_pos hjK, disjoint_singleton]
        exact fun h => hij (hS.inj hiK hjK h)
      · simp only [img, if_pos hiK, if_neg hjK, disjoint_singleton_left]
        intro h
        have hjI := hI_of j hj hjK
        exact disjoint_left.1 (hhost j hjI) h
          (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hiK⟩, rfl⟩)
      · simp only [img, if_neg hiK, if_pos hjK, disjoint_singleton_right]
        intro h
        have hiI := hI_of i hi hiK
        exact disjoint_left.1 (hhost i hiI) h
          (mem_image.2 ⟨j, mem_filter.2 ⟨hj, hjK⟩, rfl⟩)
      · simp only [img, if_neg hiK, if_neg hjK]
        exact hdisj i (hI_of i hi hiK) j (hI_of j hj hjK) hij
    · intro i hi
      by_cases hiK : i ∈ K
      · simp only [img, if_pos hiK, card_singleton]; exact one_le_fakeBound
      · simp only [img, if_neg hiK]
        have hiI := hI_of i hi hiK
        rw [card_newEdges (hw i hiI) (hvalid i hiI)]
        exact (card_fakeTemplate_le hrq.le (hrg i hi)).trans (Nat.le_succ _)
    · intro i hi S hS'
      by_cases hiK : i ∈ K
      · simp only [img, if_pos hiK, deg, filter_singleton]
        split_ifs <;> simp
      · simp only [img, if_neg hiK]
        have hiI := hI_of i hi hiK
        exact deg_placedFake_cast hrq.le (hrg i hi) (hvalid i hiI) S hS'
  have hRR := isRefinedRefiner_images hM hS.keep himg one_le_fakeBound
  have hRI : ∀ i ∈ I, img i = newEdges (T i) (Φ i) := fun i hi => by
    simp [img, hInK i hi]
  refine ⟨R.biUnion img, 𝒲.image fun W => W.biUnion img, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hRR.mono (by omega)
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    exact (card_filter_images_le hS.keep himg (hM.subset W hW) subset_union_left).trans
      (hS.oneX W hW)
  · intro S hS'
    exact le_trans (deg_le_mdeg_of_subset_image ends subset_rfl S) (hS.degX S hS')
  · intro S hS'
    have hsplit : R.biUnion img ⊆ (R.filter (· ∈ K)).image ends ∪
        I.biUnion fun i => newEdges (T i) (Φ i) := by
      intro f hf
      obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
      by_cases hiK : i ∈ K
      · simp only [img, if_pos hiK, mem_singleton] at hfi
        exact mem_union_left _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hiK⟩, hfi.symm⟩)
      · have hiI : i ∈ I := mem_filter.2 ⟨hi, hiK⟩
        rw [hRI i hiI] at hfi
        exact mem_union_right _ (mem_biUnion.2 ⟨i, hiI, hfi⟩)
    have h1 : deg ((R.filter (· ∈ K)).image ends) S ≤ C * D := by
      exact le_trans (deg_le_mdeg_of_subset_image ends
        (image_subset_image (filter_subset _ _)) S) (hS.degR S hS')
    have h2 := hdegnew S hS'
    calc deg (R.biUnion img) S ≤ deg ((R.filter (· ∈ K)).image ends ∪
          I.biUnion fun i => newEdges (T i) (Φ i)) S :=
          card_le_card (filter_subset_filter _ hsplit)
      _ ≤ deg ((R.filter (· ∈ K)).image ends) S +
          deg (I.biUnion fun i => newEdges (T i) (Φ i)) S := by
          unfold deg; rw [filter_union]; exact card_union_le _ _
      _ ≤ C * D + Ccl * Dp := Nat.add_le_add h1 h2
      _ ≤ C' * D := by
          simp only [Dp, hC'def]
          nlinarith
  · intro S hS'
    have hSne : S.Nonempty := by rw [← card_pos, hS']; omega
    have step1 : ((𝒲.image fun W => W.biUnion img).filter fun W' => S ⊆ vertexSet W').card ≤
        (𝒲.filter fun W => S ⊆ vertexSet (W.biUnion img)).card := by
      calc
        _ ≤ ((𝒲.filter fun W => S ⊆ vertexSet (W.biUnion img)).image
            fun W => W.biUnion img).card := by
          apply card_le_card
          intro W' hW'
          obtain ⟨hW'm, hSW'⟩ := mem_filter.1 hW'
          obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'm
          exact mem_image.2 ⟨W, mem_filter.2 ⟨hW, hSW'⟩, rfl⟩
        _ ≤ _ := card_image_le
    have step2 : (𝒲.filter fun W => S ⊆ vertexSet (W.biUnion img)).card ≤
        (P.filter fun p => S ⊆ pvOf V₀ Mem Φ I p).card := by
      rw [← card_map ⟨Sum.inl, Sum.inl_injective⟩]
      apply card_le_card
      intro p hp
      obtain ⟨W, hW, rfl⟩ := mem_map.1 hp
      obtain ⟨hW𝒲, hSW⟩ := mem_filter.1 hW
      have hWne : W.Nonempty := by
        obtain ⟨x, hx⟩ := hSne
        obtain ⟨f, hf, -⟩ := mem_sup.1 (hSW hx)
        obtain ⟨i, hi, -⟩ := mem_biUnion.1 hf
        exact ⟨i, hi⟩
      refine mem_filter.2 ⟨inl_mem_disjSum.2 (mem_filter.2 ⟨hW𝒲, hWne⟩), hSW.trans ?_⟩
      intro x hx
      obtain ⟨f, hf, hxf⟩ := mem_sup.1 hx
      obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
      have hiXR := hM.subset W hW𝒲 hi
      show x ∈ W.biUnion ends ∪ (W.filter (· ∈ I)).biUnion fun j => auxImage (Φ j)
      by_cases hiK : i ∈ K
      · simp only [img, if_pos hiK, mem_singleton] at hfi
        subst hfi
        exact mem_union_left _ (mem_biUnion.2 ⟨i, hi, hxf⟩)
      · have hiI := hI_of i hiXR hiK
        simp only [img, if_neg hiK] at hfi
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hfi
        rcases mem_union.1 (placeEdge_subset (hw i hiI) (Φ i) ht hxf) with h1 | h1
        · exact mem_union_left _ (mem_biUnion.2 ⟨i, hi, h1⟩)
        · exact mem_union_right _ (mem_biUnion.2 ⟨i, mem_filter.2 ⟨hi, hiI⟩, h1⟩)
    refine step1.trans (step2.trans ((hpiece S hS').trans ?_))
    calc Ccl * Dp = (Ccl * (1 + 2 * C)) * D := by simp only [Dp]; ring
      _ ≤ C' * D := Nat.mul_le_mul_right _ (by omega)

end RefinedAbsorption.Placement
