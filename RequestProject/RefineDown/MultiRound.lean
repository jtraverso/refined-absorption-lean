module
public import RequestProject.RefineDown.RoundGadgetGen
public import RequestProject.Placement.MultiEmbed
public import RequestProject.RefineDown.Round

/-!
# The anti-edge round into a reserve, with parallel copies allowed

`placedReserveRound` places the anti-edge round inside a reserve `Z` so that all new edges are
distinct and avoid a host graph; this needs `C · D ≤ |Z|`.  Here the new copies are labelled
copies of a multigraph, so different gadgets may create parallel copies.  The gadgets are placed
with `multiCliqueEmbedding`, which works for every degree `D`; this is the version used in the
dense part of the refine-down construction.

`multiRound`: for `1 ≤ r < q` there is `C ≥ 1` such that for every labelled `r`-multigraph `X`
on `Fin n` and every reserve `Z` with `|Z| ≥ C` such that every `j`-set lies in at most
`D · |Z|^(r-1-j)` copies of `X`, the anti-edge round of `X` with all new vertices inside `Z` is a
residual refiner whose residue consists of new copies, every new copy meets `Z` and lies in
`ends x ∪ Z` for a copy `x` of `X`, every piece contains at most one copy of `X`, and the new
copies and the pieces have `(r-1)`-degrees at most `C · D`.
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown.Gen

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.RefineDown

variable {n q r : ℕ} {E : Type} [DecidableEq E]

theorem mem_stepR_iff' {ends : E → Finset (Fin n)} {j₀ : Fin (fakeCount q r)} {X : Finset E}
    {c : SC (Fin n) E q r} :
    c ∈ stepR q r ends j₀ X ↔ ∃ f, c = Sum.inr f ∧ ∃ i ∈ X, f ∈ Ed q r ends j₀ i := by
  rcases c with i | f
  · simp [stepR]
  · simp [stepR, Ed]

omit [DecidableEq E] in
theorem image_liftE_psiV' (ends : E → Finset (Fin n)) (Φ : E → Fin (roundAux q r) → Fin n)
    (c : E) : (liftE q r ends c).image (psiV Φ) = ends c := by
  ext v
  simp [liftE, lift, ends2, psiV]

set_option maxHeartbeats 1000000 in
/-- **The anti-edge round into a reserve, multigraph version.** -/
theorem multiRound (hr : 1 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (X : Finset E) (Z : Finset (Fin n)) (D : ℕ),
      MIsRGraph r ends X → C ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 → mdeg ends X J ≤ D * Z.card ^ (r - 1 - J.card)) →
      ∃ (ends' : SC (Fin n) E q r → Finset (Fin n)) (R Y : Finset (SC (Fin n) E q r))
        (𝒲 : Finset (Finset (SC (Fin n) E q r))),
        (∀ x, ends' (Sum.inl x) = ends x) ∧
        IsResidualMultiRefiner q r C ends' (X.map Function.Embedding.inl) R Y 𝒲 ∧
        Y ⊆ R ∧ (∀ c ∈ R, ∀ x, c ≠ Sum.inl x) ∧
        (∀ c ∈ R, (ends' c ∩ Z).Nonempty) ∧
        (∀ c ∈ R, ∃ x ∈ X, ends' c ⊆ ends x ∪ Z) ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ X.map Function.Embedding.inl)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ C * D) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          (𝒲.filter fun W => S ⊆ W.biUnion ends').card ≤ C * D) := by
  classical
  obtain ⟨Ccl, hCcl, hcl⟩ := multiCliqueEmbedding r (roundAux q r) r
  set C₀ := (fakeCount q r + 1) * q.choose r + 2 with hC₀
  refine ⟨C₀ + 2 * Ccl + 1, by omega, ?_⟩
  intro n E _ ends X Z D hXr hZ hXJ
  have j₀ : Fin (fakeCount q r) := ⟨0, one_le_fakeCount hr hrq⟩
  obtain ⟨Φ, hvalid, hrange, hpdeg, hdeg⟩ := hcl n X ends (roundTemplate q r ends j₀) Z D
    (fun i hi => roundTemplate_wf (hXr i hi)) (le_trans (by omega) hZ)
    (fun J hJ => hXJ J hJ)
  have hA := antiEdgeStep (V := Fin n) (ends := ends) hrq j₀ X hXr
  set ψ := psiV (q := q) (r := r) Φ
  have hYR : stepY q r ends X ⊆ X.map Function.Embedding.inl ∪ stepR q r ends j₀ X := by
    intro c hc
    refine mem_union_right _ ?_
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hc
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact mem_stepR_iff'.2 ⟨f, rfl, i, hi, mem_union_right _ hfi⟩
  have hinj : ∀ c ∈ X.map Function.Embedding.inl ∪ stepR q r ends j₀ X,
      Set.InjOn ψ (sends q r ends c) := by
    intro c hc
    rcases c with i | f
    · intro x hx y hy hxy
      obtain ⟨v, -, rfl⟩ := mem_map.1 (mem_coe.1 hx)
      obtain ⟨w, -, rfl⟩ := mem_map.1 (mem_coe.1 hy)
      simpa [ψ, psiV] using hxy
    · rcases mem_union.1 hc with hc | hc
      · simp at hc
      · obtain ⟨f', hf', i, hi, hfi⟩ := mem_stepR_iff'.1 hc
        cases hf'
        exact psiV_injOn_edge (hvalid i hi) hfi
  have hinjX : Set.InjOn ψ ((X.map Function.Embedding.inl).biUnion (sends q r ends)) := by
    intro x hx y hy hxy
    obtain ⟨c, hc, hxc⟩ := mem_biUnion.1 (mem_coe.1 hx)
    obtain ⟨c', hc', hyc'⟩ := mem_biUnion.1 (mem_coe.1 hy)
    obtain ⟨i, -, rfl⟩ := mem_map.1 hc
    obtain ⟨i', -, rfl⟩ := mem_map.1 hc'
    obtain ⟨v, -, rfl⟩ := mem_map.1 hxc
    obtain ⟨w, -, rfl⟩ := mem_map.1 hyc'
    simpa [ψ, psiV] using hxy
  have hB := residual_mapEnds hA ψ hinj hinjX hYR
  set ends' := mapEnds ψ (sends q r ends) with hends'
  have hends'_inl : ∀ x, ends' (Sum.inl x) = ends x := fun x => image_liftE_psiV' ends Φ x
  have hends'_inr : ∀ f, ends' (Sum.inr f) = f.image ψ := fun f => rfl
  have hYsub : stepY q r ends X ⊆ stepR q r ends j₀ X := by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hc
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact mem_stepR_iff'.2 ⟨f, rfl, i, hi, mem_union_right _ hfi⟩
  have hsubpv : ∀ i ∈ X, ∀ f ∈ Ed q r ends j₀ i, f.image ψ ⊆ ends i ∪ auxImage (Φ i) := by
    intro i hi f hf
    rw [← placeEdge_image_betaV hf]
    exact placeEdge_subset (roundTemplate_wf (ends := ends) (j₀ := j₀) (hXr i hi)) (Φ i)
      (mem_image_of_mem _ hf)
  have hpieceV : ∀ i ∈ X, ∀ W₀, (W₀ = pieceP q r ends j₀ i ∨ W₀ = pieceQ q r ends j₀ i) →
      W₀.biUnion ends' ⊆ ends i ∪ auxImage (Φ i) := by
    intro i hi W₀ hW₀ v hv
    obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
    rcases c with i' | f
    · have : i' = i := by
        rcases hW₀ with rfl | rfl
        · exact mem_pieceP_inl.1 hc
        · exact absurd hc not_mem_pieceQ_inl
      subst this
      rw [hends'_inl] at hvc
      exact mem_union_left _ hvc
    · have hf : f ∈ Ed q r ends j₀ i := by
        rcases hW₀ with rfl | rfl
        · exact mem_union_left _ (mem_pieceP_inr.1 hc)
        · exact mem_union.2 (mem_pieceQ_inr.1 hc)
      exact hsubpv i hi f hf hvc
  refine ⟨ends', stepR q r ends j₀ X, stepY q r ends X, stepW q r ends j₀ X, hends'_inl,
    hB.mono (by omega), hYsub, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc x hx
    subst hx
    obtain ⟨f, hf, -⟩ := mem_stepR_iff'.1 hc
    cases hf
  · intro c hc
    obtain ⟨f, rfl, i, hi, hf⟩ := mem_stepR_iff'.1 hc
    obtain ⟨p, hp⟩ := (roundTemplate_wf (ends := ends) (j₀ := j₀) (hXr i hi)).edge_aux
      (f.image betaV) (mem_image_of_mem _ hf)
    refine ⟨Φ i p, mem_inter.2 ⟨?_, hrange i hi p⟩⟩
    rw [hends'_inr, ← placeEdge_image_betaV hf]
    exact mem_image.2 ⟨Sum.inr p, hp, rfl⟩
  · intro c hc
    obtain ⟨f, rfl, i, hi, hf⟩ := mem_stepR_iff'.1 hc
    refine ⟨i, hi, (hsubpv i hi f hf).trans (union_subset_union subset_rfl ?_)⟩
    intro v hv
    obtain ⟨p, -, rfl⟩ := mem_image.1 hv
    exact hrange i hi p
  · intro W hW
    obtain ⟨i, hi, hWi⟩ : ∃ i ∈ X,
        W = pieceP q r ends j₀ i ∨ W = pieceQ q r ends j₀ i := by
      rcases mem_union.1 hW with h | h
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h; exact ⟨i, hi, Or.inl rfl⟩
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h; exact ⟨i, hi, Or.inr rfl⟩
    refine (card_le_card (t := {Sum.inl i}) fun x hx => ?_).trans (by simp)
    obtain ⟨hxW, hxX⟩ := mem_filter.1 hx
    obtain ⟨i', -, rfl⟩ := mem_map.1 hxX
    have : i' = i := by
      rcases hWi with rfl | rfl
      · exact mem_pieceP_inl.1 hxW
      · exact absurd hxW not_mem_pieceQ_inl
    subst this; exact mem_singleton_self _
  · intro S hS
    refine le_trans ?_ ((hdeg S hS).trans (Nat.mul_le_mul_right _ (by omega)))
    have hsub : (stepR q r ends j₀ X).filter (fun c => S ⊆ ends' c) ⊆
        X.biUnion fun i => ((Ed q r ends j₀ i).filter fun f => S ⊆ f.image ψ).map
          Function.Embedding.inr := by
      intro c hc
      obtain ⟨hcR, hSc⟩ := mem_filter.1 hc
      obtain ⟨f, rfl, i, hi, hf⟩ := mem_stepR_iff'.1 hcR
      exact mem_biUnion.2 ⟨i, hi, mem_map_of_mem _ (mem_filter.2 ⟨hf, hSc⟩)⟩
    calc mdeg ends' (stepR q r ends j₀ X) S ≤ _ := card_le_card hsub
      _ ≤ ∑ i ∈ X, (((Ed q r ends j₀ i).filter fun f => S ⊆ f.image ψ).map
            Function.Embedding.inr).card := card_biUnion_le
      _ = ∑ i ∈ X, ((newEdges (roundTemplate q r ends j₀ i) (Φ i)).filter
            fun e => S ⊆ e).card := by
          refine sum_congr rfl fun i hi => ?_
          rw [card_map, newEdges_roundTemplate, filter_image, card_image_of_injOn]
          exact (psiV_image_injOn (hXr i hi) (hvalid i hi)).mono (by
            intro f hf; exact mem_coe.2 (mem_filter.1 (mem_coe.1 hf)).1)
  · intro S hS
    set Xs := X.filter fun p => S ⊆ ends p ∪ auxImage (Φ p)
    have hsub : (stepW q r ends j₀ X).filter (fun W => S ⊆ W.biUnion ends') ⊆
        Xs.image (pieceP q r ends j₀) ∪ Xs.image (pieceQ q r ends j₀) := by
      intro W hW
      obtain ⟨hW, hSW⟩ := mem_filter.1 hW
      rcases mem_union.1 hW with h | h
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        have hS' : S ⊆ ends i ∪ auxImage (Φ i) := hSW.trans (hpieceV i hi _ (Or.inl rfl))
        exact mem_union_left _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hS'⟩, rfl⟩)
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        have hS' : S ⊆ ends i ∪ auxImage (Φ i) := hSW.trans (hpieceV i hi _ (Or.inr rfl))
        exact mem_union_right _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hS'⟩, rfl⟩)
    have hXs : Xs.card ≤ Ccl * D := hpdeg S hS
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ Xs.card + Xs.card := Nat.add_le_add card_image_le card_image_le
      _ ≤ (C₀ + 2 * Ccl + 1) * D := by nlinarith

end RefinedAbsorption.RefineDown.Gen
