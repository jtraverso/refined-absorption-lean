module
public import RequestProject.RefineDown.Round
public import RequestProject.Placement.ReserveLemma52

/-!
# One refine-down round into a reserve

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855.  Lean formalization: Juan Pablo
Traverso Gianini, Apache-2.0.

`placedReserveRound` is the reserve version of `placedRound`: the anti-edge step
(`RefineDown.antiEdgeStep`) with all new vertices placed inside a prescribed reserve `Z ⊆ Fin n`
by the Partial Clique Embedding Lemma inside a reserve (`reserveCliqueEmbedding`).  Every new
copy, and hence every copy of the residue, contains a vertex of `Z`.  This is the first step of
the refine-down construction: it makes the residue `(r-1)`-flat with respect to the reserve.
The degree budget is relative to `|Z|`: the copies of `X` must not be too dense compared to `Z`.
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

variable {n q r : ℕ}

set_option maxHeartbeats 1000000 in
/-- **One refine-down round into a reserve.**  For `1 ≤ r < q` there is `C ≥ 1` such that the
following holds for every reserve `Z ⊆ Fin n`.  Let `X` be a labelled `r`-multigraph on `Fin n`
(tags `≤ k`) whose copies are not too dense compared to `Z`: every `j`-set (`j ≤ r - 1`) lies in
at most `D · |Z|^(r-1-j)` copies.  Let `G` be a forbidden host with `C · Δ_{r-1}(G) ≤ |Z|`, and
assume `C · D ≤ |Z|`.  Then the anti-edge round of `X`, with all new vertices placed inside `Z`,
satisfies `RoundSpec` with budget `D`, and every new copy meets `Z`; in particular the residue
is `(r-1)`-flat with respect to `Z` (every copy has at most `r - 1` vertices outside `Z`). -/
theorem placedReserveRound {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n k : ℕ) (X : Finset (Lab n)) (G : Finset (Finset (Fin n)))
      (Z : Finset (Fin n)) (D : ℕ),
      (∀ c ∈ X, c.1 ≤ k) → MIsRGraph r labEnds X →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 → mdeg labEnds X J ≤ D * Z.card ^ (r - 1 - J.card)) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ Z.card) → C * D ≤ Z.card →
      0 < Z.card →
      ∃ (R Y : Finset (Lab n)) (𝒲 : Finset (Finset (Lab n))), RoundSpec q r C k X G D R Y 𝒲 ∧
        ∀ c ∈ R, (c.2 ∩ Z).Nonempty := by
  classical
  obtain ⟨Ccl, hCcl, hcl⟩ := reserveCliqueEmbedding r (roundAux q r) r
  set C₀ := (fakeCount q r + 1) * q.choose r + 2 with hC₀
  refine ⟨C₀ + 2 * Ccl + 1, by omega, ?_⟩
  intro n k X G Z D hXk hXr hXJ hG hD hZ
  have j₀ : Fin (fakeCount q r) := ⟨0, one_le_fakeCount hr hrq⟩
  -- placement of the round gadgets inside the reserve
  obtain ⟨Φ, hvalid, hrange, hdisj, hhost, hdeg, hpdeg⟩ := hcl n X (fun i => i.2)
    (roundTemplate q r j₀) G Z D
    (fun i hi => roundTemplate_wf (hXr i hi))
    (fun S hS => le_trans (Nat.mul_le_mul_right _ (by omega)) (hG S hS))
    (le_trans (Nat.mul_le_mul_right _ (by omega)) hD)
    (fun J hJ => hXJ J hJ) hZ
  -- the abstract step
  have hA := antiEdgeStep (V := Fin n) (ends := labEnds) hrq j₀ X hXr
  set ψ := psiV (q := q) (r := r) Φ
  have hYR : stepY q r labEnds X ⊆ X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X := by
    intro c hc
    refine mem_union_right _ ?_
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hc
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact mem_stepR_iff.2 ⟨f, rfl, i, hi, mem_union_right _ hfi⟩
  have hinj : ∀ c ∈ X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X,
      Set.InjOn ψ (sends q r labEnds c) := by
    intro c hc
    rcases c with i | f
    · intro x hx y hy hxy
      obtain ⟨v, -, rfl⟩ := mem_map.1 (mem_coe.1 hx)
      obtain ⟨w, -, rfl⟩ := mem_map.1 (mem_coe.1 hy)
      simpa [ψ, psiV] using hxy
    · rcases mem_union.1 hc with hc | hc
      · simp at hc
      · obtain ⟨f', hf', i, hi, hfi⟩ := mem_stepR_iff.1 hc
        cases hf'
        exact psiV_injOn_edge (hvalid i hi) hfi
  have hinjX : Set.InjOn ψ ((X.map Function.Embedding.inl).biUnion (sends q r labEnds)) := by
    intro x hx y hy hxy
    obtain ⟨c, hc, hxc⟩ := mem_biUnion.1 (mem_coe.1 hx)
    obtain ⟨c', hc', hyc'⟩ := mem_biUnion.1 (mem_coe.1 hy)
    obtain ⟨i, -, rfl⟩ := mem_map.1 hc
    obtain ⟨i', -, rfl⟩ := mem_map.1 hc'
    obtain ⟨v, -, rfl⟩ := mem_map.1 hxc
    obtain ⟨w, -, rfl⟩ := mem_map.1 hyc'
    simpa [ψ, psiV] using hxy
  have hB := residual_mapEnds hA ψ hinj hinjX hYR
  -- renaming the copies
  have hnewE : ∀ i ∈ X, ∀ f ∈ Ed q r j₀ i, f.image ψ ∈ newEdges (roundTemplate q r j₀ i) (Φ i) := by
    intro i _ f hf
    rw [newEdges_roundTemplate]
    exact mem_image_of_mem _ hf
  let g : SC (Fin n) (Lab n) q r → Lab n :=
    Sum.elim (fun i => i) (fun f => ((k + 1 : ℕ), f.image ψ))
  have hends : ∀ c ∈ X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X,
      labEnds (g c) = mapEnds ψ (sends q r labEnds) c := by
    intro c _
    rcases c with i | f
    · exact (image_liftE_psiV Φ i).symm
    · rfl
  have hg : Set.InjOn g ↑(X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X) := by
    intro c hc c' hc' hcc'
    have hc := mem_coe.1 hc
    have hc' := mem_coe.1 hc'
    rcases c with i | f <;> rcases c' with i' | f'
    · simpa [g] using hcc'
    · exfalso
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨i₀, hi₀, he⟩ := mem_map.1 hc
        have hii : i₀ = _ := Sum.inl_injective he
        rw [hii] at hi₀
        have := hXk _ hi₀
        have h1 := congrArg Prod.fst hcc'
        simp only [g, Sum.elim_inl, Sum.elim_inr] at h1
        omega
      · obtain ⟨_, he, -⟩ := mem_stepR_iff.1 hc; cases he
    · exfalso
      rcases mem_union.1 hc' with hc' | hc'
      · obtain ⟨i₀, hi₀, he⟩ := mem_map.1 hc'
        have hii : i₀ = _ := Sum.inl_injective he
        rw [hii] at hi₀
        have := hXk _ hi₀
        have h1 := congrArg Prod.fst hcc'
        simp only [g, Sum.elim_inl, Sum.elim_inr] at h1
        omega
      · obtain ⟨_, he, -⟩ := mem_stepR_iff.1 hc'; cases he
    · have hc := (mem_union.1 hc).resolve_left (by simp)
      have hc' := (mem_union.1 hc').resolve_left (by simp)
      obtain ⟨_, he, i, hi, hfi⟩ := mem_stepR_iff.1 hc; cases he
      obtain ⟨_, he', i', hi', hfi'⟩ := mem_stepR_iff.1 hc'; cases he'
      have himg : f.image ψ = f'.image ψ := congrArg Prod.snd hcc'
      by_cases hii : i = i'
      · subst hii
        rw [psiV_image_injOn (hXr i hi) (hvalid i hi) hfi hfi' himg]
      · exfalso
        exact disjoint_left.1 (hdisj i hi i' hi' hii) (hnewE i hi f hfi)
          (himg ▸ hnewE i' hi' f' hfi')
  have hC := residual_relabel hB g labEnds hends hg hYR
  have hXg : (X.map Function.Embedding.inl).image g = X := by
    ext c
    constructor
    · intro hc
      obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hc'
      exact hi
    · intro hc
      exact mem_image.2 ⟨Sum.inl c, mem_map_of_mem _ hc, rfl⟩
  rw [hXg] at hC
  have hYsub : stepY q r labEnds X ⊆ stepR q r labEnds j₀ X := by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hc
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact mem_stepR_iff.2 ⟨f, rfl, i, hi, mem_union_right _ hfi⟩
  have hRg : ∀ c ∈ (stepR q r labEnds j₀ X).image g,
      ∃ i ∈ X, ∃ f ∈ Ed q r j₀ i, c = ((k + 1 : ℕ), f.image ψ) := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
    obtain ⟨f, rfl, i, hi, hfi⟩ := mem_stepR_iff.1 hc'
    exact ⟨i, hi, f, hfi, rfl⟩
  have hsubpv : ∀ i ∈ X, ∀ f ∈ Ed q r j₀ i, f.image ψ ⊆ i.2 ∪ auxImage (Φ i) := by
    intro i hi f hf
    rw [← placeEdge_image_betaV hf]
    exact placeEdge_subset (roundTemplate_wf (j₀ := j₀) (hXr i hi)) (Φ i)
      (mem_image_of_mem _ hf)
  have hpieceV : ∀ i ∈ X, ∀ W₀, (W₀ = pieceP q r labEnds j₀ i ∨ W₀ = pieceQ q r labEnds j₀ i) →
      (W₀.image g).biUnion labEnds ⊆ i.2 ∪ auxImage (Φ i) := by
    intro i hi W₀ hW₀ v hv
    obtain ⟨x, hx, hvx⟩ := mem_biUnion.1 hv
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    rcases c with i' | f
    · have : i' = i := by
        rcases hW₀ with rfl | rfl
        · exact mem_pieceP_inl.1 hc
        · exact absurd hc not_mem_pieceQ_inl
      subst this
      exact mem_union_left _ hvx
    · have hf : f ∈ Ed q r j₀ i := by
        rcases hW₀ with rfl | rfl
        · exact mem_union_left _ (mem_pieceP_inr.1 hc)
        · exact mem_union.2 (mem_pieceQ_inr.1 hc)
      exact hsubpv i hi f hf hvx
  refine ⟨(stepR q r labEnds j₀ X).image g, (stepY q r labEnds X).image g,
    (stepW q r labEnds j₀ X).image (image g),
    ⟨hC.mono (by omega), image_subset_image hYsub, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    obtain ⟨i, -, f, -, rfl⟩ := hRg c hc
    rfl
  · intro c hc c' hc' hcc'
    obtain ⟨i, -, f, -, rfl⟩ := hRg c (mem_coe.1 hc)
    obtain ⟨i', -, f', -, rfl⟩ := hRg c' (mem_coe.1 hc')
    exact Prod.ext rfl hcc'
  · intro c hc
    obtain ⟨i, hi, f, hf, rfl⟩ := hRg c hc
    exact fun hG' => disjoint_left.1 (hhost i hi) (hnewE i hi f hf) hG'
  · intro W hW
    obtain ⟨W₀, hW₀, rfl⟩ := mem_image.1 hW
    obtain ⟨i, hi, hW₀i⟩ : ∃ i ∈ X,
        W₀ = pieceP q r labEnds j₀ i ∨ W₀ = pieceQ q r labEnds j₀ i := by
      rcases mem_union.1 hW₀ with h | h
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h; exact ⟨i, hi, Or.inl rfl⟩
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h; exact ⟨i, hi, Or.inr rfl⟩
    refine (card_le_card (t := {i}) fun x hx => ?_).trans (by simp)
    obtain ⟨hxW, hxX⟩ := mem_filter.1 hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hxW
    rcases c with i' | f
    · have : i' = i := by
        rcases hW₀i with rfl | rfl
        · exact mem_pieceP_inl.1 hc
        · exact absurd hc not_mem_pieceQ_inl
      subst this; exact mem_singleton_self _
    · exfalso
      have := hXk _ hxX
      simp [g] at this
  · intro S hS
    refine le_trans ?_ ((hdeg S hS).trans (Nat.mul_le_mul_right _ (by omega)))
    unfold mdeg deg
    refine card_le_card_of_injOn Prod.snd (fun c hc => ?_) (fun c hc c' hc' hcc' => ?_)
    · obtain ⟨hcR, hSc⟩ := mem_filter.1 (mem_coe.1 hc)
      obtain ⟨i, hi, f, hf, rfl⟩ := hRg c hcR
      exact mem_coe.2 (mem_filter.2 ⟨mem_biUnion.2 ⟨i, hi, hnewE i hi f hf⟩, hSc⟩)
    · obtain ⟨i, -, f, -, rfl⟩ := hRg c (mem_filter.1 (mem_coe.1 hc)).1
      obtain ⟨i', -, f', -, rfl⟩ := hRg c' (mem_filter.1 (mem_coe.1 hc')).1
      exact Prod.ext rfl hcc'
  · intro S hS
    set Xs := X.filter fun p => S ⊆ p.2 ∪ auxImage (Φ p)
    have hsub : ((stepW q r labEnds j₀ X).image (image g)).filter
        (fun W => S ⊆ W.biUnion labEnds) ⊆
        Xs.image (fun i => (pieceP q r labEnds j₀ i).image g) ∪
          Xs.image (fun i => (pieceQ q r labEnds j₀ i).image g) := by
      intro W hW
      obtain ⟨hW, hSW⟩ := mem_filter.1 hW
      obtain ⟨W₀, hW₀, rfl⟩ := mem_image.1 hW
      rcases mem_union.1 hW₀ with h | h
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        have hS' : S ⊆ i.2 ∪ auxImage (Φ i) := hSW.trans (hpieceV i hi _ (Or.inl rfl))
        exact mem_union_left _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hS'⟩, rfl⟩)
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        have hS' : S ⊆ i.2 ∪ auxImage (Φ i) := hSW.trans (hpieceV i hi _ (Or.inr rfl))
        exact mem_union_right _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hS'⟩, rfl⟩)
    have hXs : Xs.card ≤ Ccl * D := hpdeg S hS
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ Xs.card + Xs.card := Nat.add_le_add card_image_le card_image_le
      _ ≤ (C₀ + 2 * Ccl + 1) * D := by nlinarith
  · intro c hc
    obtain ⟨i, hi, f, hf, rfl⟩ := hRg c hc
    obtain ⟨p, hp⟩ := (roundTemplate_wf (j₀ := j₀) (hXr i hi)).edge_aux (f.image betaV)
      (mem_image_of_mem _ hf)
    refine ⟨Φ i p, mem_inter.2 ⟨?_, hrange i hi p⟩⟩
    show Φ i p ∈ f.image ψ
    rw [← placeEdge_image_betaV hf]
    exact mem_image.2 ⟨Sum.inr p, hp, rfl⟩

end RefinedAbsorption.RefineDown
