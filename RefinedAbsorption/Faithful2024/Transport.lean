module
public import RefinedAbsorption.Faithful2024.Defs

/-!
# Transport of the Section 1 notions along injective maps of vertices

The theorems of the existing interface are stated on the vertex type `Fin n`.  The faithful
statements (`Theorem_1_7`, `Theorem_1_11` in `Faithful2024/Defs.lean`) allow an arbitrary vertex
type, with `n = |V(G)|`.  This file proves that every notion of Section 1 is invariant under an
injective relabelling `f : α ↪ β` of the vertices (`HGraph.map`), and that every hypergraph `G`
with `n` vertices is the image of a hypergraph on `Fin n` (`pullback_map`).
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset

section Transport

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β)

/-- The induced embedding on vertex sets. -/
abbrev mf : Finset α ↪ Finset β := (mapEmbedding f).toEmbedding

/-- The induced embedding on families of vertex sets. -/
abbrev mf2 : Finset (Finset α) ↪ Finset (Finset β) := (mapEmbedding (mf f)).toEmbedding

@[simp] theorem mf_apply (s : Finset α) : mf f s = s.map f := rfl

@[simp] theorem mf2_apply (F : Finset (Finset α)) : mf2 f F = F.map (mf f) := rfl

@[simp] theorem coe_mf : (mf f : Finset α → Finset β) = fun s => s.map f := by funext s; rfl

@[simp] theorem coe_mf2 : (mf2 f : Finset (Finset α) → Finset (Finset β)) = fun F => F.map (mf f) := by
  funext s; rfl

theorem deg_map (F : Finset (Finset α)) (S : Finset α) :
    deg (F.map (mf f)) (S.map f) = deg F S := by
  unfold deg
  rw [filter_map, card_map]
  congr 1
  apply filter_congr
  intro e _
  exact map_subset_map

theorem deg_map_of_not_range (F : Finset (Finset α)) (S : Finset β)
    (h : ∀ T : Finset α, S ≠ T.map f) : deg (F.map (mf f)) S = 0 := by
  unfold deg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hS
  obtain ⟨e', -, rfl⟩ := mem_map.1 he
  obtain ⟨u, -, rfl⟩ := subset_map_iff.1 hS
  exact h u rfl

theorem isDivisible_map_iff {q r : ℕ} (F : Finset (Finset α)) :
    IsDivisible q r (F.map (mf f)) ↔ IsDivisible q r F := by
  constructor
  · intro h S hS
    have := h (S.map f) (by simpa using hS)
    simpa [deg_map] using this
  · intro h S hS
    by_cases hr : ∃ T : Finset α, S = T.map f
    · obtain ⟨T, rfl⟩ := hr
      rw [deg_map]
      simpa using h T (by simpa using hS)
    · push_neg at hr
      rw [deg_map_of_not_range f F S hr]
      exact dvd_zero _

theorem vertexSet_map (F : Finset (Finset α)) :
    vertexSet (F.map (mf f)) = (vertexSet F).map f := by
  ext b
  simp only [vertexSet, mem_sup, mem_map, id, mf_apply]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hb⟩
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hb
    exact ⟨a, ⟨e, he, ha⟩, rfl⟩
  · rintro ⟨a, ⟨e, he, ha⟩, rfl⟩
    exact ⟨e.map f, ⟨e, he, rfl⟩, mem_map_of_mem f ha⟩

theorem cliqueEdges_map (r : ℕ) (Q : Finset α) :
    cliqueEdges r (Q.map f) = (cliqueEdges r Q).map (mf f) :=
  powersetCard_map f r Q

theorem map_mem_map_iff {s : Finset α} {F : Finset (Finset α)} :
    s.map f ∈ F.map (mf f) ↔ s ∈ F :=
  mem_map' (mf f)

/-- Relabel the vertices of a hypergraph. -/
def HGraph.map (G : HGraph α) : HGraph β := ⟨G.verts.map f, G.edges.map (mf f)⟩

@[simp] theorem HGraph.map_verts (G : HGraph α) : (G.map f).verts = G.verts.map f := rfl
@[simp] theorem HGraph.map_edges (G : HGraph α) : (G.map f).edges = G.edges.map (mf f) := rfl

theorem HGraph.wf_map {G : HGraph α} (h : G.WF) : (G.map f).WF := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_map.1 he
  exact map_subset_map.2 (h e' he')

theorem HGraph.isUniform_map_iff {r : ℕ} (G : HGraph α) : (G.map f).IsUniform r ↔ G.IsUniform r := by
  constructor
  · intro h e he
    have := h (e.map f) (mem_map_of_mem _ he)
    simpa using this
  · intro h e he
    obtain ⟨e', he', rfl⟩ := mem_map.1 he
    simpa using h e' he'

theorem HGraph.minDegGE_map_iff {r : ℕ} (G : HGraph α) (D : ℝ) :
    (G.map f).MinDegGE r D ↔ G.MinDegGE r D := by
  constructor
  · intro h S hS hc
    have := h (S.map f) (map_subset_map.2 hS) (by simpa using hc)
    simpa [deg_map] using this
  · intro h S hS hc
    obtain ⟨T, hT, rfl⟩ := subset_map_iff.1 hS
    rw [map_edges, deg_map]
    exact h T hT (by simpa using hc)

theorem HGraph.maxDeg_map (r : ℕ) (G : HGraph α) : (G.map f).maxDeg r = G.maxDeg r := by
  unfold HGraph.maxDeg
  rw [map_verts, powersetCard_map, sup_map]
  congr 1
  funext S
  simp only [Function.comp, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  exact deg_map f _ _

theorem HGraph.isSubgraph_map {H G : HGraph α} (h : H.IsSubgraph G) :
    (H.map f).IsSubgraph (G.map f) :=
  ⟨map_subset_map.2 h.1, map_subset_map.2 h.2⟩

theorem HGraph.isSpanningSubgraph_map_iff (X G : HGraph α) :
    (X.map f).IsSpanningSubgraph (G.map f) ↔ X.IsSpanningSubgraph G := by
  unfold HGraph.IsSpanningSubgraph
  simp only [map_verts, map_edges, map_inj, map_subset_map]

/-- Pulling a sub-family of `X.map f` back to `X`. -/
def pullFam (F : Finset (Finset α)) (L : Finset (Finset β)) : Finset (Finset α) :=
  F.filter fun e => e.map f ∈ L

theorem pullFam_map {F : Finset (Finset α)} {L : Finset (Finset β)} (hL : L ⊆ F.map (mf f)) :
    (pullFam f F L).map (mf f) = L := by
  ext e
  simp only [pullFam, mem_map, mem_filter, mf_apply]
  constructor
  · rintro ⟨e', ⟨-, he'⟩, rfl⟩; exact he'
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_map.1 (hL he)
    exact ⟨e', ⟨he', he⟩, rfl⟩

theorem pullFam_subset (F : Finset (Finset α)) (L : Finset (Finset β)) : pullFam f F L ⊆ F :=
  filter_subset _ _

theorem isCliqueDecomposition_map {q r : ℕ} {G : Finset (Finset α)} {𝒟 : Finset (Finset α)}
    (h : IsCliqueDecomposition q r G 𝒟) :
    IsCliqueDecomposition q r (G.map (mf f)) (𝒟.map (mf f)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨Q', hQ', rfl⟩ := mem_map.1 hQ
    simpa using h1 Q' hQ'
  · intro Q₁ hQ₁ Q₂ hQ₂ hne
    obtain ⟨Q₁', hQ₁', rfl⟩ := mem_map.1 hQ₁
    obtain ⟨Q₂', hQ₂', rfl⟩ := mem_map.1 hQ₂
    have hne' : Q₁' ≠ Q₂' := fun h => hne (by rw [h])
    simp only [mf_apply, cliqueEdges_map]
    exact (disjoint_map _).2 (h2 Q₁' hQ₁' Q₂' hQ₂' hne')
  · rw [← h3]
    ext e
    constructor
    · intro he
      obtain ⟨Q₀, hQ₀, he⟩ := mem_biUnion.1 he
      obtain ⟨Q, hQ, rfl⟩ := mem_map.1 hQ₀
      rw [mf_apply, cliqueEdges_map] at he
      obtain ⟨e', he', rfl⟩ := mem_map.1 he
      exact mem_map_of_mem _ (mem_biUnion.2 ⟨Q, hQ, he'⟩)
    · intro he
      obtain ⟨e', he', rfl⟩ := mem_map.1 he
      obtain ⟨Q, hQ, he'⟩ := mem_biUnion.1 he'
      refine mem_biUnion.2 ⟨Q.map f, mem_map_of_mem (mf f) hQ, ?_⟩
      rw [cliqueEdges_map]
      exact mem_map_of_mem _ he'

theorem isOmniAbsorber_map {q r : ℕ} {X A : HGraph α} {𝓗 : Finset (Finset α)}
    {QA : Finset (Finset α) → Finset (Finset α)} (h : IsOmniAbsorber q r X A 𝓗 QA) :
    IsOmniAbsorber q r (X.map f) (A.map f) (𝓗.map (mf f))
      (fun L => (QA (pullFam f X.edges L)).map (mf f)) := by
  refine ⟨HGraph.wf_map f h.wfX, HGraph.wf_map f h.wfA, by simp [h.verts_eq], ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (disjoint_map (mf f)).2 h.disjoint
  · intro Q hQ
    obtain ⟨Q', hQ', rfl⟩ := mem_map.1 hQ
    obtain ⟨hc, hs⟩ := h.family Q' hQ'
    refine ⟨by simpa using hc, ?_⟩
    simp only [mf_apply, cliqueEdges_map, HGraph.map_edges, ← map_union]
    exact map_subset_map.2 hs
  · intro Q hQ
    obtain ⟨Q', hQ', rfl⟩ := mem_map.1 hQ
    simp only [mf_apply, cliqueEdges_map, HGraph.map_edges, filter_map]
    rw [card_map]
    refine le_trans (le_of_eq ?_) (h.oneX Q' hQ')
    congr 1
    apply filter_congr
    intro e _
    simp [Function.comp, map_mem_map_iff]
  · intro L hL hdiv
    have hL' := pullFam_map f hL
    have hdiv' : IsDivisible q r (pullFam f X.edges L) := by
      rw [← isDivisible_map_iff f, hL']; exact hdiv
    exact map_subset_map.2 (h.sub _ (pullFam_subset f _ _) hdiv')
  · intro L hL hdiv
    have hL' := pullFam_map f hL
    have hdiv' : IsDivisible q r (pullFam f X.edges L) := by
      rw [← isDivisible_map_iff f, hL']; exact hdiv
    have := isCliqueDecomposition_map f (h.decomp _ (pullFam_subset f _ _) hdiv')
    rwa [map_union, hL'] at this

theorem isCRefinedOmni_map {r C : ℕ} {X A : HGraph α} {𝓗 : Finset (Finset α)}
    (h : IsCRefinedOmni r C X A 𝓗) :
    IsCRefinedOmni r C (X.map f) (A.map f) (𝓗.map (mf f)) := by
  intro e he
  simp only [HGraph.map_edges, ← map_union] at he
  obtain ⟨e', he', rfl⟩ := mem_map.1 he
  rw [filter_map, card_map]
  refine le_trans (le_of_eq ?_) (h e' he')
  congr 1
  apply filter_congr
  intro Q _
  simp [Function.comp, cliqueEdges_map, map_mem_map_iff]

theorem isRefiner_map {q r : ℕ} {X R : HGraph α} {𝓗 : Finset (Finset (Finset α))}
    {QR : Finset (Finset α) → Finset (Finset (Finset α))} (h : IsRefiner q r X R 𝓗 QR) :
    IsRefiner q r (X.map f) (R.map f) (𝓗.map (mf2 f))
      (fun L => (QR (pullFam f X.edges L)).map (mf2 f)) := by
  refine ⟨(HGraph.isUniform_map_iff f X).2 h.unifX, (HGraph.isUniform_map_iff f R).2 h.unifR,
    by simp [h.verts_eq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (disjoint_map (mf f)).2 h.disjoint
  · intro H hH
    obtain ⟨H', hH', rfl⟩ := mem_map.1 hH
    obtain ⟨hs, hd⟩ := h.family H' hH'
    refine ⟨?_, (isDivisible_map_iff f H').2 hd⟩
    simp only [mf2_apply, HGraph.map_edges, ← map_union]
    exact map_subset_map.2 hs
  · intro H hH
    obtain ⟨H', hH', rfl⟩ := mem_map.1 hH
    change ((H'.map (mf f)).filter (fun e => e ∈ X.edges.map (mf f))).card ≤ 1
    rw [filter_map, card_map]
    refine le_trans (le_of_eq ?_) (h.oneX H' hH')
    congr 1
    apply filter_congr
    intro e _
    simp [Function.comp, map_mem_map_iff]
  · intro L hL hdiv
    have hL' := pullFam_map f hL
    have hdiv' : IsDivisible q r (pullFam f X.edges L) := by
      rw [← isDivisible_map_iff f, hL']; exact hdiv
    exact map_subset_map.2 (h.sub _ (pullFam_subset f _ _) hdiv')
  · intro L hL hdiv
    have hL' := pullFam_map f hL
    have hdiv' : IsDivisible q r (pullFam f X.edges L) := by
      rw [← isDivisible_map_iff f, hL']; exact hdiv
    have hp := h.pairwise _ (pullFam_subset f _ _) hdiv'
    intro H₁ hH₁ H₂ hH₂ hne
    obtain ⟨H₁', hH₁', rfl⟩ := mem_map.1 (mem_coe.1 hH₁)
    obtain ⟨H₂', hH₂', rfl⟩ := mem_map.1 (mem_coe.1 hH₂)
    have hne' : H₁' ≠ H₂' := fun h => hne (by rw [h])
    have := hp (mem_coe.2 hH₁') (mem_coe.2 hH₂') hne'
    simp only [Function.onFun, id, mf2_apply] at this ⊢
    exact (disjoint_map _).2 this
  · intro L hL hdiv
    have hL' := pullFam_map f hL
    have hdiv' : IsDivisible q r (pullFam f X.edges L) := by
      rw [← isDivisible_map_iff f, hL']; exact hdiv
    have hc := h.cover _ (pullFam_subset f _ _) hdiv'
    rw [sup_map]
    have e1 : (QR (pullFam f X.edges L)).sup (id ∘ ⇑(mf2 f)) =
        ((QR (pullFam f X.edges L)).sup id).map (mf f) := by
      ext e
      simp only [mem_sup, Function.comp, id, mf2_apply, mem_map]
      constructor
      · rintro ⟨H, hH, e', he', rfl⟩; exact ⟨e', ⟨H, hH, he'⟩, rfl⟩
      · rintro ⟨e', ⟨H, hH, he'⟩, rfl⟩; exact ⟨H, hH, e', he', rfl⟩
    rw [e1, hc, map_union, hL', HGraph.map_edges]

theorem isCRefinedFamily_map {C : ℕ} {G : Finset (Finset α)} {𝓗 : Finset (Finset (Finset α))}
    (h : IsCRefinedFamily C G 𝓗) : IsCRefinedFamily C (G.map (mf f)) (𝓗.map (mf2 f)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.1 he
    rw [filter_map, card_map]
    refine le_trans (le_of_eq ?_) (h.mult_le e' he')
    congr 1
    apply filter_congr
    intro H _
    simp [Function.comp, map_mem_map_iff]
  · intro H hH
    obtain ⟨H', hH', rfl⟩ := mem_map.1 hH
    simpa [vertexSet_map] using h.verts_le H' hH'
  · intro H hH
    obtain ⟨H', hH', rfl⟩ := mem_map.1 hH
    simpa using h.card_le H' hH'

theorem refDegree_map (r : ℕ) (R : HGraph α) (𝓗 : Finset (Finset (Finset α))) :
    refDegree r (R.map f) (𝓗.map (mf2 f)) = refDegree r R 𝓗 := by
  unfold refDegree
  rw [HGraph.map_verts, powersetCard_map, sup_map]
  congr 1
  funext S
  change ((𝓗.map (mf2 f)).filter (fun H => S.map f ⊆ vertexSet H)).card =
    (𝓗.filter (fun H => S ⊆ vertexSet H)).card
  rw [filter_map, card_map]
  congr 1
  apply filter_congr
  intro H _
  show map f S ⊆ vertexSet (H.map (mf f)) ↔ _
  rw [vertexSet_map]
  exact map_subset_map

end Transport

section Pullback

variable {α : Type*} [DecidableEq α]

/-- The canonical embedding `Fin |s| ↪ α` onto `s`. -/
noncomputable def finEmb (s : Finset α) : Fin s.card ↪ α :=
  ⟨fun i => (s.equivFin.symm i : α), fun i j h => s.equivFin.symm.injective (Subtype.ext h)⟩

theorem univ_map_finEmb (s : Finset α) : (univ : Finset (Fin s.card)).map (finEmb s) = s := by
  ext a
  simp only [mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
  · intro ha
    exact ⟨s.equivFin ⟨a, ha⟩, by
      change ((s.equivFin.symm (s.equivFin ⟨a, ha⟩)) : α) = a
      simp⟩

/-- The hypergraph on `Fin |s|` whose image under `finEmb s` is `G` (when `V(G) = s`). -/
noncomputable def pullback (s : Finset α) (G : HGraph α) : HGraph (Fin s.card) :=
  ⟨univ, univ.filter fun e => e.map (finEmb s) ∈ G.edges⟩

theorem pullback_map {s : Finset α} {G : HGraph α} (hwf : G.WF) (hs : G.verts = s) :
    (pullback s G).map (finEmb s) = G := by
  obtain ⟨V, E⟩ := G
  simp only [HGraph.map, pullback] at hs ⊢
  subst hs
  congr 1
  · exact univ_map_finEmb V
  · ext e
    simp only [mem_map, mem_filter, mem_univ, true_and, mf_apply]
    constructor
    · rintro ⟨e', he', rfl⟩; exact he'
    · intro he
      have hsub : e ⊆ (univ : Finset (Fin V.card)).map (finEmb V) := by
        rw [univ_map_finEmb]; exact hwf e he
      obtain ⟨u, -, rfl⟩ := subset_map_iff.1 hsub
      exact ⟨u, he, rfl⟩

theorem pullback_card (s : Finset α) (G : HGraph α) : (pullback s G).verts.card = s.card := by
  simp [pullback]

end Pullback

end RefinedAbsorption.Faithful2024
