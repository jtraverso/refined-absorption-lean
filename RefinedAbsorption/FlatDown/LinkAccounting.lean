module
public import RefinedAbsorption.FlatDown.FlatDegree

/-!
# Bookkeeping for the link refiners of a flat step

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

* `IsResidualMultiRefiner.filter_nonempty`, `LinkRefiners.filter_nonempty`: empty pieces can be
  removed from a (residual) refiner, so link pieces may be assumed nonempty.
* `linkSum_le`: the degree of a set `S` in the lifted link refiners of a flat step is at most the
  sum, over the outside parts `T ⊇ S \ Z`, of the degree of `S ∩ Z` in the link refiner of `T`.
* `flatRoots_count_le`: the number of lifted pieces `(T, W)` whose vertex set `T ∪ V(W)` contains
  a set `J` is at most the sum, over the outside parts `T ⊇ J \ Z`, of the number of pieces of the
  link refiner of `T` whose vertex set contains `J ∩ Z`.

These reduce the degree and density hypotheses of the placed flat step
(`Placement.placedFlatStep`) to degree and piece-degree bounds of the individual link refiners.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner

section Nonempty

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

theorem sup_filter_nonempty (𝒰 : Finset (Finset E)) :
    (𝒰.filter Finset.Nonempty).sup id = 𝒰.sup id := by
  ext c
  simp only [mem_sup, mem_filter, id]
  constructor
  · rintro ⟨W, ⟨hW, -⟩, hc⟩; exact ⟨W, hW, hc⟩
  · rintro ⟨W, hW, hc⟩; exact ⟨W, ⟨hW, ⟨c, hc⟩⟩, hc⟩

/-- Empty pieces can be removed from a residual refiner. -/
theorem _root_.RefinedAbsorption.MultiRefiner.IsResidualMultiRefiner.filter_nonempty {q r C : ℕ} {ends : E → Finset V}
    {X R Y : Finset E} {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) :
    IsResidualMultiRefiner q r C ends X R Y (𝒲.filter Finset.Nonempty) := by
  refine ⟨h.rgraph, h.disjoint, fun W hW => h.divisible W (mem_filter.1 hW).1,
    fun W hW => h.subset W (mem_filter.1 hW).1, fun W hW => h.card_le W (mem_filter.1 hW).1,
    fun i hi => le_trans (card_le_card ?_) (h.mult_le i hi), fun L hL hdiv => ?_⟩
  · intro W hW
    simp only [mem_filter] at hW ⊢
    exact ⟨hW.1.1, hW.2⟩
  · obtain ⟨𝒰, h𝒰, Res, hRes, hRd, hpw, hd, heq⟩ := h.decomp L hL hdiv
    refine ⟨𝒰.filter Finset.Nonempty, filter_subset_filter _ h𝒰, Res, hRes, hRd,
      hpw.subset (fun W hW => (mem_filter.1 hW).1), ?_, ?_⟩
    · rw [sup_filter_nonempty]; exact hd
    · rw [sup_filter_nonempty]; exact heq

end Nonempty

section Link

variable {V E N : Type} [DecidableEq V] [DecidableEq E] [DecidableEq N]
  {ends : E → Finset V} {Z : Finset V} {endsN : Finset V → N → Finset V}

/-- Link pieces may be assumed nonempty. -/
theorem LinkRefiners.filter_nonempty {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲) :
    LinkRefiners q r i Cl ends Z X endsN RN fun T => (𝒲 T).filter Finset.Nonempty :=
  ⟨fun T hT => (hL.ref T hT).filter_nonempty, hL.inZ⟩

/-- Restricting the pieces restricts the lifted pieces. -/
theorem fI_mono {i : ℕ} {X : Finset E} {𝒲 𝒲' : Finset V → Finset (Finset (E ⊕ N))}
    (h : ∀ T, 𝒲' T ⊆ 𝒲 T) : fI ends Z i X 𝒲' ⊆ fI ends Z i X 𝒲 := by
  intro t ht
  obtain ⟨hT, hW⟩ := mem_fI.1 ht
  exact mem_fI.2 ⟨hT, h _ hW⟩

/-- **Degrees in the lifted link refiners.**  A set `S` lies in the lifted copy `T ∪ endsN T y`
only if `S \ Z ⊆ T` and `S ∩ Z ⊆ endsN T y`. -/
theorem linkSum_le {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲)
    (S : Finset V) :
    ∑ T ∈ outParts ends Z i X, ((RN T).filter fun y => S ⊆ T ∪ endsN T y).card ≤
      ∑ T ∈ (outParts ends Z i X).filter (fun T => S \ Z ⊆ T),
        ((RN T).filter fun y => S ∩ Z ⊆ endsN T y).card := by
  rw [sum_filter]
  refine sum_le_sum fun T hT => ?_
  have hTZ := (outParts_card hT).2
  split_ifs with hST
  · refine card_le_card fun y hy => ?_
    obtain ⟨hy, hS⟩ := mem_filter.1 hy
    refine mem_filter.2 ⟨hy, fun v hv => ?_⟩
    obtain ⟨hvS, hvZ⟩ := mem_inter.1 hv
    rcases mem_union.1 (hS hvS) with h | h
    · exact absurd hvZ (disjoint_left.1 hTZ h)
    · exact h
  · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun y hy hS => hST ?_))
    intro v hv
    obtain ⟨hvS, hvZ⟩ := mem_sdiff.1 hv
    rcases mem_union.1 (hS hvS) with h | h
    · exact h
    · exact absurd (hL.inZ T hT y hy h) hvZ

/-- **Density of the lifted pieces.**  A set `J` lies in the vertex set `T ∪ V(W)` of a lifted
piece only if `J \ Z ⊆ T` and `J ∩ Z ⊆ V(W)`. -/
theorem flatRoots_count_le {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲)
    (J : Finset V) :
    ((fI ends Z i X 𝒲).filter fun t => J ⊆ t.1 ∪ t.2.biUnion (lE ends Z endsN t.1)).card ≤
      ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
        ((𝒲 T).filter fun W => J ∩ Z ⊆ W.biUnion (lE ends Z endsN T)).card := by
  have hsub : ((fI ends Z i X 𝒲).filter fun t => J ⊆ t.1 ∪ t.2.biUnion (lE ends Z endsN t.1)) ⊆
      ((outParts ends Z i X).filter (fun T => J \ Z ⊆ T)).biUnion fun T =>
        ((𝒲 T).filter fun W => J ∩ Z ⊆ W.biUnion (lE ends Z endsN T)).image fun W => (T, W) := by
    intro t ht
    obtain ⟨ht, hJ⟩ := mem_filter.1 ht
    obtain ⟨hT, hW⟩ := mem_fI.1 ht
    have hTZ := (outParts_card hT).2
    have hp := link_piece_props hL hT hW
    have hVZ : t.2.biUnion (lE ends Z endsN t.1) ⊆ Z := biUnion_subset.2 fun w hw => (hp w hw).2.1
    refine mem_biUnion.2 ⟨t.1, mem_filter.2 ⟨hT, fun v hv => ?_⟩,
      mem_image.2 ⟨t.2, mem_filter.2 ⟨hW, fun v hv => ?_⟩, rfl⟩⟩
    · obtain ⟨hvJ, hvZ⟩ := mem_sdiff.1 hv
      rcases mem_union.1 (hJ hvJ) with h | h
      · exact h
      · exact absurd (hVZ h) hvZ
    · obtain ⟨hvJ, hvZ⟩ := mem_inter.1 hv
      rcases mem_union.1 (hJ hvJ) with h | h
      · exact absurd hvZ (disjoint_left.1 hTZ h)
      · exact h
  exact (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun T _ => card_image_le))

end Link

end RefinedAbsorption.FlatDown
