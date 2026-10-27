module
public import RequestProject.OmniFromRefiner

/-!
# Transporting hypergraphs and decompositions along injective maps

Helper lemmas for the construction of absorbers: images of hypergraphs and clique families under
an injective vertex map, removal of several cliques from a decomposition, and unions of
decompositions over a finite index set.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- The image of a hypergraph (or clique family) under an injective vertex map. -/
def gmap (f : U ↪ V) (G : Finset (Finset U)) : Finset (Finset V) :=
  G.map (mapEmbedding f).toEmbedding

omit [DecidableEq U] [DecidableEq V] in
theorem mapEmb_apply (f : U ↪ V) (e : Finset U) : (mapEmbedding f) e = e.map f := rfl

omit [DecidableEq U] [DecidableEq V] in
theorem mapEmb_toEmb_apply (f : U ↪ V) (e : Finset U) :
    (mapEmbedding f).toEmbedding e = e.map f := rfl

omit [DecidableEq U] [DecidableEq V] in
theorem mem_gmap {f : U ↪ V} {G : Finset (Finset U)} {e : Finset V} :
    e ∈ gmap f G ↔ ∃ e₀ ∈ G, e₀.map f = e := by
  rw [gmap, mem_map]; rfl

omit [DecidableEq U] [DecidableEq V] in
theorem map_mem_gmap {f : U ↪ V} {G : Finset (Finset U)} {e : Finset U} :
    e.map f ∈ gmap f G ↔ e ∈ G := by
  rw [mem_gmap]
  constructor
  · rintro ⟨e₀, he₀, h⟩
    rwa [← map_injective f h]
  · intro h; exact ⟨e, h, rfl⟩

theorem gmap_union (f : U ↪ V) (G H : Finset (Finset U)) :
    gmap f (G ∪ H) = gmap f G ∪ gmap f H := by
  simp [gmap, map_union]

theorem gmap_sdiff (f : U ↪ V) (G H : Finset (Finset U)) :
    gmap f (G \ H) = gmap f G \ gmap f H := by
  simp [gmap, Finset.map_sdiff]

theorem gmap_erase (f : U ↪ V) (G : Finset (Finset U)) (e : Finset U) :
    gmap f (G.erase e) = (gmap f G).erase (e.map f) := by
  rw [gmap, gmap, map_erase]; rfl

omit [DecidableEq U] [DecidableEq V] in
theorem gmap_cliqueEdges (f : U ↪ V) (r : ℕ) (Q : Finset U) :
    gmap f (cliqueEdges r Q) = cliqueEdges r (Q.map f) := by
  simp [gmap, cliqueEdges, powersetCard_map, mapEmbedding]

omit [DecidableEq U] [DecidableEq V] in
theorem gmap_mono (f : U ↪ V) {G H : Finset (Finset U)} (h : G ⊆ H) : gmap f G ⊆ gmap f H :=
  map_subset_map.2 h

omit [DecidableEq U] [DecidableEq V] in
theorem disjoint_gmap (f : U ↪ V) {G H : Finset (Finset U)} :
    Disjoint (gmap f G) (gmap f H) ↔ Disjoint G H := by
  simp [gmap, disjoint_map]

omit [DecidableEq U] [DecidableEq V] in
theorem IsRGraph.gmap {r : ℕ} {G : Finset (Finset U)} (h : IsRGraph r G) (f : U ↪ V) :
    IsRGraph r (gmap f G) := by
  intro e he
  obtain ⟨e₀, he₀, rfl⟩ := mem_gmap.1 he
  rw [card_map]; exact h e₀ he₀

/-- Decompositions are transported along injective vertex maps. -/
theorem IsDecomposition.gmap {q r : ℕ} {G 𝒬 : Finset (Finset U)} (h : IsDecomposition q r G 𝒬)
    (f : U ↪ V) : IsDecomposition q r (RefinedAbsorption.gmap f G) (RefinedAbsorption.gmap f 𝒬) := by
  refine ⟨h.rgraph.gmap f, fun Q hQ => ?_, fun e he => ?_⟩
  · obtain ⟨Q₀, hQ₀, rfl⟩ := mem_gmap.1 hQ
    rw [card_map]; exact h.card_eq Q₀ hQ₀
  · by_cases hrange : ∀ x ∈ e, ∃ y, f y = x
    · classical
      set e₀ := e.preimage f f.injective.injOn with he₀
      have hmap : e₀.map f = e := by
        ext x
        simp only [mem_map, he₀, mem_preimage]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx; obtain ⟨y, rfl⟩ := hrange x hx; exact ⟨y, hx, rfl⟩
      have hc : e₀.card = r := by rw [← card_map f, hmap, he]
      have h1 := h.mult_eq e₀ hc
      have hiff : e ∈ RefinedAbsorption.gmap f G ↔ e₀ ∈ G := by rw [← hmap, map_mem_gmap]
      have hcount : cliqueMult (RefinedAbsorption.gmap f 𝒬) e = cliqueMult 𝒬 e₀ := by
        rw [← hmap, cliqueMult, cliqueMult, RefinedAbsorption.gmap, filter_map, card_map]
        congr 2
        ext Q
        simp [Function.comp, mapEmb_toEmb_apply, map_subset_map]
      rw [hcount, h1]
      simp only [hiff]
    · push_neg at hrange
      obtain ⟨x, hx, hx'⟩ := hrange
      have hnot : e ∉ RefinedAbsorption.gmap f G := by
        intro h'
        obtain ⟨e₀, -, rfl⟩ := mem_gmap.1 h'
        obtain ⟨y, -, rfl⟩ := mem_map.1 hx
        exact hx' y rfl
      rw [if_neg hnot, cliqueMult, card_eq_zero, filter_eq_empty_iff]
      intro Q hQ heQ
      obtain ⟨Q₀, -, rfl⟩ := mem_gmap.1 hQ
      obtain ⟨y, -, rfl⟩ := mem_map.1 (heQ hx)
      exact hx' y rfl

/-- Removing a set `C` of cliques from a decomposition of `G` gives a decomposition of `G` minus
the edges of these cliques. -/
theorem IsDecomposition.sdiff_biUnion {q r : ℕ} {G 𝒬 C : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) (hC : C ⊆ 𝒬) :
    IsDecomposition q r (G \ C.biUnion (cliqueEdges r)) (𝒬 \ C) := by
  refine ⟨fun e he => h.rgraph e (mem_sdiff.1 he).1,
    fun Q hQ => h.card_eq Q (mem_sdiff.1 hQ).1, fun e he => ?_⟩
  have h1 := h.mult_eq e he
  by_cases heG : e ∈ G
  · rw [if_pos heG, cliqueMult, card_eq_one] at h1
    obtain ⟨Q₀, hQ₀⟩ := h1
    have hQ₀m : Q₀ ∈ 𝒬 ∧ e ⊆ Q₀ := by
      have : Q₀ ∈ 𝒬.filter (fun Q => e ⊆ Q) := by rw [hQ₀]; exact mem_singleton_self _
      exact mem_filter.1 this
    have huniq : ∀ Q ∈ 𝒬, e ⊆ Q → Q = Q₀ := by
      intro Q hQ heQ
      have : Q ∈ 𝒬.filter (fun Q => e ⊆ Q) := mem_filter.2 ⟨hQ, heQ⟩
      rw [hQ₀] at this; exact mem_singleton.1 this
    by_cases hQ₀C : Q₀ ∈ C
    · have hnot : e ∉ G \ C.biUnion (cliqueEdges r) := fun h' =>
        (mem_sdiff.1 h').2 (mem_biUnion.2 ⟨Q₀, hQ₀C, mem_powersetCard.2 ⟨hQ₀m.2, he⟩⟩)
      rw [if_neg hnot, cliqueMult, card_eq_zero, filter_eq_empty_iff]
      intro Q hQ heQ
      rw [huniq Q (mem_sdiff.1 hQ).1 heQ] at hQ
      exact (mem_sdiff.1 hQ).2 hQ₀C
    · have hin : e ∈ G \ C.biUnion (cliqueEdges r) := by
        refine mem_sdiff.2 ⟨heG, fun h' => ?_⟩
        obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.1 h'
        rw [huniq Q (hC hQ) (mem_powersetCard.1 heQ).1] at hQ
        exact hQ₀C hQ
      rw [if_pos hin, cliqueMult, card_eq_one]
      refine ⟨Q₀, ?_⟩
      ext Q
      simp only [mem_filter, mem_sdiff, mem_singleton]
      constructor
      · rintro ⟨⟨hQ, -⟩, heQ⟩; exact huniq Q hQ heQ
      · rintro rfl; exact ⟨⟨hQ₀m.1, hQ₀C⟩, hQ₀m.2⟩
  · rw [if_neg heG] at h1
    have hnot : e ∉ G \ C.biUnion (cliqueEdges r) := fun h' => heG (mem_sdiff.1 h').1
    rw [if_neg hnot, cliqueMult, card_eq_zero, filter_eq_empty_iff]
    intro Q hQ heQ
    have : 0 < cliqueMult 𝒬 e := card_pos.2 ⟨Q, mem_filter.2 ⟨(mem_sdiff.1 hQ).1, heQ⟩⟩
    omega

/-- Union of decompositions of pairwise edge-disjoint graphs indexed by a finite set. -/
theorem IsDecomposition.biUnion {q r : ℕ} (hrq : r ≤ q) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (G 𝒬 : ι → Finset (Finset V)) (hdisj : (s : Set ι).PairwiseDisjoint G)
    (h : ∀ i ∈ s, IsDecomposition q r (G i) (𝒬 i)) :
    IsDecomposition q r (s.biUnion G) (s.biUnion 𝒬) := by
  have := IsDecomposition.sup hrq s G 𝒬 hdisj h
  rwa [sup_eq_biUnion, sup_eq_biUnion] at this

/-- Two distinct cliques of a decomposition are edge-disjoint. -/
theorem IsDecomposition.disjoint_cliqueEdges {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) {Q Q' : Finset V} (hQ : Q ∈ 𝒬) (hQ' : Q' ∈ 𝒬) (hne : Q ≠ Q') :
    Disjoint (cliqueEdges r Q) (cliqueEdges r Q') := by
  rw [disjoint_left]
  intro e he he'
  have hc := (mem_powersetCard.1 he).2
  have h1 := h.mult_eq e hc
  have heG := h.cliqueEdges_subset hQ he
  rw [if_pos heG] at h1
  have : ({Q, Q'} : Finset (Finset V)) ⊆ 𝒬.filter (fun P => e ⊆ P) := by
    intro P hP
    rcases mem_insert.1 hP with rfl | hP
    · exact mem_filter.2 ⟨hQ, (mem_powersetCard.1 he).1⟩
    · rw [mem_singleton.1 hP]; exact mem_filter.2 ⟨hQ', (mem_powersetCard.1 he').1⟩
  have := card_le_card this
  rw [card_pair hne] at this
  rw [cliqueMult] at h1
  omega

end RefinedAbsorption
