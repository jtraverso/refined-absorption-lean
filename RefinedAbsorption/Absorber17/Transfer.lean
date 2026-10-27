module
public import RefinedAbsorption.Absorber17.Maps
public import RefinedAbsorption.Statements

/-!
# Transporting absorbers

Absorbers are preserved by injective vertex maps, an absorber for `L ∪ G` (with `G`
decomposable) yields an absorber for `L`, and an absorber living on `Fin m ⊕ R` can be moved to
`Fin N` with the original vertices `Fin m` placed first.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- A single `q`-clique decomposes its own edge set. -/
theorem isDecomposition_singleton {q r : ℕ} {Q : Finset V} (hQ : Q.card = q) :
    IsDecomposition q r (cliqueEdges r Q) {Q} := by
  refine ⟨fun e he => (mem_powersetCard.1 he).2, fun Q' hQ' => by
    rw [mem_singleton.1 hQ']; exact hQ, fun e he => ?_⟩
  by_cases h : e ⊆ Q
  · rw [cliqueEdges, if_pos (mem_powersetCard.2 ⟨h, he⟩), cliqueMult, filter_singleton, if_pos h,
      card_singleton]
  · rw [cliqueEdges, if_neg (fun h' => h (mem_powersetCard.1 h').1), cliqueMult, filter_singleton, if_neg h,
      card_empty]

theorem vertexSet_gmap (f : U ↪ V) (G : Finset (Finset U)) :
    vertexSet (gmap f G) = (vertexSet G).map f := by
  ext x
  simp only [vertexSet, mem_sup, id, mem_gmap, mem_map]
  constructor
  · rintro ⟨e, ⟨e₀, he₀, rfl⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact ⟨y, ⟨e₀, he₀, hy⟩, rfl⟩
  · rintro ⟨y, ⟨e₀, he₀, hy⟩, rfl⟩
    exact ⟨e₀.map f, ⟨e₀, he₀, rfl⟩, mem_map_of_mem f hy⟩

theorem deg_gmap_map (f : U ↪ V) (G : Finset (Finset U)) (S : Finset U) :
    deg (gmap f G) (S.map f) = deg G S := by
  rw [deg, deg, gmap, filter_map, card_map]
  congr 2
  ext e
  simp [Function.comp, mapEmb_toEmb_apply, map_subset_map]

theorem IsDivisible.gmap {q r : ℕ} {L : Finset (Finset U)} (h : IsDivisible q r L) (f : U ↪ V) :
    IsDivisible q r (gmap f L) := by
  intro S hS
  by_cases hrange : ∀ x ∈ S, ∃ y, f y = x
  · classical
    set S₀ := S.preimage f f.injective.injOn with hS₀
    have hmap : S₀.map f = S := by
      ext x
      simp only [mem_map, hS₀, mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; obtain ⟨y, rfl⟩ := hrange x hx; exact ⟨y, hx, rfl⟩
    have hc : S₀.card = S.card := by rw [← card_map f, hmap]
    rw [← hmap, deg_gmap_map, card_map]
    exact h S₀ (hc ▸ hS)
  · push_neg at hrange
    obtain ⟨x, hx, hx'⟩ := hrange
    have : deg (RefinedAbsorption.gmap f L) S = 0 := by
      rw [deg, card_eq_zero, filter_eq_empty_iff]
      intro e he hSe
      obtain ⟨e₀, -, rfl⟩ := mem_gmap.1 he
      obtain ⟨y, -, rfl⟩ := mem_map.1 (hSe hx)
      exact hx' y rfl
    rw [this]; exact dvd_zero _

/-- Absorbers are transported along injective vertex maps. -/
theorem IsAbsorber.gmap {q r : ℕ} {L A : Finset (Finset U)} (h : IsAbsorber q r L A)
    (f : U ↪ V) : IsAbsorber q r (RefinedAbsorption.gmap f L) (RefinedAbsorption.gmap f A) := by
  refine ⟨h.divisible.gmap f, fun e he hsub => ?_, ?_, ?_⟩
  · obtain ⟨e₀, he₀, rfl⟩ := mem_gmap.1 he
    rw [vertexSet_gmap, map_subset_map] at hsub
    exact h.independent e₀ he₀ hsub
  · obtain ⟨𝒬, h𝒬⟩ := h.decomp
    exact ⟨_, h𝒬.gmap f⟩
  · obtain ⟨𝒬, h𝒬⟩ := h.decomp_union
    rw [← gmap_union]
    exact ⟨_, h𝒬.gmap f⟩

theorem subset_vertexSet {G : Finset (Finset V)} {e : Finset V} (he : e ∈ G) :
    e ⊆ vertexSet G := le_sup (f := id) he

theorem vertexSet_union (G H : Finset (Finset V)) :
    vertexSet (G ∪ H) = vertexSet G ∪ vertexSet H := sup_union

/-- **Padding.**  If `A` absorbs `L ∪ G`, where `G` is decomposable and edge-disjoint from `L`
and no edge of `G` lies inside `V(L)`, then `A ∪ G` absorbs `L`. -/
theorem IsAbsorber.pad {q r : ℕ} (hrq : r ≤ q) {L G A : Finset (Finset V)}
    (h : IsAbsorber q r (L ∪ G) A) (hL : IsDivisible q r L) (hG : HasDecomposition q r G)
    (hGL : ∀ e ∈ G, ¬ e ⊆ vertexSet L) : IsAbsorber q r L (A ∪ G) := by
  have hdisj : Disjoint A G := by
    rw [disjoint_left]
    intro e heA heG
    exact h.independent e heA ((subset_vertexSet heG).trans
      (by rw [vertexSet_union]; exact subset_union_right))
  refine ⟨hL, fun e he hsub => ?_, ?_, ?_⟩
  · rcases mem_union.1 he with he | he
    · exact h.independent e he (hsub.trans (by rw [vertexSet_union]; exact subset_union_left))
    · exact hGL e he hsub
  · obtain ⟨𝒬, h𝒬⟩ := h.decomp
    obtain ⟨𝒲, h𝒲⟩ := hG
    exact ⟨_, IsDecomposition.union hrq hdisj h𝒬 h𝒲⟩
  · have : A ∪ G ∪ L = A ∪ (L ∪ G) := by
      ext; simp only [mem_union]; tauto
    rw [this]; exact h.decomp_union

/-- The embedding `Fin m ⊕ R ↪ Fin (m + |R|)` sending `inl i` to `i`. -/
noncomputable def finSumEmb (m : ℕ) (R : Type*) [Fintype R] :
    Fin m ⊕ R ↪ Fin (m + Fintype.card R) :=
  ((Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin R)).trans finSumFinEquiv).toEmbedding

theorem finSumEmb_inl (m : ℕ) (R : Type*) [Fintype R] (i : Fin m) :
    finSumEmb m R (Sum.inl i) = Fin.castLE (Nat.le_add_right _ _) i := by
  simp [finSumEmb]
  rfl

/-- An absorber for the copy of `L` on `Fin m ⊕ R` gives the conclusion of Theorem 1.7. -/
theorem absorber_on_fin {q r m : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {L : Finset (Finset (Fin m))} {A : Finset (Finset (Fin m ⊕ R))}
    (h : IsAbsorber q r (gmap (Function.Embedding.inl) L) A) :
    ∃ N, ∃ hN : m ≤ N, ∃ A' : Finset (Finset (Fin N)),
      IsAbsorber q r (L.map (Finset.mapEmbedding (Fin.castLEEmb hN)).toEmbedding) A' := by
  refine ⟨m + Fintype.card R, Nat.le_add_right _ _, gmap (finSumEmb m R) A, ?_⟩
  have h' := h.gmap (finSumEmb m R)
  have hL : gmap (finSumEmb m R) (gmap Function.Embedding.inl L) =
      L.map (Finset.mapEmbedding (Fin.castLEEmb (Nat.le_add_right m (Fintype.card R)))).toEmbedding := by
    ext e
    simp only [mem_gmap, mem_map]
    constructor
    · rintro ⟨e₁, ⟨e₀, he₀, rfl⟩, rfl⟩
      refine ⟨e₀, he₀, ?_⟩
      rw [mapEmb_toEmb_apply, map_map]
      congr 1
    · rintro ⟨e₀, he₀, rfl⟩
      refine ⟨e₀.map Function.Embedding.inl, ⟨e₀, he₀, rfl⟩, ?_⟩
      rw [mapEmb_toEmb_apply, map_map]
      congr 1
  rw [hL] at h'
  exact h'

end RefinedAbsorption
