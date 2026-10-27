module
public import RequestProject.Placement.Lemma52
public import RequestProject.Absorber17.Library

/-!
# Placing the bounded absorber library inside `K_n^r`

We apply the Partial Clique Embedding Lemma (`partialCliqueEmbedding`) to the uniform library of
bounded absorbers (`RefinedAbsorption.Absorber17.absorberLibrary`).

* `exists_absorberGadget`: every divisible `r`-graph `W` with at most `c` edges is the root
  graph of a gadget (roots `V(W)`, `B = B(q,r,c)` auxiliary vertices) such that **every** valid
  placement of the gadget is a `B`-bounded absorber for `W`, with both modes placed alongside.
* `placedAttachedAbsorbers`: for a family `𝒲` of such pieces in `K_n^r`, absorbers can be attached
  to all pieces *inside `Fin n`*: pairwise edge-disjoint, edge-disjoint from `X ∪ R`, and with
  `Δ_{r-1}(⋃ A W) ≤ C · D`, where `D` is the maximum number of pieces whose vertex set contains a
  given `(r-1)`-set.

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Lemma 5.2 and its use for absorbers).
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.Absorber17

/-- The embedding `Fin k ⊕ Fin B ↪ V ⊕ Fin B` given by `ψ` on the roots. -/
def rootSumEmb {V : Type*} {k B : ℕ} (ψ : Fin k ↪ V) : Fin k ⊕ Fin B ↪ V ⊕ Fin B :=
  Function.Embedding.sumMap ψ (Function.Embedding.refl _)

/-- Placing a template that was transported along `rootSumEmb ψ` is the same as transporting the
original template along `Sum.elim ψ φ`. -/
theorem newEdges_gmap_rootSumEmb {n k B : ℕ} (ψ : Fin k ↪ Fin n) (φ : Fin B ↪ Fin n)
    (hdisj : ∀ i j, ψ i ≠ φ j) (A : Finset (Finset (Fin k ⊕ Fin B))) :
    newEdges (RefinedAbsorption.gmap (rootSumEmb ψ) A) φ =
      RefinedAbsorption.gmap (sumElimEmb ψ φ hdisj) A := by
  ext f
  simp only [newEdges, mem_image, mem_gmap]
  constructor
  · rintro ⟨t, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨e, he, ?_⟩
    ext x
    simp only [placeEdge, mem_map, mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨rootSumEmb ψ y, ⟨y, hy, rfl⟩, by cases y <;> rfl⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by cases y <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    refine ⟨e.map (rootSumEmb ψ), ⟨e, he, rfl⟩, ?_⟩
    ext x
    simp only [placeEdge, mem_map, mem_image]
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by cases y <;> rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨rootSumEmb ψ y, ⟨y, hy, rfl⟩, by cases y <;> rfl⟩

/-- **Rooted templates.**  A divisible `r`-graph `L` with at most `c` edges is the image of a type
`LS` on `Fin |V(L)|` along an enumeration `ψ` of `V(L)`, and `LS` has a library template on
`Fin |V(L)| ⊕ Fin B`. -/
theorem exists_rootedTemplate {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (c : ℕ) {V : Type}
    [DecidableEq V] (L : Finset (Finset V)) (hL : IsRGraph r L) (hdiv : IsDivisible q r L)
    (hc : L.card ≤ c) :
    ∃ ψ : Fin (vertexSet L).card ↪ V, (∀ i, ψ i ∈ vertexSet L) ∧
      ∃ LS : Finset (Finset (Fin (vertexSet L).card)), RefinedAbsorption.gmap ψ LS = L ∧
      ∃ A Qon Qoff : Finset (Finset (Fin (vertexSet L).card ⊕ Fin (libraryBound q r hr hrq c))),
        IsBoundedAbsorber q r (libraryBound q r hr hrq c)
          (RefinedAbsorption.gmap Function.Embedding.inl LS) A Qon Qoff := by
  classical
  set T := vertexSet L with hT
  set k := T.card with hk
  have hkc : k ≤ r * c := card_vertexSet_le hL hc
  let ψ : Fin k ↪ V := ⟨fun i => (T.equivFin.symm i).1, fun i j h =>
    T.equivFin.symm.injective (Subtype.val_injective h)⟩
  have hψT : ∀ i, ψ i ∈ T := fun i => (T.equivFin.symm i).2
  have hrange : ∀ x ∈ T, ∃ i, ψ i = x := fun x hx =>
    ⟨T.equivFin ⟨x, hx⟩, by
      change ((T.equivFin.symm (T.equivFin ⟨x, hx⟩)) : V) = x
      simp⟩
  have hpre : ∀ e ∈ L, (e.preimage ψ ψ.injective.injOn).map ψ = e := by
    intro e he
    ext x
    simp only [mem_map, mem_preimage]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      obtain ⟨i, rfl⟩ := hrange x (subset_vertexSet he hx)
      exact ⟨i, hx, rfl⟩
  set LS : Finset (Finset (Fin k)) := L.image (fun e => e.preimage ψ ψ.injective.injOn)
    with hLSdef
  have hLS : RefinedAbsorption.gmap ψ LS = L := by
    ext e
    simp only [mem_gmap, hLSdef, mem_image]
    constructor
    · rintro ⟨e₀, ⟨e', he', rfl⟩, rfl⟩; rw [hpre e' he']; exact he'
    · intro he; exact ⟨_, ⟨e, he, rfl⟩, hpre e he⟩
  have hLSr : IsRGraph r LS := by
    intro e₀ he₀
    rw [← card_map ψ]
    exact hL _ (hLS ▸ map_mem_gmap.2 he₀)
  have hLSd : IsDivisible q r LS := by
    intro S₀ hS₀
    rw [← deg_gmap_map ψ, hLS]
    have := hdiv (S₀.map ψ) (by rwa [card_map])
    rwa [card_map] at this
  obtain ⟨A, Qon, Qoff, hA⟩ := exists_libraryTemplate hr hrq hkc LS hLSr hLSd
  exact ⟨ψ, hψT, LS, hLS, A, Qon, Qoff, hA⟩

/-- The empty graph has the trivial bounded absorber. -/
theorem isBoundedAbsorber_empty {q r B : ℕ} {V : Type*} [DecidableEq V] :
    IsBoundedAbsorber q r B (∅ : Finset (Finset V)) ∅ ∅ ∅ := by
  have hdec : IsDecomposition q r (∅ : Finset (Finset V)) ∅ :=
    ⟨fun e he => by simp at he, fun Q hQ => by simp at hQ, fun e _ => by simp [cliqueMult]⟩
  refine ⟨⟨fun S _ => by simp [deg], fun e he => by simp at he, ⟨∅, hdec⟩, ⟨∅, by simpa using hdec⟩⟩,
    by simpa using hdec, hdec, by simp [vertexSet], by simp, by simp, by simp⟩

/-- **Absorber gadgets.**  Every nonempty divisible `r`-graph `W` with at most `c` edges on
`Fin n` is the root graph of a gadget with roots `V(W)` (at most `r c` of them) and
`B = libraryBound` auxiliary vertices, together with two clique templates, such that every valid
placement `φ` yields a `B`-bounded absorber for `W` (absorber `newEdges T φ`, on-mode
`newEdges Ton φ`, off-mode `newEdges Toff φ`). -/
theorem exists_absorberGadget {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (c : ℕ) {n : ℕ}
    (W : Finset (Finset (Fin n))) (hW : IsRGraph r W) (hdiv : IsDivisible q r W)
    (hc : W.card ≤ c) (hne : W.Nonempty) :
    ∃ T Ton Toff : Finset (Finset (Fin n ⊕ Fin (libraryBound q r hr hrq c))),
      GadgetWF r (r * c) (vertexSet W) T ∧
      ∀ φ, ValidPlacement (vertexSet W) φ →
        IsBoundedAbsorber q r (libraryBound q r hr hrq c) W (newEdges T φ) (newEdges Ton φ)
          (newEdges Toff φ) := by
  classical
  obtain ⟨ψ, hψ, LS, hLS, A, Qon, Qoff, hA⟩ := exists_rootedTemplate hr hrq c W hW hdiv hc
  refine ⟨RefinedAbsorption.gmap (rootSumEmb ψ) A, RefinedAbsorption.gmap (rootSumEmb ψ) Qon,
    RefinedAbsorption.gmap (rootSumEmb ψ) Qoff, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact card_vertexSet_le hW hc
  · obtain ⟨e, he⟩ := hne
    calc r - 1 ≤ e.card := by rw [hW e he]; omega
      _ ≤ _ := card_le_card (subset_vertexSet he)
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_gmap.1 ht
    rw [card_map]
    exact hA.off.rgraph e he
  · intro t ht a ha
    obtain ⟨e, he, rfl⟩ := mem_gmap.1 ht
    obtain ⟨y, -, hy⟩ := mem_map.1 ha
    rcases y with i | j
    · have : ψ i = a := by simpa [rootSumEmb] using hy
      rw [← this]; exact hψ i
    · simp [rootSumEmb] at hy
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_gmap.1 ht
    by_contra hno
    push_neg at hno
    apply hA.absorber.independent e he
    intro x hx
    rcases x with i | j
    · rw [vertexSet_gmap]
      refine mem_map_of_mem _ ?_
      have : ψ i ∈ vertexSet (RefinedAbsorption.gmap ψ LS) := by rw [hLS]; exact hψ i
      rw [vertexSet_gmap] at this
      obtain ⟨i', hi', hii'⟩ := mem_map.1 this
      rwa [ψ.injective hii'] at hi'
    · exact absurd (mem_map_of_mem (rootSumEmb ψ) hx) (hno j)
  · rintro φ ⟨hinj, havoid⟩
    let φe : Fin (libraryBound q r hr hrq c) ↪ Fin n := ⟨φ, hinj⟩
    have hdisj : ∀ i j, ψ i ≠ φe j := fun i j h =>
      havoid j (by rw [← show ψ i = φ j from h]; exact hψ i)
    show IsBoundedAbsorber q r _ W (newEdges _ ⇑φe) (newEdges _ ⇑φe) (newEdges _ ⇑φe)
    rw [newEdges_gmap_rootSumEmb ψ φe hdisj, newEdges_gmap_rootSumEmb ψ φe hdisj,
      newEdges_gmap_rootSumEmb ψ φe hdisj]
    have h := hA.gmap (sumElimEmb ψ φe hdisj)
    rw [gmap_gmap] at h
    have hinl : Function.Embedding.inl.trans (sumElimEmb ψ φe hdisj) = ψ := by ext i; rfl
    rwa [hinl, hLS] at h

/-- **Attached absorbers inside `K_n^r`** (the absorber half of the final embedding step).

Fix `q > r ≥ 1` and `c`.  There are `B` and `C` such that for every family `𝒲` of divisible
`r`-graphs on `Fin n` with at most `c` edges each, every host `r`-graph `X ∪ R` with
`C · Δ_{r-1}(X ∪ R) ≤ n`, and every `D` with `C · D ≤ n` bounding the number of pieces whose
vertex set contains a given `(r-1)`-set, there are attached absorbers inside `Fin n`: each is a
`B`-bounded absorber for its piece, they are pairwise edge-disjoint and edge-disjoint from
`X ∪ R`, and their union has maximum `(r-1)`-degree at most `C · D`. -/
theorem placedAttachedAbsorbers {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (c : ℕ) :
    ∃ B C : ℕ, 0 < C ∧ ∀ (n : ℕ) (X R : Finset (Finset (Fin n)))
      (𝒲 : Finset (Finset (Finset (Fin n)))) (D : ℕ),
      (∀ W ∈ 𝒲, IsRGraph r W) → (∀ W ∈ 𝒲, IsDivisible q r W) → (∀ W ∈ 𝒲, W.card ≤ c) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg (X ∪ R) S ≤ n) →
      (∀ S : Finset (Fin n), S.card = r - 1 → (𝒲.filter fun W => S ⊆ vertexSet W).card ≤ D) →
      C * D ≤ n → 0 < n →
      ∃ A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n)),
        IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff ∧
        (∀ W ∈ 𝒲, IsBoundedAbsorber q r B W (A W) (Qon W) (Qoff W)) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → deg (𝒲.sup A) S ≤ C * D) := by
  classical
  set B := libraryBound q r hr hrq c
  obtain ⟨C, hC, hemb⟩ := partialCliqueEmbedding r B (r * c)
  refine ⟨B, C, hC, ?_⟩
  intro n X R 𝒲 D hrg hdiv hcard hG hD hCD hn
  set I := 𝒲.filter fun W => W.Nonempty
  have hgad : ∀ W ∈ I, ∃ T Ton Toff : Finset (Finset (Fin n ⊕ Fin B)),
      GadgetWF r (r * c) (vertexSet W) T ∧
      ∀ φ, ValidPlacement (vertexSet W) φ →
        IsBoundedAbsorber q r B W (newEdges T φ) (newEdges Ton φ) (newEdges Toff φ) := by
    intro W hW
    rw [mem_filter] at hW
    exact exists_absorberGadget hr hrq c W (hrg W hW.1) (hdiv W hW.1) (hcard W hW.1) hW.2
  choose! T Ton Toff hTw hTabs using hgad
  obtain ⟨Φ, hvalid, hdisj, hhost, hdeg⟩ := hemb n I (fun W => vertexSet W) T (X ∪ R) D hTw hG
    hCD (fun S hS => le_trans (card_le_card (filter_subset_filter _ (filter_subset _ _)))
      (hD S hS)) hn
  set A : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (T W) (Φ W) else ∅
  set Qon : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (Ton W) (Φ W) else ∅
  set Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (Toff W) (Φ W) else ∅
  have hbd : ∀ W ∈ 𝒲, IsBoundedAbsorber q r B W (A W) (Qon W) (Qoff W) := by
    intro W hW
    by_cases hWI : W ∈ I
    · simp only [A, Qon, Qoff, if_pos hWI]
      exact hTabs W hWI (Φ W) (hvalid W hWI)
    · have hW0 : W = ∅ := by
        by_contra h
        exact hWI (mem_filter.2 ⟨hW, nonempty_iff_ne_empty.2 h⟩)
      simp only [A, Qon, Qoff, if_neg hWI]
      rw [hW0]
      exact isBoundedAbsorber_empty
  refine ⟨A, Qon, Qoff, ⟨fun W hW => (hbd W hW).off.rgraph, ?_, ?_, fun W hW => (hbd W hW).on,
    fun W hW => (hbd W hW).off⟩, hbd, ?_⟩
  · intro W _
    simp only [A]
    split_ifs with hWI
    · exact hhost W hWI
    · exact disjoint_empty_left _
  · intro W hW W' hW' hne
    simp only [A]
    split_ifs with h1 h2 h2
    · exact hdisj W h1 W' h2 hne
    · exact disjoint_empty_right _
    · exact disjoint_empty_left _
    · exact disjoint_empty_left _
  · intro S hS
    have hsup : 𝒲.sup A ⊆ I.biUnion fun W => newEdges (T W) (Φ W) := by
      intro f hf
      obtain ⟨W, hW, hfW⟩ := mem_sup.1 hf
      simp only [A] at hfW
      split_ifs at hfW with hWI
      · exact mem_biUnion.2 ⟨W, hWI, hfW⟩
      · simp at hfW
    refine le_trans ?_ (hdeg S hS)
    unfold deg
    exact card_le_card (filter_subset_filter _ hsup)

end RefinedAbsorption.Placement
