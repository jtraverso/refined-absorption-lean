module
public import RefinedAbsorption.Absorber17.Attach

/-!
# A uniform library of absorbers

Fix `q > r ≥ 1` and `c`.  There is a single constant `B = B(q, r, c)` such that every
`K_q^r`-divisible `r`-graph `L` with at most `c` edges has a `K_q^r`-absorber with at most `B`
vertices and at most `B` edges, together with an "on" decomposition (of `A ∪ L`) and an "off"
decomposition (of `A`) each with at most `B` cliques.  Moreover the absorber can be placed on the
roots `V(L)` plus any prescribed set of at least `B` further vertices.

Proof: `L` has at most `rc` vertices, so up to relabelling its vertex set there are only finitely
many such `L` (`r`-graphs on `Fin k`, `k ≤ rc`).  For each of these *types* we choose one
absorber (Theorem 1.7) and record the size of its vertex set, of its edge set and of its two
decompositions; `B` is the maximum.  The chosen template lives on `Fin k ⊕ Fin B` with the roots
on the left; it is transported to `L` along an embedding that is the given enumeration of `V(L)`
on the roots (the roots are fixed) and an arbitrary injection into the prescribed vertex set on
the remaining vertices.
-/

@[expose] public section

namespace RefinedAbsorption.Absorber17

open Finset

/-- **Bounded absorber.**  `A` is a `K_q^r`-absorber for `L` with explicit decompositions
`Qon` of `A ∪ L` and `Qoff` of `A`, and the vertex set of `A`, the edge set of `A` and both
decompositions have size at most `B`. -/
structure IsBoundedAbsorber (q r B : ℕ) {V : Type*} [DecidableEq V]
    (L A Qon Qoff : Finset (Finset V)) : Prop where
  absorber : IsAbsorber q r L A
  on : IsDecomposition q r (A ∪ L) Qon
  off : IsDecomposition q r A Qoff
  card_vertices : (vertexSet A).card ≤ B
  card_edges : A.card ≤ B
  card_on : Qon.card ≤ B
  card_off : Qoff.card ≤ B

theorem IsBoundedAbsorber.mono {q r B B' : ℕ} {V : Type*} [DecidableEq V]
    {L A Qon Qoff : Finset (Finset V)} (h : IsBoundedAbsorber q r B L A Qon Qoff) (hB : B ≤ B') :
    IsBoundedAbsorber q r B' L A Qon Qoff :=
  ⟨h.absorber, h.on, h.off, h.card_vertices.trans hB, h.card_edges.trans hB, h.card_on.trans hB,
    h.card_off.trans hB⟩

theorem card_gmap {U V : Type*} [DecidableEq U] [DecidableEq V] (f : U ↪ V)
    (G : Finset (Finset U)) : (gmap f G).card = G.card := card_map _

/-- Bounded absorbers are transported along injective vertex maps. -/
theorem IsBoundedAbsorber.gmap {q r B : ℕ} {U V : Type*} [DecidableEq U] [DecidableEq V]
    {L A Qon Qoff : Finset (Finset U)} (h : IsBoundedAbsorber q r B L A Qon Qoff) (f : U ↪ V) :
    IsBoundedAbsorber q r B (RefinedAbsorption.gmap f L) (RefinedAbsorption.gmap f A)
      (RefinedAbsorption.gmap f Qon) (RefinedAbsorption.gmap f Qoff) := by
  refine ⟨h.absorber.gmap f, ?_, h.off.gmap f, ?_, ?_, ?_, ?_⟩
  · rw [← gmap_union]; exact h.on.gmap f
  · rw [vertexSet_gmap, card_map]; exact h.card_vertices
  · rw [card_gmap]; exact h.card_edges
  · rw [card_gmap]; exact h.card_on
  · rw [card_gmap]; exact h.card_off

/-- The embedding `Fin N ↪ Fin k ⊕ Fin M` putting `Fin k` (the roots) on the left. -/
def splitEmb {k N M : ℕ} (hNM : N ≤ M) : Fin N ↪ Fin k ⊕ Fin M :=
  ⟨fun i => if h : i.1 < k then Sum.inl ⟨i.1, h⟩ else Sum.inr ⟨i.1 - k, by omega⟩,
    fun i j hij => by
      by_cases hi : i.1 < k <;> by_cases hj : j.1 < k <;>
        simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq, Fin.mk.injEq] at hij
      · exact Fin.ext hij
      · exact Fin.ext (by omega)⟩

/-- **Templates.**  Every `K_q^r`-divisible `r`-graph `LS` on `Fin k` has a bounded absorber on
`Fin k ⊕ Fin M` (for some `M`) with roots `Fin k` on the left. -/
theorem exists_template {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {k : ℕ}
    (LS : Finset (Finset (Fin k))) (h1 : IsRGraph r LS) (h2 : IsDivisible q r LS) :
    ∃ M : ℕ, ∃ A Qon Qoff : Finset (Finset (Fin k ⊕ Fin M)),
      IsBoundedAbsorber q r M (RefinedAbsorption.gmap Function.Embedding.inl LS) A Qon Qoff := by
  obtain ⟨N, hN, A', habs⟩ := absorberExistence q r hr hrq k LS h1 h2
  change IsAbsorber q r (RefinedAbsorption.gmap (Fin.castLEEmb hN) LS) A' at habs
  obtain ⟨Qon, hon⟩ := habs.decomp_union
  obtain ⟨Qoff, hoff⟩ := habs.decomp
  set M := N + A'.card + Qon.card + Qoff.card with hM
  have hb : IsBoundedAbsorber q r M (RefinedAbsorption.gmap (Fin.castLEEmb hN) LS) A' Qon Qoff :=
    ⟨habs, hon, hoff, (card_le_univ _).trans (by simp [hM]; omega), by omega, by omega, by omega⟩
  have hφ := hb.gmap (splitEmb (k := k) (show N ≤ M by omega))
  rw [gmap_gmap] at hφ
  have he : (Fin.castLEEmb hN).trans (splitEmb (k := k) (show N ≤ M by omega)) =
      Function.Embedding.inl := by
    ext i
    change (if h : i.1 < k then Sum.inl (⟨i.1, h⟩ : Fin k)
      else Sum.inr (⟨i.1 - k, by omega⟩ : Fin M)) = Sum.inl i
    rw [dif_pos i.2]
  rw [he] at hφ
  exact ⟨M, _, _, _, hφ⟩

/-- Enlarging the number of non-root vertices of a template. -/
theorem IsBoundedAbsorber.widen {q r k M M' : ℕ} (hM : M ≤ M')
    {LS : Finset (Finset (Fin k))} {A Qon Qoff : Finset (Finset (Fin k ⊕ Fin M))}
    (h : IsBoundedAbsorber q r M (RefinedAbsorption.gmap Function.Embedding.inl LS) A Qon Qoff) :
    ∃ A' Qon' Qoff' : Finset (Finset (Fin k ⊕ Fin M')),
      IsBoundedAbsorber q r M' (RefinedAbsorption.gmap Function.Embedding.inl LS) A' Qon' Qoff' := by
  have h' := (h.gmap (Function.Embedding.sumMap (Function.Embedding.refl _)
    (Fin.castLEEmb hM))).mono hM
  rw [gmap_gmap] at h'
  exact ⟨_, _, _, h'⟩

/-- An `r`-graph with at most `c` edges has at most `r c` vertices. -/
theorem card_vertexSet_le {V : Type*} [DecidableEq V] {r c : ℕ} {L : Finset (Finset V)}
    (hL : IsRGraph r L) (hc : L.card ≤ c) : (vertexSet L).card ≤ r * c := by
  rw [vertexSet, sup_eq_biUnion]
  refine (card_biUnion_le).trans ?_
  rw [sum_congr rfl (fun e he => (hL e he : (id e).card = r)), sum_const, smul_eq_mul]
  rw [mul_comm]; exact Nat.mul_le_mul_left r hc

open Classical in
/-- The size of the chosen template of a type `LS` (or `0` if `LS` is not a divisible
`r`-graph). -/
noncomputable def templateSize (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) (k : ℕ)
    (LS : Finset (Finset (Fin k))) : ℕ :=
  if h : IsRGraph r LS ∧ IsDivisible q r LS then
    Classical.choose (exists_template hr hrq LS h.1 h.2)
  else 0

/-- The uniform bound `B(q, r, c)`: the maximum template size over all types on at most
`r c` vertices. -/
noncomputable def libraryBound (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) (c : ℕ) : ℕ :=
  (range (r * c + 1)).sup fun k => (univ : Finset (Finset (Finset (Fin k)))).sup
    (templateSize q r hr hrq k)

theorem templateSize_le {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {c k : ℕ} (hk : k ≤ r * c)
    (LS : Finset (Finset (Fin k))) : templateSize q r hr hrq k LS ≤ libraryBound q r hr hrq c := by
  refine le_trans ?_ (le_sup (f := fun k => (univ : Finset (Finset (Finset (Fin k)))).sup
    (templateSize q r hr hrq k)) (mem_range.2 (Nat.lt_succ_of_le hk)))
  exact le_sup (f := templateSize q r hr hrq k) (mem_univ LS)

/-- Every type on at most `r c` vertices has a template with `libraryBound` non-root
vertices. -/
theorem exists_libraryTemplate {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {c k : ℕ} (hk : k ≤ r * c)
    (LS : Finset (Finset (Fin k))) (h1 : IsRGraph r LS) (h2 : IsDivisible q r LS) :
    ∃ A Qon Qoff : Finset (Finset (Fin k ⊕ Fin (libraryBound q r hr hrq c))),
      IsBoundedAbsorber q r (libraryBound q r hr hrq c)
        (RefinedAbsorption.gmap Function.Embedding.inl LS) A Qon Qoff := by
  classical
  have hle := templateSize_le hr hrq hk LS
  have hspec := Classical.choose_spec (exists_template hr hrq LS h1 h2)
  have heq : templateSize q r hr hrq k LS = Classical.choose (exists_template hr hrq LS h1 h2) := by
    rw [templateSize, dif_pos ⟨h1, h2⟩]
  obtain ⟨A, Qon, Qoff, hA⟩ := hspec
  rw [heq] at hle
  exact hA.widen hle

/-- An embedding of `Fin k ⊕ Fin B` built from two embeddings with disjoint ranges. -/
def sumElimEmb {V : Type*} {k B : ℕ} (ψ : Fin k ↪ V) (e : Fin B ↪ V)
    (h : ∀ i j, ψ i ≠ e j) : Fin k ⊕ Fin B ↪ V :=
  ⟨Sum.elim ψ e, fun x y hxy => by
    cases x <;> cases y <;> simp only [Sum.elim_inl, Sum.elim_inr] at hxy
    · exact congrArg _ (ψ.injective hxy)
    · exact absurd hxy (h _ _)
    · exact absurd hxy.symm (h _ _)
    · exact congrArg _ (e.injective hxy)⟩

/-- **Uniform absorber library.**  Fix `q > r ≥ 1` and `c`.  There is `B` such that every
`K_q^r`-divisible `r`-graph `L` with at most `c` edges, and every set `S` of at least `B`
vertices disjoint from `V(L)`, admit a `K_q^r`-absorber `A` for `L` with an on-mode `Qon`
(decomposition of `A ∪ L`) and an off-mode `Qoff` (decomposition of `A`), such that `A` has at
most `B` vertices and `B` edges, both modes have at most `B` cliques, and all vertices of `A`
lie in `V(L) ∪ S`. -/
theorem absorberLibrary {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (c : ℕ) :
    ∃ B : ℕ, ∀ (V : Type) [DecidableEq V] (L : Finset (Finset V)), IsRGraph r L →
      IsDivisible q r L → L.card ≤ c → ∀ S : Finset V, Disjoint S (vertexSet L) → B ≤ S.card →
        ∃ A Qon Qoff : Finset (Finset V), IsBoundedAbsorber q r B L A Qon Qoff ∧
          vertexSet A ⊆ vertexSet L ∪ S := by
  refine ⟨libraryBound q r hr hrq c, fun V _ L hL hdiv hc S hS hBS => ?_⟩
  classical
  set B := libraryBound q r hr hrq c
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
  set LS : Finset (Finset (Fin k)) := L.image (fun e => e.preimage ψ ψ.injective.injOn) with hLSdef
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
  obtain ⟨S', hS'S, hS'card⟩ := exists_subset_card_eq hBS
  let e : Fin B ↪ V := enumEmb S' hS'card
  have heS : ∀ j, e j ∈ S := fun j => hS'S (by
    rw [← map_enumEmb S' hS'card]; exact mem_map_of_mem _ (mem_univ j))
  have hdisj : ∀ i j, ψ i ≠ e j := fun i j h =>
    disjoint_left.1 hS (heS j) (h ▸ hψT i)
  let Φ := sumElimEmb ψ e hdisj
  have hΦ := hA.gmap Φ
  rw [gmap_gmap] at hΦ
  have hinl : Function.Embedding.inl.trans Φ = ψ := by ext i; rfl
  rw [hinl, hLS] at hΦ
  refine ⟨_, _, _, hΦ, ?_⟩
  rw [vertexSet_gmap]
  intro x hx
  obtain ⟨y, -, rfl⟩ := mem_map.1 hx
  cases y with
  | inl i => exact mem_union_left _ (hψT i)
  | inr j => exact mem_union_right _ (heS j)

/-- Every edge of an absorber placed on `V(L) ∪ S` meets `S` (the roots are independent). -/
theorem IsAbsorber.exists_mem_of_subset {q r : ℕ} {V : Type*} [DecidableEq V]
    {L A : Finset (Finset V)} (h : IsAbsorber q r L A) {S : Finset V}
    (hS : vertexSet A ⊆ vertexSet L ∪ S) {f : Finset V} (hf : f ∈ A) : ∃ x ∈ f, x ∈ S := by
  by_contra hno
  push_neg at hno
  refine h.independent f hf fun x hx => ?_
  rcases mem_union.1 (hS (subset_vertexSet hf hx)) with h' | h'
  · exact h'
  · exact absurd h' (hno x hx)

/-- The fresh vertices `(W, j)`, `j < B`, reserved for the absorber attached to `W`. -/
def freshSet {V : Type} [DecidableEq V] (W : Finset (Finset V)) (B : ℕ) :
    Finset (V ⊕ (Finset (Finset V) × ℕ)) :=
  (range B).image fun j => Sum.inr (W, j)

theorem card_freshSet {V : Type} [DecidableEq V] (W : Finset (Finset V)) (B : ℕ) :
    (freshSet W B).card = B := by
  rw [freshSet, card_image_of_injective _ (fun i j h => by simpa using h), card_range]

/-- **Bounded attached absorbers.**  Fix `q > r ≥ 1` and `C`.  There is `B` such that for every
family `𝒲` of `K_q^r`-divisible subgraphs of the `r`-graph `X ∪ R`, each with at most `C` edges,
there are attached absorbers (pairwise edge-disjoint, edge-disjoint from `X ∪ R`) on new vertices
such that every attached absorber has at most `B` vertices and `B` edges and both of its modes
have at most `B` cliques.  The absorber attached to `W` lives on `V(W)` plus `B` new vertices
reserved for `W`. -/
theorem exists_boundedAttachedAbsorbers {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (C : ℕ) :
    ∃ B : ℕ, ∀ (V : Type) [DecidableEq V] (X R : Finset (Finset V))
      (𝒲 : Finset (Finset (Finset V))), IsRGraph r (X ∪ R) → (∀ W ∈ 𝒲, W ⊆ X ∪ R) →
      (∀ W ∈ 𝒲, IsDivisible q r W) → (∀ W ∈ 𝒲, W.card ≤ C) →
      ∃ A Qon Qoff : Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))) →
          Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))),
        IsAttachedAbsorbers q r (RefinedAbsorption.gmap Function.Embedding.inl X)
          (RefinedAbsorption.gmap Function.Embedding.inl R)
          (𝒲.image (RefinedAbsorption.gmap Function.Embedding.inl)) A Qon Qoff ∧
        ∀ W ∈ 𝒲, IsBoundedAbsorber q r B (RefinedAbsorption.gmap Function.Embedding.inl W)
          (A (RefinedAbsorption.gmap Function.Embedding.inl W))
          (Qon (RefinedAbsorption.gmap Function.Embedding.inl W))
          (Qoff (RefinedAbsorption.gmap Function.Embedding.inl W)) ∧
          vertexSet (A (RefinedAbsorption.gmap Function.Embedding.inl W)) ⊆
            vertexSet (RefinedAbsorption.gmap Function.Embedding.inl W) ∪ freshSet W B := by
  obtain ⟨B, hB⟩ := absorberLibrary hr hrq C
  refine ⟨B, fun V _ X R 𝒲 hrg hsub hdiv hcard => ?_⟩
  classical
  set ι : V ↪ V ⊕ (Finset (Finset V) × ℕ) := Function.Embedding.inl with hι
  have hW : ∀ W ∈ 𝒲, ∃ A Qon Qoff : Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))),
      IsBoundedAbsorber q r B (RefinedAbsorption.gmap ι W) A Qon Qoff ∧
        vertexSet A ⊆ vertexSet (RefinedAbsorption.gmap ι W) ∪ freshSet W B := by
    intro W hWm
    refine hB _ _ ?_ ?_ ?_ _ ?_ ?_
    · exact IsRGraph.gmap (fun e he => hrg e (hsub W hWm he)) ι
    · exact (hdiv W hWm).gmap ι
    · rw [card_gmap]; exact hcard W hWm
    · rw [disjoint_left]
      intro x hx hx'
      rw [vertexSet_gmap] at hx'
      obtain ⟨y, -, rfl⟩ := mem_map.1 hx'
      obtain ⟨j, -, hj⟩ := mem_image.1 hx
      simp [ι] at hj
    · rw [card_freshSet]
  choose! Aw Qw Ow hAw hvert using hW
  have hinj : ∀ W₁ W₂ : Finset (Finset V),
      RefinedAbsorption.gmap ι W₁ = RefinedAbsorption.gmap ι W₂ → W₁ = W₂ :=
    fun W₁ W₂ h => map_injective _ h
  let pre : Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))) → Finset (Finset V) := fun W' =>
    if h : ∃ W ∈ 𝒲, RefinedAbsorption.gmap ι W = W' then Classical.choose h else ∅
  have hpre : ∀ W ∈ 𝒲, pre (RefinedAbsorption.gmap ι W) = W := by
    intro W hWm
    have h : ∃ W₀ ∈ 𝒲, RefinedAbsorption.gmap ι W₀ = RefinedAbsorption.gmap ι W :=
      ⟨W, hWm, rfl⟩
    simp only [pre, dif_pos h]
    exact hinj _ _ (Classical.choose_spec h).2
  refine ⟨fun W' => Aw (pre W'), fun W' => Qw (pre W'), fun W' => Ow (pre W'), ?_, ?_⟩
  · -- each edge of the absorber attached to `W` contains a fresh vertex tagged by `W`
    have hfr : ∀ W ∈ 𝒲, ∀ f ∈ Aw W, ∃ j, (Sum.inr (W, j) : V ⊕ (Finset (Finset V) × ℕ)) ∈ f := by
      intro W hWm f hf
      obtain ⟨x, hx, hxS⟩ := IsAbsorber.exists_mem_of_subset (hAw W hWm).absorber (hvert W hWm) hf
      obtain ⟨j, -, rfl⟩ := mem_image.1 hxS
      exact ⟨j, hx⟩
    have htag : ∀ W ∈ 𝒲, ∀ f ∈ Aw W, ∀ x ∈ f, ∀ W₁ j,
        x = (Sum.inr (W₁, j) : V ⊕ (Finset (Finset V) × ℕ)) → W₁ = W := by
      intro W hWm f hf x hx W₁ j rfl
      rcases mem_union.1 (hvert W hWm (subset_vertexSet hf hx)) with h | h
      · rw [vertexSet_gmap] at h
        obtain ⟨y, -, hy⟩ := mem_map.1 h
        simp [ι] at hy
      · obtain ⟨j', -, hj'⟩ := mem_image.1 h
        simp only [Sum.inr.injEq, Prod.mk.injEq] at hj'
        exact hj'.1.symm
    refine ⟨fun W' hW' => ?_, fun W' hW' => ?_, fun W₁' hW₁' W₂' hW₂' hne => ?_,
      fun W' hW' => ?_, fun W' hW' => ?_⟩
    · obtain ⟨W, hWm, rfl⟩ := mem_image.1 hW'
      simp only [hpre W hWm]
      exact (hAw W hWm).off.rgraph
    · obtain ⟨W, hWm, rfl⟩ := mem_image.1 hW'
      simp only [hpre W hWm]
      rw [disjoint_left]
      intro f hf hfXR
      obtain ⟨j, hj⟩ := hfr W hWm f hf
      rw [← gmap_union] at hfXR
      obtain ⟨f₀, -, rfl⟩ := mem_gmap.1 hfXR
      obtain ⟨y, -, hy⟩ := mem_map.1 hj
      simp [ι] at hy
    · obtain ⟨W₁, hW₁, rfl⟩ := mem_image.1 hW₁'
      obtain ⟨W₂, hW₂, rfl⟩ := mem_image.1 hW₂'
      simp only [hpre W₁ hW₁, hpre W₂ hW₂]
      rw [disjoint_left]
      intro f hf₁ hf₂
      obtain ⟨j, hj⟩ := hfr W₁ hW₁ f hf₁
      exact hne (congrArg _ (htag W₂ hW₂ f hf₂ _ hj W₁ j rfl))
    · obtain ⟨W, hWm, rfl⟩ := mem_image.1 hW'
      simp only [hpre W hWm]
      exact (hAw W hWm).on
    · obtain ⟨W, hWm, rfl⟩ := mem_image.1 hW'
      simp only [hpre W hWm]
      exact (hAw W hWm).off
  · intro W hWm
    simp only [hpre W hWm]
    exact ⟨hAw W hWm, hvert W hWm⟩

end RefinedAbsorption.Absorber17
