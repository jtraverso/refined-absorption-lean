module
public import RequestProject.Absorber17.Construction
public import RequestProject.GJW.Main

/-!
# Theorem 1.7: existence of absorbers

Every `K_q^r`-divisible `r`-graph `L` (`q > r ≥ 1`) has a `K_q^r`-absorber.

Proof: pad `L` with two vertex-disjoint `q`-cliques on new vertices (so that the vertex count
condition of the Graver–Jurkat–Wilson theorem holds), take a multi-absorber from the
Graver–Jurkat–Wilson theorem, turn it into an absorber with anti-edges and anti-clique absorbers
(`Construction.lean`), and finally remove the padding (`IsAbsorber.pad`) and move everything to
`Fin N`.
-/

@[expose] public section

namespace RefinedAbsorption.Absorber17

open Finset

/-! ### From multisets of cliques to indexed families -/

theorem card_filter_get {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    (univ.filter (fun i : Fin l.length => p (l.get i))).card = l.countP (fun b => decide (p b)) := by
  rw [card_filter, ← List.sum_ofFn]
  have : List.ofFn (fun i : Fin l.length => if p (l.get i) then 1 else 0) =
      l.map (fun x => if p x then 1 else 0) := by
    conv_rhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]; rfl
  rw [this]
  clear this
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a <;> simp [h, Nat.add_comm]

theorem multiset_card_filter {α : Type} (Q : Multiset α) (p : α → Prop) [DecidablePred p] :
    (Q.filter p).card = (univ.filter (fun i : Fin Q.toList.length => p (Q.toList.get i))).card := by
  rw [card_filter_get, ← Multiset.countP_eq_card_filter]
  have := Multiset.coe_countP p Q.toList
  rw [Multiset.coe_toList] at this
  exact this

/-- An enumeration of a `q`-set. -/
noncomputable def enumEmb {W : Type} [DecidableEq W] {q : ℕ} (Q : Finset W) (h : Q.card = q) :
    Fin q ↪ W :=
  ⟨fun s => (Q.equivFin.symm (Fin.cast h.symm s) : W), fun s t hst => by
    have := Q.equivFin.symm.injective (Subtype.val_injective hst)
    exact Fin.cast_injective _ this⟩

theorem map_enumEmb {W : Type} [DecidableEq W] {q : ℕ} (Q : Finset W) (h : Q.card = q) :
    univ.map (enumEmb Q h) = Q := by
  ext x
  simp only [mem_map, mem_univ, true_and, enumEmb, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨s, rfl⟩; exact (Q.equivFin.symm _).2
  · intro hx
    refine ⟨Fin.cast h (Q.equivFin ⟨x, hx⟩), ?_⟩
    change ((Q.equivFin.symm (Fin.cast h.symm (Fin.cast h (Q.equivFin ⟨x, hx⟩)))) : W) = x
    simp

/-- The indexed presentation of a multi-absorber. -/
noncomputable def multiDataOf {W : Type} [DecidableEq W] {q r : ℕ} {L : Finset (Finset W)}
    {A : Finset W → ℕ} (Q₁ Q₂ : Multiset (Finset W))
    (h₁ : IsMultiDecomposition q r (fun e => A e + if e ∈ L then 1 else 0) Q₁)
    (h₂ : IsMultiDecomposition q r A Q₂) : MultiData q r W L where
  k₁ := Q₁.toList.length
  k₂ := Q₂.toList.length
  A := A
  P i := enumEmb (Q₁.toList.get i) (h₁.1 _ (Multiset.mem_toList.1 (List.get_mem _ _)))
  M j := enumEmb (Q₂.toList.get j) (h₂.1 _ (Multiset.mem_toList.1 (List.get_mem _ _)))
  cntP e he := by
    simp only [map_enumEmb]
    rw [← multiset_card_filter]
    exact h₁.2 e he
  cntM e he := by
    simp only [map_enumEmb]
    rw [← multiset_card_filter]
    exact h₂.2 e he

/-! ### Padding by two cliques -/

/-- Vertices of `L` together with two disjoint `q`-sets of new vertices. -/
abbrev PadV (m q : ℕ) : Type := Fin m ⊕ (Bool × Fin q)

def Qb (m q : ℕ) (b : Bool) : Finset (PadV m q) := univ.image (fun s => Sum.inr (b, s))

def Gpad (m q r : ℕ) : Finset (Finset (PadV m q)) := univ.biUnion (fun b => cliqueEdges r (Qb m q b))

theorem card_Qb (m q : ℕ) (b : Bool) : (Qb m q b).card = q := by
  rw [Qb, card_image_of_injective _ (fun s t h => by simpa using h), card_univ, Fintype.card_fin]

theorem mem_Qb {m q : ℕ} {b : Bool} {x : PadV m q} : x ∈ Qb m q b ↔ ∃ s, x = Sum.inr (b, s) := by
  simp only [Qb, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩; exact ⟨s, rfl⟩

theorem Gpad_rgraph (m q r : ℕ) : IsRGraph r (Gpad m q r) := by
  intro e he
  obtain ⟨b, -, he⟩ := mem_biUnion.1 he
  exact (mem_powersetCard.1 he).2

theorem Gpad_vertex {m q r : ℕ} (hr : 1 ≤ r) {e : Finset (PadV m q)} (he : e ∈ Gpad m q r) :
    ∃ b s, (Sum.inr (b, s) : PadV m q) ∈ e := by
  obtain ⟨b, -, he⟩ := mem_biUnion.1 he
  obtain ⟨hsub, hc⟩ := mem_powersetCard.1 he
  obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < e.card)
  obtain ⟨s, rfl⟩ := mem_Qb.1 (hsub hx)
  exact ⟨b, s, hx⟩

theorem Gpad_dec {m q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) : HasDecomposition q r (Gpad m q r) := by
  refine HasDecomposition.biUnion' hrq _ _ (fun b _ b' _ hne => ?_)
    (fun b _ => ⟨_, isDecomposition_singleton (card_Qb m q b)⟩)
  rw [disjoint_left]
  intro e he he'
  obtain ⟨hsub, hc⟩ := mem_powersetCard.1 he
  obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < e.card)
  obtain ⟨s, rfl⟩ := mem_Qb.1 (hsub hx)
  obtain ⟨s', hs'⟩ := mem_Qb.1 ((mem_powersetCard.1 he').1 hx)
  simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
  exact hne hs'.1

theorem exists_edge_through {W : Type} [DecidableEq W] {r : ℕ} (hr : 1 ≤ r) {Q : Finset W}
    (hQ : r ≤ Q.card) {v : W} (hv : v ∈ Q) : ∃ e ∈ cliqueEdges r Q, v ∈ e := by
  obtain ⟨u, hvu, huQ, hu⟩ := exists_subsuperset_card_eq (s := {v}) (t := Q) (n := r)
    (singleton_subset_iff.2 hv) (by simpa using hr) hQ
  exact ⟨u, mem_powersetCard.2 ⟨huQ, hu⟩, hvu (mem_singleton_self v)⟩

theorem Qb_subset_vertexSet {m q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (b : Bool) :
    Qb m q b ⊆ vertexSet (Gpad m q r) := by
  intro v hv
  obtain ⟨e, he, hve⟩ := exists_edge_through hr (by rw [card_Qb]; exact hrq) hv
  exact subset_vertexSet (mem_biUnion.2 ⟨b, mem_univ _, he⟩) hve

theorem card_vertexSet_pad {m q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (L₀ : Finset (Finset (PadV m q))) :
    q + r ≤ (vertexSet (L₀ ∪ Gpad m q r)).card := by
  have hsub : Qb m q false ∪ Qb m q true ⊆ vertexSet (L₀ ∪ Gpad m q r) := by
    rw [vertexSet_union]
    exact union_subset ((Qb_subset_vertexSet hr hrq false).trans subset_union_right)
      ((Qb_subset_vertexSet hr hrq true).trans subset_union_right)
  have hdisj : Disjoint (Qb m q false) (Qb m q true) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨s, rfl⟩ := mem_Qb.1 hx
    obtain ⟨s', hs'⟩ := mem_Qb.1 hx'
    simp at hs'
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_Qb, card_Qb] at this
  omega

theorem gmap_gmap {U₁ U₂ U₃ : Type*} [DecidableEq U₁] [DecidableEq U₂] [DecidableEq U₃]
    (f : U₁ ↪ U₂) (g : U₂ ↪ U₃) (G : Finset (Finset U₁)) :
    gmap g (gmap f G) = gmap (f.trans g) G := by
  ext e
  simp only [mem_gmap]
  constructor
  · rintro ⟨e₁, ⟨e₀, he₀, rfl⟩, rfl⟩
    exact ⟨e₀, he₀, by rw [map_map]⟩
  · rintro ⟨e₀, he₀, rfl⟩
    exact ⟨e₀.map f, ⟨e₀, he₀, rfl⟩, by rw [map_map]⟩

theorem inl_inl_not_inr {m q : ℕ} {β : Type*} {x : Fin m} {b : Bool} {s : Fin q} :
    (Sum.inl (Sum.inl x) : PadV m q ⊕ β) ≠ Sum.inl (Sum.inr (b, s)) := by simp

set_option synthInstance.maxSize 1024 in
/-- **Theorem 1.7 (existence of absorbers).** -/
theorem absorberExistence : AbsorberExistence := by
  intro q r hr hrq m L hL hdiv
  have hL₀r : IsRGraph r (gmap (Function.Embedding.inl : Fin m ↪ PadV m q) L) := hL.gmap _
  have hL₀d : IsDivisible q r (gmap (Function.Embedding.inl : Fin m ↪ PadV m q) L) := hdiv.gmap _
  have hdisj : Disjoint (gmap (Function.Embedding.inl : Fin m ↪ PadV m q) L) (Gpad m q r) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨b, s, hbs⟩ := Gpad_vertex hr he'
    obtain ⟨e₀, -, rfl⟩ := mem_gmap.1 he
    obtain ⟨x, -, hx⟩ := mem_map.1 hbs
    simp at hx
  have hL'r : IsRGraph r (gmap (Function.Embedding.inl : Fin m ↪ PadV m q) L ∪ Gpad m q r) := by
    intro e he
    rcases mem_union.1 he with he | he
    · exact hL₀r e he
    · exact Gpad_rgraph m q r e he
  have hL'd : IsDivisible q r (gmap (Function.Embedding.inl : Fin m ↪ PadV m q) L ∪ Gpad m q r) :=
    hL₀d.union hdisj (Gpad_dec hr hrq.le).isDivisible
  obtain ⟨A, -, ⟨Q₁, h₁⟩, ⟨Q₂, h₂⟩⟩ := exists_multiAbsorber_of_graverJurkatWilson
    graverJurkatWilson hr hrq hL'r hL'd (card_vertexSet_pad hr hrq.le _)
  obtain ⟨Z⟩ := exists_ACAbsorber hrq.le
  haveI : DecidableEq Z.T := Z.deq
  have D := multiDataOf Q₁ Q₂ h₁ h₂
  have hAbs := isAbsorber_Abs D Z hrq hL'r hL'd
  rw [Lc, gmap_union] at hAbs
  have hGdec : HasDecomposition q r (gmap (Function.Embedding.inl :
      PadV m q ↪ VT D Z) (Gpad m q r)) := by
    obtain ⟨𝒬, h𝒬⟩ := Gpad_dec (m := m) hr hrq.le
    exact ⟨_, h𝒬.gmap _⟩
  have hind : ∀ e ∈ gmap (Function.Embedding.inl :
      PadV m q ↪ VT D Z) (Gpad m q r),
      ¬ e ⊆ vertexSet (gmap (Function.Embedding.inl : PadV m q ↪ VT D Z)
        (gmap (Function.Embedding.inl : Fin m ↪ PadV m q) L)) := by
    intro e he hsub
    obtain ⟨e₀, he₀, rfl⟩ := mem_gmap.1 he
    obtain ⟨b, s, hbs⟩ := Gpad_vertex hr he₀
    have := hsub (mem_map_of_mem _ hbs)
    rw [vertexSet_gmap] at this
    obtain ⟨y, hy, hy'⟩ := mem_map.1 this
    rw [vertexSet_gmap] at hy
    obtain ⟨x, -, rfl⟩ := mem_map.1 hy
    exact inl_inl_not_inr hy'
  have hpad := hAbs.pad hrq.le (hL₀d.gmap _) hGdec hind
  have hmove := hpad.gmap (Equiv.sumAssoc (Fin m) (Bool × Fin q)
    ((Finset (PadV m q) × Fin (D.k₁ + 1) × Fin (q - r)) ⊕ ((Fin D.k₁ ⊕ Fin D.k₂) × Z.T))).toEmbedding
  rw [gmap_gmap, gmap_gmap] at hmove
  have hemb : Function.Embedding.inl.trans (Function.Embedding.inl.trans
      (Equiv.sumAssoc (Fin m) (Bool × Fin q)
    ((Finset (PadV m q) × Fin (D.k₁ + 1) × Fin (q - r)) ⊕ ((Fin D.k₁ ⊕ Fin D.k₂) × Z.T))).toEmbedding) =
      (Function.Embedding.inl : Fin m ↪ Fin m ⊕ _) := by
    ext x
    simp
  rw [hemb] at hmove
  exact absorber_on_fin hmove

end RefinedAbsorption.Absorber17
