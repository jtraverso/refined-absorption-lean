module
public import RequestProject.Placement.Counting

/-!
# Degrees in a placed gadget

A valid placement is injective on every template edge and on the whole template support, so the
degree of a set `S ⊆ Fin n` in the placed gadget equals the degree of its pull-back `S''` in the
template (`deg_newEdges_eq`).  Consequently any degree congruence of the template that only
depends on whether `S''` lies inside the roots transfers to the placed gadget
(`deg_newEdges_cast`).  This is what keeps divisibility when fake edges are placed inside
`K_n^r` with shared vertices.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ}

/-- The pull-back of `S ⊆ Fin n` to the template vertex type of a placement. -/
def pullback (R : Finset (Fin n)) (φ : Fin h → Fin n) (S : Finset (Fin n)) :
    Finset (Fin n ⊕ Fin h) :=
  (S.filter (· ∈ R)).map Function.Embedding.inl ∪
    (univ.filter fun p => φ p ∈ S).map Function.Embedding.inr

theorem mem_pullback_inl {R : Finset (Fin n)} {φ : Fin h → Fin n} {S : Finset (Fin n)}
    {a : Fin n} : (Sum.inl a : Fin n ⊕ Fin h) ∈ pullback R φ S ↔ a ∈ S ∧ a ∈ R := by
  simp [pullback]

theorem mem_pullback_inr {R : Finset (Fin n)} {φ : Fin h → Fin n} {S : Finset (Fin n)}
    {p : Fin h} : (Sum.inr p : Fin n ⊕ Fin h) ∈ pullback R φ S ↔ φ p ∈ S := by
  simp [pullback]

theorem card_pullback {R : Finset (Fin n)} {φ : Fin h → Fin n} (hφ : ValidPlacement R φ)
    {S : Finset (Fin n)} (hS : S ⊆ R ∪ auxImage φ) : (pullback R φ S).card = S.card := by
  unfold pullback
  rw [card_union_of_disjoint (by
    rw [disjoint_left]; intro x hx hx'
    obtain ⟨a, -, rfl⟩ := mem_map.1 hx
    obtain ⟨p, -, hp⟩ := mem_map.1 hx'
    simp at hp), card_map, card_map]
  have h2 : (univ.filter fun p => φ p ∈ S).card = (S.filter (· ∉ R)).card := by
    rw [← card_image_of_injective _ hφ.1]
    congr 1
    ext a
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨hp, hφ.2 p⟩
    · rintro ⟨ha, haR⟩
      rcases mem_union.1 (hS ha) with h1 | h1
      · exact absurd h1 haR
      · obtain ⟨p, -, rfl⟩ := mem_image.1 h1
        exact ⟨p, ha, rfl⟩
  rw [h2, ← card_union_of_disjoint (disjoint_filter_filter_not _ _ _), filter_union_filter_not_eq]

/-- `S ⊆ placeEdge φ t` iff the pull-back of `S` lies in `t`. -/
theorem subset_placeEdge_iff {r k : ℕ} {R : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF r k R T) {φ : Fin h → Fin n} (hφ : ValidPlacement R φ) {t} (ht : t ∈ T)
    {S : Finset (Fin n)} (hS : S ⊆ R ∪ auxImage φ) :
    S ⊆ placeEdge φ t ↔ pullback R φ S ⊆ t := by
  constructor
  · intro hSt x hx
    rcases x with a | p
    · rw [mem_pullback_inl] at hx
      obtain ⟨y, hy, hya⟩ := mem_image.1 (hSt hx.1)
      rcases y with a' | p'
      · simp only [emb, Sum.elim_inl] at hya; subst hya; exact hy
      · simp only [emb, Sum.elim_inr] at hya
        exact absurd (hya ▸ hx.2) (hφ.2 p')
    · rw [mem_pullback_inr] at hx
      obtain ⟨y, hy, hya⟩ := mem_image.1 (hSt hx)
      rcases y with a' | p'
      · simp only [emb, Sum.elim_inl] at hya
        exact absurd (hya ▸ hw.edge_roots t ht a' hy) (hφ.2 p)
      · simp only [emb, Sum.elim_inr] at hya
        rw [← hφ.1 hya]; exact hy
  · intro hSt a ha
    rcases mem_union.1 (hS ha) with h1 | h1
    · exact mem_image.2 ⟨Sum.inl a, hSt (mem_pullback_inl.2 ⟨ha, h1⟩), rfl⟩
    · obtain ⟨p, -, rfl⟩ := mem_image.1 h1
      exact mem_image.2 ⟨Sum.inr p, hSt (mem_pullback_inr.2 ha), rfl⟩

/-- A valid placement does not identify distinct template edges. -/
theorem placeEdge_injOn {r k : ℕ} {R : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF r k R T) {φ : Fin h → Fin n} (hφ : ValidPlacement R φ) :
    Set.InjOn (placeEdge φ) T := by
  intro t ht t' ht' htt'
  have hinj : ∀ s : Finset (Fin n ⊕ Fin h), (∀ a, Sum.inl a ∈ s → a ∈ R) →
      Set.InjOn (emb φ) s := fun s hs =>
    emb_injOn φ univ (fun a _ b _ hab => hφ.1 hab) (fun p _ => hφ.2 p) s hs
      (fun p _ => mem_univ p)
  have hunion := hinj (t ∪ t') (by
    intro a ha
    rcases mem_union.1 ha with h1 | h1
    · exact hw.edge_roots t ht a h1
    · exact hw.edge_roots t' ht' a h1)
  ext x
  constructor
  · intro hx
    have : emb φ x ∈ placeEdge φ t' := htt' ▸ mem_image_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 this
    rw [hunion (mem_union_right _ hy) (mem_union_left _ hx) hyx] at hy
    exact hy
  · intro hx
    have : emb φ x ∈ placeEdge φ t := htt'.symm ▸ mem_image_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 this
    rw [hunion (mem_union_left _ hy) (mem_union_right _ hx) hyx] at hy
    exact hy

theorem card_newEdges {r k : ℕ} {R : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF r k R T) {φ : Fin h → Fin n} (hφ : ValidPlacement R φ) :
    (newEdges T φ).card = T.card :=
  card_image_of_injOn (placeEdge_injOn hw hφ)

/-- Every placed edge is an `r`-set. -/
theorem card_of_mem_newEdges {r k : ℕ} {R : Finset (Fin n)}
    {T : Finset (Finset (Fin n ⊕ Fin h))} (hw : GadgetWF r k R T) {φ : Fin h → Fin n}
    (hφ : ValidPlacement R φ) {f : Finset (Fin n)} (hf : f ∈ newEdges T φ) : f.card = r := by
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hf
  unfold placeEdge
  rw [card_image_of_injOn (emb_injOn φ univ (fun a _ b _ hab => hφ.1 hab) (fun p _ => hφ.2 p) t
    (hw.edge_roots t ht) (fun p _ => mem_univ p)), hw.edge_card t ht]

/-- **Degrees transfer along a valid placement.** -/
theorem deg_newEdges_eq {r k : ℕ} {R : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF r k R T) {φ : Fin h → Fin n} (hφ : ValidPlacement R φ) {S : Finset (Fin n)}
    (hS : S ⊆ R ∪ auxImage φ) : deg (newEdges T φ) S = deg T (pullback R φ S) := by
  unfold deg newEdges
  rw [filter_image, card_image_of_injOn ((placeEdge_injOn hw hφ).mono (filter_subset _ _))]
  congr 1
  exact filter_congr fun t ht => subset_placeEdge_iff hw hφ ht hS

theorem deg_newEdges_eq_zero {r k : ℕ} {R : Finset (Fin n)}
    {T : Finset (Finset (Fin n ⊕ Fin h))} (hw : GadgetWF r k R T) (φ : Fin h → Fin n)
    {S : Finset (Fin n)} (hS : ¬ S ⊆ R ∪ auxImage φ) : deg (newEdges T φ) S = 0 := by
  unfold deg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro f hf hSf
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hf
  exact hS (hSf.trans (placeEdge_subset hw φ ht))

/-- **Degree congruences transfer along a valid placement.**  If, modulo `b`, the degree of every
template set of size `|S|` is `1` or `0` according to whether it lies inside the roots, then the
same holds for `S` in the placed gadget. -/
theorem deg_newEdges_cast {r k : ℕ} {R : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF r k R T) {φ : Fin h → Fin n} (hφ : ValidPlacement R φ) (S : Finset (Fin n))
    (b : ℕ) (hT : ∀ S'' : Finset (Fin n ⊕ Fin h), S''.card = S.card →
      ((deg T S'' : ℕ) : ZMod b) = if S'' ⊆ R.map Function.Embedding.inl then 1 else 0) :
    ((deg (newEdges T φ) S : ℕ) : ZMod b) = if S ⊆ R then 1 else 0 := by
  by_cases hS : S ⊆ R ∪ auxImage φ
  · rw [deg_newEdges_eq hw hφ hS, hT _ (card_pullback hφ hS)]
    congr 1
    apply propext
    constructor
    · intro h a ha
      rcases mem_union.1 (hS ha) with h1 | h1
      · exact h1
      · obtain ⟨p, -, rfl⟩ := mem_image.1 h1
        have := h (mem_pullback_inr.2 ha)
        obtain ⟨b', -, hb'⟩ := mem_map.1 this
        simp at hb'
    · intro h x hx
      rcases x with a | p
      · rw [mem_pullback_inl] at hx
        exact mem_map_of_mem _ hx.2
      · rw [mem_pullback_inr] at hx
        exact absurd (h hx) (hφ.2 p)
  · rw [deg_newEdges_eq_zero hw φ hS, if_neg (fun h => hS (h.trans subset_union_left))]
    simp

end RefinedAbsorption.Placement
