module
public import RequestProject.RefineDown.RoundGadget

/-!
# The anti-edge round as gadgets, for an arbitrary label type

The same construction as `RoundGadget.lean`, with copies labelled by an arbitrary type `E` and
vertex sets given by `ends : E → Finset (Fin n)` (instead of `Lab n` and `labEnds`).  This is
needed for multigraph rounds, where parallel copies cannot be told apart by their vertex sets.
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown.Gen

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.RefineDown

instance instDecidableEqFinsetSVGen (n q r : ℕ) (E : Type) [DecidableEq E] :
    DecidableEq (Finset (SV (Fin n) E q r)) :=
  @Finset.decidableEq _ (inferInstance : DecidableEq (SV (Fin n) E q r))

variable {n q r : ℕ} {E : Type} [DecidableEq E]

/-- The template coordinates of a vertex of the abstract step (the tag is forgotten). -/
def betaV : SV (Fin n) E q r → Fin n ⊕ Fin (roundAux q r)
  | Sum.inl v => Sum.inl v
  | Sum.inr (Sum.inl _, _, t) => Sum.inr (auxCode q r (Sum.inl t))
  | Sum.inr (Sum.inr _, j, t) => Sum.inr (auxCode q r (Sum.inr (j, t)))

/-- The vertex map of a placed round: old vertices are fixed, the new vertices of the copy `i`
follow `Φ i`. -/
def psiV (Φ : E → Fin (roundAux q r) → Fin n) : SV (Fin n) E q r → Fin n
  | Sum.inl v => v
  | Sum.inr (Sum.inl i, _, t) => Φ i (auxCode q r (Sum.inl t))
  | Sum.inr (Sum.inr i, j, t) => Φ i (auxCode q r (Sum.inr (j, t)))

/-- The vertices that may occur in a new edge of the copy `i`. -/
def Good (j₀ : Fin (fakeCount q r)) (i : E) : SV (Fin n) E q r → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl i', j, _) => i' = i ∧ j = j₀
  | Sum.inr (Sum.inr i', _, _) => i' = i

/-- The new edges of the copy `i`: anti-edge and fake edge. -/
def Ed (q r : ℕ) (ends : E → Finset (Fin n)) (j₀ : Fin (fakeCount q r)) (i : E) : Finset (Finset (SV (Fin n) E q r)) :=
  antiE q r ends j₀ i ∪ fakeE q r ends i

/-- **The round gadget** of the copy `i`. -/
def roundTemplate (q r : ℕ) (ends : E → Finset (Fin n)) (j₀ : Fin (fakeCount q r)) (i : E) :
    Finset (Finset (Fin n ⊕ Fin (roundAux q r))) :=
  (Ed q r ends j₀ i).image fun f => f.image betaV

omit [DecidableEq E] in
theorem psiV_eq_emb {Φ : E → Fin (roundAux q r) → Fin n} {j₀ : Fin (fakeCount q r)}
    {i : E} {x : SV (Fin n) E q r} (hx : Good j₀ i x) :
    psiV Φ x = emb (Φ i) (betaV x) := by
  rcases x with v | ⟨i' | i', j, t⟩
  · rfl
  · obtain ⟨rfl, -⟩ := hx; rfl
  · cases hx; rfl

omit [DecidableEq E] in
theorem betaV_injOn_good {j₀ : Fin (fakeCount q r)} {i : E} :
    Set.InjOn (betaV (n := n) (q := q) (r := r) (E := E)) {x | Good j₀ i x} := by
  intro x hx y hy hxy
  rcases x with v | ⟨i₁ | i₁, j₁, t₁⟩ <;> rcases y with w | ⟨i₂ | i₂, j₂, t₂⟩ <;>
    simp only [betaV, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq] at hxy ⊢
  · exact hxy
  · obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    exact ⟨rfl, rfl, hxy⟩
  · cases hx; cases hy
    simp_all

theorem good_of_mem_Ed {j₀ : Fin (fakeCount q r)} {i : E}
    {f : Finset (SV (Fin n) E q r)} (hf : f ∈ Ed q r ends j₀ i)
    {x : SV (Fin n) E q r} (hx : x ∈ f) : Good j₀ i x := by
  rcases x with v | ⟨i' | i', j, t⟩
  · trivial
  · rcases mem_union.1 hf with hf | hf
    · obtain ⟨h1, h2⟩ := antiPiece_fresh_tag (ends := ends2 ends) hf hx
      exact ⟨Sum.inl_injective h1, h2⟩
    · exact absurd (fakeEdge_fresh_tag (ends := ends2 ends) hf hx) (by simp)
  · rcases mem_union.1 hf with hf | hf
    · exact absurd (antiPiece_fresh_tag (ends := ends2 ends) hf hx).1 (by simp)
    · exact Sum.inr_injective (fakeEdge_fresh_tag (ends := ends2 ends) hf hx)

theorem inl_mem_Ed {j₀ : Fin (fakeCount q r)} {i : E}
    {f : Finset (SV (Fin n) E q r)} (hf : f ∈ Ed q r ends j₀ i) {v : Fin n}
    (hv : (Sum.inl v : SV (Fin n) E q r) ∈ f) : v ∈ ends i := by
  rcases mem_union.1 hf with hf | hf
  · exact fakeEdge_inl (ends := ends2 ends) (i := Sum.inl i)
      (mem_biUnion.2 ⟨j₀, mem_univ _, hf⟩) hv
  · exact fakeEdge_inl (ends := ends2 ends) (i := Sum.inr i) hf hv

theorem card_mem_Ed {j₀ : Fin (fakeCount q r)} {i : E}
    {f : Finset (SV (Fin n) E q r)} (hf : f ∈ Ed q r ends j₀ i) : f.card = r := by
  rcases mem_union.1 hf with hf | hf
  · exact antiE_card_edge hf
  · exact fakeEdge_card_edge hf

theorem fresh_mem_Ed {j₀ : Fin (fakeCount q r)} {i : E} (hi : (ends i).card = r)
    {f : Finset (SV (Fin n) E q r)} (hf : f ∈ Ed q r ends j₀ i) :
    ∃ x ∈ f, ∃ p, betaV x = Sum.inr p := by
  rcases mem_union.1 hf with hf | hf
  · obtain ⟨t, ht⟩ := antiE_tag (ends := ends) hi hf
    exact ⟨_, ht, _, rfl⟩
  · obtain ⟨j, t, ht⟩ := fakeE_tag (ends := ends) hi hf
    exact ⟨_, ht, _, rfl⟩

theorem roundTemplate_wf {j₀ : Fin (fakeCount q r)} {i : E} (hi : (ends i).card = r) :
    GadgetWF r r (ends i) (roundTemplate q r ends j₀ i) where
  roots_le := hi.le
  roots_ge := by omega
  edge_card := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := mem_image.1 ht
    rw [card_image_of_injOn (betaV_injOn_good.mono fun x hx => good_of_mem_Ed hf hx),
      card_mem_Ed hf]
  edge_roots := by
    intro t ht a ha
    obtain ⟨f, hf, rfl⟩ := mem_image.1 ht
    obtain ⟨x, hx, hxa⟩ := mem_image.1 ha
    rcases x with v | ⟨i' | i', j, s⟩
    · cases hxa; exact inl_mem_Ed hf hx
    · simp [betaV] at hxa
    · simp [betaV] at hxa
  edge_aux := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := mem_image.1 ht
    obtain ⟨x, hx, p, hp⟩ := fresh_mem_Ed hi hf
    exact ⟨p, mem_image.2 ⟨x, hx, hp⟩⟩

theorem placeEdge_image_betaV {Φ : E → Fin (roundAux q r) → Fin n}
    {j₀ : Fin (fakeCount q r)} {i : E} {f : Finset (SV (Fin n) E q r)}
    (hf : f ∈ Ed q r ends j₀ i) : placeEdge (Φ i) (f.image betaV) = f.image (psiV Φ) := by
  unfold placeEdge
  rw [image_image]
  exact image_congr fun x hx => (psiV_eq_emb (good_of_mem_Ed hf hx)).symm

theorem newEdges_roundTemplate {Φ : E → Fin (roundAux q r) → Fin n}
    {j₀ : Fin (fakeCount q r)} (i : E) :
    newEdges (roundTemplate q r ends j₀ i) (Φ i) = (Ed q r ends j₀ i).image fun f => f.image (psiV Φ) := by
  unfold newEdges roundTemplate
  rw [image_image]
  exact image_congr fun f hf => placeEdge_image_betaV hf

/-- A valid placement is injective on every new edge of its copy. -/
theorem psiV_injOn_edge {Φ : E → Fin (roundAux q r) → Fin n} {j₀ : Fin (fakeCount q r)}
    {i : E} (hv : ValidPlacement (ends i) (Φ i)) {f : Finset (SV (Fin n) E q r)}
    (hf : f ∈ Ed q r ends j₀ i) : Set.InjOn (psiV Φ) f := by
  intro x hx y hy hxy
  rw [psiV_eq_emb (good_of_mem_Ed hf hx), psiV_eq_emb (good_of_mem_Ed hf hy)] at hxy
  have hemb : Set.InjOn (emb (Φ i)) ((f.image betaV : Finset _) : Set _) :=
    emb_injOn (Φ i) univ (fun a _ b _ hab => hv.1 hab) (fun p _ => hv.2 p) _
      (fun a ha => by
        obtain ⟨z, hz, hza⟩ := mem_image.1 ha
        rcases z with w | ⟨i' | i', j, s⟩
        · cases hza; exact inl_mem_Ed hf hz
        · simp [betaV] at hza
        · simp [betaV] at hza)
      (fun p _ => mem_univ p)
  exact betaV_injOn_good (good_of_mem_Ed hf hx) (good_of_mem_Ed hf hy)
    (hemb (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) hxy)

/-- A valid placement does not identify different new edges of the same copy. -/
theorem psiV_image_injOn {Φ : E → Fin (roundAux q r) → Fin n} {j₀ : Fin (fakeCount q r)}
    {i : E} (hi : (ends i).card = r) (hv : ValidPlacement (ends i) (Φ i)) :
    Set.InjOn (fun f : Finset (SV (Fin n) E q r) => f.image (psiV Φ))
      (Ed q r ends j₀ i : Set (Finset (SV (Fin n) E q r))) := by
  intro f hf f' hf' hff'
  have h1 := placeEdge_image_betaV (Φ := Φ) (mem_coe.1 hf)
  have h2 := placeEdge_image_betaV (Φ := Φ) (mem_coe.1 hf')
  have hpl := placeEdge_injOn (roundTemplate_wf (ends := ends) (j₀ := j₀) hi) hv
    (mem_image_of_mem _ (mem_coe.1 hf)) (mem_image_of_mem _ (mem_coe.1 hf'))
    (h1.trans (hff'.trans h2.symm))
  have hgood : Set.InjOn (betaV (n := n) (q := q) (r := r) (E := E)) ((f ∪ f' : Finset _) : Set _) :=
    betaV_injOn_good.mono fun x hx => by
      rcases mem_union.1 (mem_coe.1 hx) with hx | hx
      · exact good_of_mem_Ed (mem_coe.1 hf) hx
      · exact good_of_mem_Ed (mem_coe.1 hf') hx
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 (hpl ▸ mem_image_of_mem betaV hx)
    rw [← hgood (mem_union_right _ hy) (mem_union_left _ hx) hyx]; exact hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 (hpl.symm ▸ mem_image_of_mem betaV hx)
    rw [← hgood (mem_union_left _ hy) (mem_union_right _ hx) hyx]; exact hy

end RefinedAbsorption.RefineDown.Gen
