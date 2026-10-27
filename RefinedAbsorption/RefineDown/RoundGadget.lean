module
public import RefinedAbsorption.RefineDown.Step
public import RefinedAbsorption.RefineDown.Transport
public import RefinedAbsorption.Placement.Cluster
public import RefinedAbsorption.Placement.PlacedDeg

/-!
# The anti-edge round as gadgets on `Fin n`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (refine-down, Section 4, and the
Partial Clique Embedding Lemma 5.2).  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

Copies are labelled by `Lab n = ℕ × Finset (Fin n)`: the first coordinate is the round in which
the copy was created, the second one is its vertex set.  For the copy `i` the anti-edge step
(`RefineDown.antiEdgeStep`) creates the new edges `Ed j₀ i = A_i ∪ F_i` on new vertices tagged by
`i`.  We read them as one gadget with roots `i.2` and `roundAux q r = (q - r) + m (q - r)`
auxiliary vertices (`roundTemplate`), and we describe the vertex map `psiV Φ` which sends the new
vertices of copy `i` along the placement `Φ i`:

* `newEdges_roundTemplate`: the placed gadget of `i` is the image of `Ed j₀ i` under `psiV Φ`;
* `psiV_injOn_edge`, `psiV_image_injOn`: a valid placement is injective on every new edge and
  does not identify different new edges of the same copy.
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

/-- Copy labels on `Fin n`: creation round and vertex set. -/
abbrev Lab (n : ℕ) := ℕ × Finset (Fin n)

/-- The vertex set of a labelled copy. -/
abbrev labEnds {n : ℕ} : Lab n → Finset (Fin n) := Prod.snd

/-- The number of auxiliary vertices of a round gadget. -/
def roundAux (q r : ℕ) : ℕ := (q - r) + fakeCount q r * (q - r)

/-- Coordinates of the auxiliary vertices of a round gadget. -/
def auxCode (q r : ℕ) : Fin (q - r) ⊕ (Fin (fakeCount q r) × Fin (q - r)) ≃ Fin (roundAux q r) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

instance instDecidableEqFinsetSVLab (n q r : ℕ) :
    DecidableEq (Finset (SV (Fin n) (Lab n) q r)) :=
  @Finset.decidableEq _ (inferInstance : DecidableEq (SV (Fin n) (Lab n) q r))

variable {n q r : ℕ}

/-- The template coordinates of a vertex of the abstract step (the tag is forgotten). -/
def betaV : SV (Fin n) (Lab n) q r → Fin n ⊕ Fin (roundAux q r)
  | Sum.inl v => Sum.inl v
  | Sum.inr (Sum.inl _, _, t) => Sum.inr (auxCode q r (Sum.inl t))
  | Sum.inr (Sum.inr _, j, t) => Sum.inr (auxCode q r (Sum.inr (j, t)))

/-- The vertex map of a placed round: old vertices are fixed, the new vertices of the copy `i`
follow `Φ i`. -/
def psiV (Φ : Lab n → Fin (roundAux q r) → Fin n) : SV (Fin n) (Lab n) q r → Fin n
  | Sum.inl v => v
  | Sum.inr (Sum.inl i, _, t) => Φ i (auxCode q r (Sum.inl t))
  | Sum.inr (Sum.inr i, j, t) => Φ i (auxCode q r (Sum.inr (j, t)))

/-- The vertices that may occur in a new edge of the copy `i`. -/
def Good (j₀ : Fin (fakeCount q r)) (i : Lab n) : SV (Fin n) (Lab n) q r → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl i', j, _) => i' = i ∧ j = j₀
  | Sum.inr (Sum.inr i', _, _) => i' = i

/-- The new edges of the copy `i`: anti-edge and fake edge. -/
def Ed (q r : ℕ) (j₀ : Fin (fakeCount q r)) (i : Lab n) : Finset (Finset (SV (Fin n) (Lab n) q r)) :=
  antiE q r labEnds j₀ i ∪ fakeE q r labEnds i

/-- **The round gadget** of the copy `i`. -/
def roundTemplate (q r : ℕ) (j₀ : Fin (fakeCount q r)) (i : Lab n) :
    Finset (Finset (Fin n ⊕ Fin (roundAux q r))) :=
  (Ed q r j₀ i).image fun f => f.image betaV

theorem psiV_eq_emb {Φ : Lab n → Fin (roundAux q r) → Fin n} {j₀ : Fin (fakeCount q r)}
    {i : Lab n} {x : SV (Fin n) (Lab n) q r} (hx : Good j₀ i x) :
    psiV Φ x = emb (Φ i) (betaV x) := by
  rcases x with v | ⟨i' | i', j, t⟩
  · rfl
  · obtain ⟨rfl, -⟩ := hx; rfl
  · cases hx; rfl

theorem betaV_injOn_good {j₀ : Fin (fakeCount q r)} {i : Lab n} :
    Set.InjOn (betaV (n := n) (q := q) (r := r)) {x | Good j₀ i x} := by
  intro x hx y hy hxy
  rcases x with v | ⟨i₁ | i₁, j₁, t₁⟩ <;> rcases y with w | ⟨i₂ | i₂, j₂, t₂⟩ <;>
    simp only [betaV, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq] at hxy ⊢
  · exact hxy
  · obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    exact ⟨rfl, rfl, hxy⟩
  · cases hx; cases hy
    simp_all

theorem good_of_mem_Ed {j₀ : Fin (fakeCount q r)} {i : Lab n}
    {f : Finset (SV (Fin n) (Lab n) q r)} (hf : f ∈ Ed q r j₀ i)
    {x : SV (Fin n) (Lab n) q r} (hx : x ∈ f) : Good j₀ i x := by
  rcases x with v | ⟨i' | i', j, t⟩
  · trivial
  · rcases mem_union.1 hf with hf | hf
    · obtain ⟨h1, h2⟩ := antiPiece_fresh_tag (ends := ends2 labEnds) hf hx
      exact ⟨Sum.inl_injective h1, h2⟩
    · exact absurd (fakeEdge_fresh_tag (ends := ends2 labEnds) hf hx) (by simp)
  · rcases mem_union.1 hf with hf | hf
    · exact absurd (antiPiece_fresh_tag (ends := ends2 labEnds) hf hx).1 (by simp)
    · exact Sum.inr_injective (fakeEdge_fresh_tag (ends := ends2 labEnds) hf hx)

theorem inl_mem_Ed {j₀ : Fin (fakeCount q r)} {i : Lab n}
    {f : Finset (SV (Fin n) (Lab n) q r)} (hf : f ∈ Ed q r j₀ i) {v : Fin n}
    (hv : (Sum.inl v : SV (Fin n) (Lab n) q r) ∈ f) : v ∈ i.2 := by
  rcases mem_union.1 hf with hf | hf
  · exact fakeEdge_inl (ends := ends2 labEnds) (i := Sum.inl i)
      (mem_biUnion.2 ⟨j₀, mem_univ _, hf⟩) hv
  · exact fakeEdge_inl (ends := ends2 labEnds) (i := Sum.inr i) hf hv

theorem card_mem_Ed {j₀ : Fin (fakeCount q r)} {i : Lab n}
    {f : Finset (SV (Fin n) (Lab n) q r)} (hf : f ∈ Ed q r j₀ i) : f.card = r := by
  rcases mem_union.1 hf with hf | hf
  · exact antiE_card_edge hf
  · exact fakeEdge_card_edge hf

theorem fresh_mem_Ed {j₀ : Fin (fakeCount q r)} {i : Lab n} (hi : i.2.card = r)
    {f : Finset (SV (Fin n) (Lab n) q r)} (hf : f ∈ Ed q r j₀ i) :
    ∃ x ∈ f, ∃ p, betaV x = Sum.inr p := by
  rcases mem_union.1 hf with hf | hf
  · obtain ⟨t, ht⟩ := antiE_tag (ends := labEnds) hi hf
    exact ⟨_, ht, _, rfl⟩
  · obtain ⟨j, t, ht⟩ := fakeE_tag (ends := labEnds) hi hf
    exact ⟨_, ht, _, rfl⟩

theorem roundTemplate_wf {j₀ : Fin (fakeCount q r)} {i : Lab n} (hi : i.2.card = r) :
    GadgetWF r r i.2 (roundTemplate q r j₀ i) where
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

theorem placeEdge_image_betaV {Φ : Lab n → Fin (roundAux q r) → Fin n}
    {j₀ : Fin (fakeCount q r)} {i : Lab n} {f : Finset (SV (Fin n) (Lab n) q r)}
    (hf : f ∈ Ed q r j₀ i) : placeEdge (Φ i) (f.image betaV) = f.image (psiV Φ) := by
  unfold placeEdge
  rw [image_image]
  exact image_congr fun x hx => (psiV_eq_emb (good_of_mem_Ed hf hx)).symm

theorem newEdges_roundTemplate {Φ : Lab n → Fin (roundAux q r) → Fin n}
    {j₀ : Fin (fakeCount q r)} (i : Lab n) :
    newEdges (roundTemplate q r j₀ i) (Φ i) = (Ed q r j₀ i).image fun f => f.image (psiV Φ) := by
  unfold newEdges roundTemplate
  rw [image_image]
  exact image_congr fun f hf => placeEdge_image_betaV hf

/-- A valid placement is injective on every new edge of its copy. -/
theorem psiV_injOn_edge {Φ : Lab n → Fin (roundAux q r) → Fin n} {j₀ : Fin (fakeCount q r)}
    {i : Lab n} (hv : ValidPlacement i.2 (Φ i)) {f : Finset (SV (Fin n) (Lab n) q r)}
    (hf : f ∈ Ed q r j₀ i) : Set.InjOn (psiV Φ) f := by
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
theorem psiV_image_injOn {Φ : Lab n → Fin (roundAux q r) → Fin n} {j₀ : Fin (fakeCount q r)}
    {i : Lab n} (hi : i.2.card = r) (hv : ValidPlacement i.2 (Φ i)) :
    Set.InjOn (fun f : Finset (SV (Fin n) (Lab n) q r) => f.image (psiV Φ))
      (Ed q r j₀ i : Set (Finset (SV (Fin n) (Lab n) q r))) := by
  intro f hf f' hf' hff'
  have h1 := placeEdge_image_betaV (Φ := Φ) (mem_coe.1 hf)
  have h2 := placeEdge_image_betaV (Φ := Φ) (mem_coe.1 hf')
  have hpl := placeEdge_injOn (roundTemplate_wf (j₀ := j₀) hi) hv
    (mem_image_of_mem _ (mem_coe.1 hf)) (mem_image_of_mem _ (mem_coe.1 hf'))
    (h1.trans (hff'.trans h2.symm))
  have hgood : Set.InjOn (betaV (n := n) (q := q) (r := r)) ((f ∪ f' : Finset _) : Set _) :=
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

end RefinedAbsorption.RefineDown
