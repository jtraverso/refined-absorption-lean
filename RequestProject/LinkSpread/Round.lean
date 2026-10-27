module
public import RequestProject.RefineDown.MultiRound

/-!
# The anti-edge round for all link graphs at once (tagged round)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, Lemma 5.2).  Lean
formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The link refiners required by `PlacedLinkLevelE q r i` must be built for **all** outside parts `T`
simultaneously, spread over the reserve: what is measured is the `(r-1)`-degree of the *lifted*
copies `T ∪ y`, summed over all `T`.  This file does this for the first move of any refiner
construction, the anti-edge round.

We work with a *tagged* multigraph: every copy `x` has a body `bd x` (a `k`-set, the link copy) and
a tag `tg x` (an `i`-set disjoint from the body, the outside part).  The lifted copy is
`tg x ∪ bd x`, an `(i + k)`-set.  The round is the `K_q^k` anti-edge round of the bodies
(`antiEdgeStep`), but its gadgets are placed **once, for all copies of all tags**, with the
Partial Clique Embedding Lemma in uniformity `i + k`: the template edges are lifted by the tag
(`liftTemplate`), so the loads that are controlled are those of the lifted new edges.

`taggedRound`: there is `C` such that for every tagged multigraph whose lifted copies are not too
dense compared to a reserve `Z`, there is one global placement of the round with all new vertices in
`Z` such that

* for **every** sub-multigraph `X₀ ⊆ X` (in particular, for every fibre `{x : tg x = T}`) the
  round of `X₀` is a residual `K_q^k`-refiner of the bodies of `X₀`, with residue in its new
  copies;
* every new copy of `x` lies in `bd x ∪ A x` and meets `A x`, where `A x ⊆ Z` are the new vertices
  of `x`;
* the lifted new copies `tg x ∪ f` have `(i + k - 1)`-degrees at most `C · D`, summed over all
  copies of all tags, and so do the lifted gadget vertex sets `tg x ∪ bd x ∪ A x`.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.RefineDown

variable {n h : ℕ}

/-- Lifting a gadget template by a fixed set `A` of roots: every template edge gets `A` added. -/
def liftTemplate (A : Finset (Fin n)) (T : Finset (Finset (Fin n ⊕ Fin h))) :
    Finset (Finset (Fin n ⊕ Fin h)) :=
  T.image fun t => t ∪ A.map Function.Embedding.inl

theorem placeEdge_union_inl (φ : Fin h → Fin n) (t : Finset (Fin n ⊕ Fin h))
    (A : Finset (Fin n)) : placeEdge φ (t ∪ A.map Function.Embedding.inl) = placeEdge φ t ∪ A := by
  unfold placeEdge
  rw [image_union]
  congr 1
  ext a
  simp [emb]

theorem newEdges_liftTemplate (φ : Fin h → Fin n) (A : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) :
    newEdges (liftTemplate A T) φ = (newEdges T φ).image fun e => e ∪ A := by
  unfold newEdges liftTemplate
  rw [image_image, image_image]
  exact image_congr fun t _ => placeEdge_union_inl φ t A

/-- A lifted template is well formed in uniformity `i + k`. -/
theorem liftTemplate_wf {k i : ℕ} {R A : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF k k R T) (hA : A.card = i) (hdisj : Disjoint A R) :
    GadgetWF (i + k) (i + k) (A ∪ R) (liftTemplate A T) where
  roots_le := by
    rw [card_union_of_disjoint hdisj, hA]; have := hw.roots_le; omega
  roots_ge := by
    rw [card_union_of_disjoint hdisj, hA]; have := hw.roots_ge; omega
  edge_card := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := mem_image.1 ht
    rw [card_union_of_disjoint, hw.edge_card t₀ ht₀, card_map, hA, Nat.add_comm]
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hx'
    exact disjoint_left.1 hdisj ha (hw.edge_roots t₀ ht₀ a hx)
  edge_roots := by
    intro t ht a ha
    obtain ⟨t₀, ht₀, rfl⟩ := mem_image.1 ht
    rcases mem_union.1 ha with ha | ha
    · exact mem_union_right _ (hw.edge_roots t₀ ht₀ a ha)
    · obtain ⟨b, hb, he⟩ := mem_map.1 ha
      cases he
      exact mem_union_left _ hb
  edge_aux := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := mem_image.1 ht
    obtain ⟨p, hp⟩ := hw.edge_aux t₀ ht₀
    exact ⟨p, mem_union_left _ hp⟩

variable {E : Type} [DecidableEq E]

theorem stepY_subset_stepR {q k : ℕ} (bd : E → Finset (Fin n)) (j₀ : Fin (fakeCount q k))
    (X₀ : Finset E) : stepY q k bd X₀ ⊆ stepR q k bd j₀ X₀ := by
  intro c hc
  obtain ⟨f, hf, rfl⟩ := mem_map.1 hc
  obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
  exact Gen.mem_stepR_iff'.2 ⟨f, rfl, i, hi, mem_union_right _ hfi⟩

set_option maxHeartbeats 1000000 in
/-- **The anti-edge round for all tags at once.**  See the module docstring. -/
theorem taggedRound (q k i : ℕ) (hk : 1 ≤ k) (hkq : k < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (tg bd : E → Finset (Fin n))
      (X : Finset E) (Z : Finset (Fin n)) (D : ℕ),
      (∀ x ∈ X, (bd x).card = k) → (∀ x ∈ X, (tg x).card = i) →
      (∀ x ∈ X, Disjoint (tg x) (bd x)) → C ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ i + k - 1 →
        (X.filter fun x => J ⊆ tg x ∪ bd x).card ≤ D * Z.card ^ (i + k - 1 - J.card)) →
      ∃ (j₀ : Fin (fakeCount q k)) (ends' : SC (Fin n) E q k → Finset (Fin n))
        (A : E → Finset (Fin n)),
        (∀ x, ends' (Sum.inl x) = bd x) ∧
        (∀ X₀ ⊆ X, IsResidualMultiRefiner q k C ends' (X₀.map Function.Embedding.inl)
          (stepR q k bd j₀ X₀) (stepY q k bd X₀) (stepW q k bd j₀ X₀)) ∧
        (∀ x ∈ X, A x ⊆ Z ∧ Disjoint (A x) (tg x ∪ bd x)) ∧
        (∀ x ∈ X, ∀ f ∈ Gen.Ed q k bd j₀ x,
          ends' (Sum.inr f) ⊆ bd x ∪ A x ∧ (ends' (Sum.inr f) ∩ A x).Nonempty) ∧
        (∀ x ∈ X, (pieceP q k bd j₀ x).biUnion ends' ⊆ bd x ∪ A x ∧
          (pieceQ q k bd j₀ x).biUnion ends' ⊆ bd x ∪ A x) ∧
        (∀ S : Finset (Fin n), S.card = i + k - 1 →
          (X.filter fun x => S ⊆ tg x ∪ bd x ∪ A x).card ≤ C * D) ∧
        (∀ S : Finset (Fin n), S.card = i + k - 1 →
          ∑ x ∈ X, ((Gen.Ed q k bd j₀ x).filter fun f => S ⊆ tg x ∪ ends' (Sum.inr f)).card ≤
            C * D) := by
  obtain ⟨Ccl, hCcl, hcl⟩ := multiCliqueEmbedding (i + k) (roundAux q k) (i + k)
  set C₀ := (fakeCount q k + 1) * q.choose k + 2 with hC₀
  refine ⟨C₀ + Ccl + 1, by omega, ?_⟩
  intro n E _ tg bd X Z D hbd htg hdisj hZ hXJ
  have j₀ : Fin (fakeCount q k) := ⟨0, one_le_fakeCount hk hkq⟩
  obtain ⟨Φ, hvalid, hrange, hpdeg, hdeg⟩ := hcl n X (fun x => tg x ∪ bd x)
    (fun x => liftTemplate (tg x) (Gen.roundTemplate q k bd j₀ x)) Z D
    (fun x hx => liftTemplate_wf (Gen.roundTemplate_wf (hbd x hx)) (htg x hx) (hdisj x hx))
    (le_trans (by omega) hZ) (fun J hJ => hXJ J hJ)
  have hvalid' : ∀ x ∈ X, ValidPlacement (bd x) (Φ x) :=
    fun x hx => ⟨(hvalid x hx).1, fun p hp => (hvalid x hx).2 p (mem_union_right _ hp)⟩
  set ψ := Gen.psiV (q := q) (r := k) Φ
  set ends' := mapEnds ψ (sends q k bd) with hends'
  have hends'_inl : ∀ x, ends' (Sum.inl x) = bd x := fun x => Gen.image_liftE_psiV' bd Φ x
  have hends'_inr : ∀ f, ends' (Sum.inr f) = f.image ψ := fun f => rfl
  have hsubpv : ∀ x ∈ X, ∀ f ∈ Gen.Ed q k bd j₀ x, f.image ψ ⊆ bd x ∪ auxImage (Φ x) := by
    intro x hx f hf
    have e := Gen.placeEdge_image_betaV (Φ := Φ) hf
    have hs := placeEdge_subset (Gen.roundTemplate_wf (ends := bd) (j₀ := j₀) (hbd x hx)) (Φ x)
      (mem_image_of_mem _ hf)
    rw [e] at hs
    exact hs
  refine ⟨j₀, ends', fun x => auxImage (Φ x), hends'_inl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the round of every sub-multigraph is a residual refiner
    intro X₀ hX₀
    have hA := antiEdgeStep (V := Fin n) (ends := bd) hkq j₀ X₀ (fun x hx => hbd x (hX₀ hx))
    have hYR : stepY q k bd X₀ ⊆ X₀.map Function.Embedding.inl ∪ stepR q k bd j₀ X₀ :=
      (stepY_subset_stepR bd j₀ X₀).trans subset_union_right
    have hinj : ∀ c ∈ X₀.map Function.Embedding.inl ∪ stepR q k bd j₀ X₀,
        Set.InjOn ψ (sends q k bd c) := by
      intro c hc
      rcases c with x | f
      · intro a ha b hb hab
        obtain ⟨v, -, rfl⟩ := mem_map.1 (mem_coe.1 ha)
        obtain ⟨w, -, rfl⟩ := mem_map.1 (mem_coe.1 hb)
        simpa [ψ, Gen.psiV] using hab
      · rcases mem_union.1 hc with hc | hc
        · simp at hc
        · obtain ⟨f', hf', x, hx, hfx⟩ := Gen.mem_stepR_iff'.1 hc
          cases hf'
          exact Gen.psiV_injOn_edge (hvalid' x (hX₀ hx)) hfx
    have hinjX : Set.InjOn ψ ((X₀.map Function.Embedding.inl).biUnion (sends q k bd)) := by
      intro a ha b hb hab
      obtain ⟨c, hc, hac⟩ := mem_biUnion.1 (mem_coe.1 ha)
      obtain ⟨c', hc', hbc'⟩ := mem_biUnion.1 (mem_coe.1 hb)
      obtain ⟨x, -, rfl⟩ := mem_map.1 hc
      obtain ⟨x', -, rfl⟩ := mem_map.1 hc'
      obtain ⟨v, -, rfl⟩ := mem_map.1 hac
      obtain ⟨w, -, rfl⟩ := mem_map.1 hbc'
      simpa [ψ, Gen.psiV] using hab
    exact (residual_mapEnds hA ψ hinj hinjX hYR).mono (by omega)
  · intro x hx
    refine ⟨fun v hv => ?_, ?_⟩
    · obtain ⟨p, -, rfl⟩ := mem_image.1 hv
      exact hrange x hx p
    · rw [disjoint_left]
      intro v hv hv'
      obtain ⟨p, -, rfl⟩ := mem_image.1 hv
      exact (hvalid x hx).2 p hv'
  · intro x hx f hf
    refine ⟨hsubpv x hx f hf, ?_⟩
    obtain ⟨p, hp⟩ := (Gen.roundTemplate_wf (ends := bd) (j₀ := j₀) (hbd x hx)).edge_aux
      (f.image Gen.betaV) (mem_image_of_mem _ hf)
    refine ⟨Φ x p, mem_inter.2 ⟨?_, mem_image_of_mem _ (mem_univ p)⟩⟩
    rw [hends'_inr, ← Gen.placeEdge_image_betaV hf]
    exact mem_image.2 ⟨Sum.inr p, hp, rfl⟩
  · intro x hx
    have key : ∀ W₀, (W₀ = pieceP q k bd j₀ x ∨ W₀ = pieceQ q k bd j₀ x) →
        W₀.biUnion ends' ⊆ bd x ∪ auxImage (Φ x) := by
      intro W₀ hW₀ v hv
      obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
      rcases c with x' | f
      · have : x' = x := by
          rcases hW₀ with rfl | rfl
          · exact mem_pieceP_inl.1 hc
          · exact absurd hc not_mem_pieceQ_inl
        subst this
        rw [hends'_inl] at hvc
        exact mem_union_left _ hvc
      · have hf : f ∈ Gen.Ed q k bd j₀ x := by
          rcases hW₀ with rfl | rfl
          · exact mem_union_left _ (mem_pieceP_inr.1 hc)
          · exact mem_union.2 (mem_pieceQ_inr.1 hc)
        exact hsubpv x hx f hf hvc
    exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩
  · intro S hS
    exact (hpdeg S hS).trans (Nat.mul_le_mul_right _ (by omega))
  · intro S hS
    refine le_trans ?_ ((hdeg S hS).trans (Nat.mul_le_mul_right _ (by omega)))
    refine sum_le_sum fun x hx => ?_
    have hd : ∀ g ∈ Gen.Ed q k bd j₀ x, Disjoint (g.image ψ) (tg x) := by
      intro g hg
      rw [disjoint_left]
      intro v hv hvt
      rcases mem_union.1 (hsubpv x hx g hg hv) with hv' | hv'
      · exact disjoint_left.1 (hdisj x hx) hvt hv'
      · obtain ⟨p, -, rfl⟩ := mem_image.1 hv'
        exact (hvalid x hx).2 p (mem_union_left _ hvt)
    rw [newEdges_liftTemplate, Gen.newEdges_roundTemplate, image_image]
    refine card_le_card_of_injOn (fun f => f.image ψ ∪ tg x) ?_ ?_
    · intro f hf
      have hf' := mem_filter.1 (mem_coe.1 hf)
      refine mem_filter.2 ⟨mem_image.2 ⟨f, hf'.1, rfl⟩, ?_⟩
      have := hf'.2
      rw [hends'_inr, union_comm] at this
      exact this
    · intro f hf f' hf' hff'
      have hf1 := (mem_filter.1 (mem_coe.1 hf)).1
      have hf1' := (mem_filter.1 (mem_coe.1 hf')).1
      have e1 : f.image ψ = f'.image ψ := by
        have := congrArg (fun s => s \ tg x) hff'
        simp only at this
        rwa [union_sdiff_right, union_sdiff_right, (hd f hf1).sdiff_eq_left,
          (hd f' hf1').sdiff_eq_left] at this
      exact Gen.psiV_image_injOn (hbd x hx) (hvalid' x hx) hf1 hf1' e1

end RefinedAbsorption.LinkSpread
