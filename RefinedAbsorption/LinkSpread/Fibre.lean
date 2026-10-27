module
public import RefinedAbsorption.FlatDown.LinkAccounting

/-!
# Tagged multigraphs: fibres and lifted link refiners

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, induction on uniformity).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

A *tagged multigraph* is a labelled multigraph whose copies `x` have a body `bd x` inside a region
`Zo` and a tag `tg x` outside `Zo`.  The lifted copy is `liftEnds tg bd x = tg x ∪ bd x`.  The
fibre of a tag `T` is the set of copies with tag `T`.

In the application `Zo` is the reserve of the level-`i` flat step, the tag is the outside part `T`
of a copy and the body is its link copy: the link graphs of all outside parts form one tagged
multigraph, and the link refiners of all `T` together are measured through the lifted copies.

The basic observation of this file (`linkRefiners_fibre`) is that **link levels compose**: for a
sub-reserve `Z ⊆ Zo`, the links of the lifted multigraph at level `i + j` with respect to `Z` are
exactly the links, at level `j`, of the bodies of the individual fibres.  Hence link refiners of
the lifted multigraph at level `i + j` (for instance those given by `PlacedLinkLevelE q r (i + j)`)
are, fibre by fibre, link refiners of the bodies at level `j`, with the same constant.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown

variable {V E N : Type} [DecidableEq V] [DecidableEq E] [DecidableEq N]

/-- The lifted ends of a tagged multigraph. -/
def liftEnds (tg bd : E → Finset V) : E → Finset V := fun x => tg x ∪ bd x

/-- The fibre of the tag `T`. -/
def fibre (tg : E → Finset V) (X : Finset E) (T : Finset V) : Finset E :=
  X.filter fun x => tg x = T

omit [DecidableEq E] [DecidableEq N] in
theorem fibre_subset (tg : E → Finset V) (X : Finset E) (T : Finset V) : fibre tg X T ⊆ X :=
  filter_subset _ _

omit [DecidableEq E] [DecidableEq N] in
theorem mem_fibre {tg : E → Finset V} {X : Finset E} {T : Finset V} {x : E} :
    x ∈ fibre tg X T ↔ x ∈ X ∧ tg x = T := mem_filter

section Region

variable {tg bd : E → Finset V} {Zo Z : Finset V}

omit [DecidableEq E] [DecidableEq N] in
/-- The link ends of the lifted multigraph are those of the bodies. -/
theorem lk_liftEnds (hZ : Z ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo) :
    lk (liftEnds tg bd) Z = lk bd Z := by
  funext x
  unfold lk liftEnds
  rw [union_inter_distrib_right,
    disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_right hZ (htg x)), empty_union]

omit [DecidableEq E] [DecidableEq N] in
theorem lE_liftEnds (hZ : Z ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo)
    (endsN : Finset V → N → Finset V) (T T₂ : Finset V) :
    lE (liftEnds tg bd) Z endsN (T ∪ T₂) = lE bd Z (fun T₂ => endsN (T ∪ T₂)) T₂ := by
  unfold lE
  rw [lk_liftEnds hZ htg]

omit [DecidableEq E] [DecidableEq N] in
/-- Splitting a union of a set outside `Zo` and a set inside `Zo`. -/
theorem union_split_eq {A B A' B' : Finset V} (hA : Disjoint A Zo) (hA' : Disjoint A' Zo)
    (hB : B ⊆ Zo) (hB' : B' ⊆ Zo) (h : A ∪ B = A' ∪ B') : A = A' ∧ B = B' := by
  have h1 : (A ∪ B) ∩ Zo = B := by
    rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.1 hA, empty_union, inter_eq_left.2 hB]
  have h2 : (A' ∪ B') ∩ Zo = B' := by
    rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.1 hA', empty_union,
      inter_eq_left.2 hB']
  have h3 : (A ∪ B) \ Zo = A := by
    rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 hB, union_empty, hA.sdiff_eq_left]
  have h4 : (A' ∪ B') \ Zo = A' := by
    rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 hB', union_empty, hA'.sdiff_eq_left]
  exact ⟨by rw [← h3, ← h4, h], by rw [← h1, ← h2, h]⟩

omit [DecidableEq E] [DecidableEq N] in
/-- The outside part (with respect to `Z`) of a lifted copy. -/
theorem liftEnds_sdiff (hZ : Z ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo) (x : E) :
    liftEnds tg bd x \ Z = tg x ∪ (bd x \ Z) := by
  unfold liftEnds
  rw [union_sdiff_distrib, (disjoint_of_subset_right hZ (htg x)).sdiff_eq_left]

omit [DecidableEq E] [DecidableEq N] in
/-- The link of `T ∪ T₂` in the lifted multigraph is the link of `T₂` in the fibre of `T`. -/
theorem lnk_liftEnds (hZ : Z ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo) (hbd : ∀ x, bd x ⊆ Zo)
    {T T₂ : Finset V} (hT : Disjoint T Zo) (hT₂ : T₂ ⊆ Zo) (X : Finset E) :
    lnk (liftEnds tg bd) Z X (T ∪ T₂) = lnk bd Z (fibre tg X T) T₂ := by
  ext x
  simp only [lnk, mem_filter, fibre]
  rw [liftEnds_sdiff hZ htg]
  constructor
  · rintro ⟨hx, h⟩
    obtain ⟨h1, h2⟩ := union_split_eq (htg x) hT (sdiff_subset.trans (hbd x)) hT₂ h
    exact ⟨⟨hx, h1⟩, h2⟩
  · rintro ⟨⟨hx, h1⟩, h2⟩
    exact ⟨hx, by rw [h1, h2]⟩

/-- Outside parts of a fibre lift to outside parts of the lifted multigraph. -/
theorem outParts_liftEnds (hZ : Z ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo) (hbd : ∀ x, bd x ⊆ Zo)
    {i j : ℕ} {X : Finset E} (htgc : ∀ x ∈ X, (tg x).card = i) {T T₂ : Finset V}
    (hT₂ : T₂ ∈ outParts bd Z j (fibre tg X T)) :
    T ∪ T₂ ∈ outParts (liftEnds tg bd) Z (i + j) X := by
  obtain ⟨x, hx, hc, rfl⟩ := mem_outParts.1 hT₂
  obtain ⟨hxX, rfl⟩ := mem_fibre.1 hx
  refine mem_outParts.2 ⟨x, hxX, ?_, liftEnds_sdiff hZ htg x⟩
  rw [liftEnds_sdiff hZ htg, card_union_of_disjoint
    (disjoint_of_subset_right (sdiff_subset.trans (hbd x)) (htg x)), htgc x hxX, hc]

/-- The outside parts of the bodies of a fibre lie in `Zo`. -/
theorem outParts_fibre_subset (hbd : ∀ x, bd x ⊆ Zo) {j : ℕ} {X : Finset E} {T T₂ : Finset V}
    (hT₂ : T₂ ∈ outParts bd Z j (fibre tg X T)) : T₂ ⊆ Zo := by
  obtain ⟨x, -, -, rfl⟩ := mem_outParts.1 hT₂
  exact sdiff_subset.trans (hbd x)

/-- **Link levels compose.**  Link refiners of the lifted multigraph at level `i + j` restrict,
on the fibre of every tag `T` outside `Zo`, to link refiners of the bodies at level `j`
(uniformity `r - i`, clique size `q - i`), with the same constant. -/
theorem linkRefiners_fibre (hZ : Z ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo) (hbd : ∀ x, bd x ⊆ Zo)
    {q r i j Cl : ℕ} {X : Finset E} (htgc : ∀ x ∈ X, (tg x).card = i)
    {endsN : Finset V → N → Finset V} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))}
    (hL : LinkRefiners q r (i + j) Cl (liftEnds tg bd) Z X endsN RN 𝒲) {T : Finset V}
    (hT : Disjoint T Zo) :
    LinkRefiners (q - i) (r - i) j Cl bd Z (fibre tg X T) (fun T₂ => endsN (T ∪ T₂))
      (fun T₂ => RN (T ∪ T₂)) (fun T₂ => 𝒲 (T ∪ T₂)) where
  ref T₂ hT₂ := by
    have h := hL.ref (T ∪ T₂) (outParts_liftEnds hZ htg hbd htgc hT₂)
    rw [lE_liftEnds hZ htg, lnk_liftEnds hZ htg hbd hT (outParts_fibre_subset hbd hT₂)] at h
    rwa [Nat.sub_sub, Nat.sub_sub]
  inZ T₂ hT₂ y hy := hL.inZ (T ∪ T₂) (outParts_liftEnds hZ htg hbd htgc hT₂) y hy

end Region

end RefinedAbsorption.LinkSpread
