module
public import RequestProject.Absorber17.Booster
public import RequestProject.Absorber17.Maps
public import Mathlib.Algebra.Field.ZMod

/-!
# An absorber for the anti-clique (Section 3.1)

Let `S` be a `q`-set.  For every `r`-subset `e ⊆ S` take `q - r` private new vertices `Y_e`;
the *anti-edge* of `e` is the clique on `e ∪ Y_e` minus the edge `e`, and the *anti-clique* on
`S` is the union of the anti-edges of all `r`-subsets of `S`.

We construct an absorber for the anti-clique from the booster of `Booster.lean`: take one
booster `B₁` with root `S`, and for each `r`-subset `e ⊆ S` glue a fresh copy `B_e` of the
booster along its root onto the "off" clique `Q'_e` of `B₁` through `e`.  In the resulting graph
`Z`, the "on" decomposition contains the clique `S`, while the "off" decomposition contains, for
every `e`, a clique `Q̂_e = e ∪ Y_e` with pairwise disjoint private parts `Y_e`.  Then
`Rest = Z \ ⋃_e K(Q̂_e)` is an absorber for the anti-clique.

The result is packaged in the structure `ACAbsorber`, which records only what the general
absorber construction needs.
-/

@[expose] public section

namespace RefinedAbsorption.Absorber17

open Finset

/-- The `r`-subsets of `Fin q`. -/
def Iset (q r : ℕ) : Finset (Finset (Fin q)) := (univ : Finset (Fin q)).powersetCard r

theorem mem_Iset {q r : ℕ} {I : Finset (Fin q)} : I ∈ Iset q r ↔ I.card = r := by
  simp [Iset, mem_powersetCard]

/-- **Abstract anti-clique absorber.**  A vertex type `T` with root vertices `rv i` (`i < q`) and,
for every `r`-subset `I` of `Fin q`, private vertices `yv I s` (`s < q - r`), such that, with
`Qh I = rv(I) ∪ yv(I, ·)` (the anti-edge clique of the root edge `rv(I)`), the graph `Rest`
and the graph `Rest ∪ AC` both have `K_q^r`-decompositions, where `AC` is the anti-clique, and
no edge of `Rest` lies inside the vertex set of `AC`. -/
structure ACAbsorber (q r : ℕ) where
  T : Type
  [fin : Fintype T]
  [deq : DecidableEq T]
  rv : Fin q ↪ T
  yv : Finset (Fin q) → Fin (q - r) → T
  yv_inj : ∀ I ∈ Iset q r, ∀ J ∈ Iset q r, ∀ s t, yv I s = yv J t → I = J ∧ s = t
  yv_ne_rv : ∀ I ∈ Iset q r, ∀ s i, yv I s ≠ rv i
  Rest : Finset (Finset T)
  rest_dec : HasDecomposition q r Rest
  restAC_dec : HasDecomposition q r (Rest ∪ (Iset q r).biUnion (fun I =>
    cliqueEdges r (I.map rv ∪ univ.image (yv I)) \ {I.map rv}))
  rest_indep : ∀ f ∈ Rest, ¬ f ⊆ univ.map rv ∪ (Iset q r).biUnion (fun I => univ.image (yv I))

attribute [instance] ACAbsorber.fin ACAbsorber.deq

variable {q r : ℕ} {F : Type} [DecidableEq F] [Fintype F] [Field F]

/-- Vertex type of the anti-clique absorber built from the booster. -/
abbrev ZV (q : ℕ) (F : Type) := (Fin q × F) ⊕ (Finset (Fin q) × (Fin q × F))

open Classical in
/-- The member of the off family vanishing on `I`. -/
noncomputable def phiI (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) : Fin q → F :=
  if h : ∃ φ ∈ offFamily r a, ∀ i ∈ I, φ i = 0 then Classical.choose h else 0

theorem phiI_spec {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I.card = r) : phiI r a I ∈ offFamily r a ∧ ∀ i ∈ I, phiI r a I i = 0 := by
  have h : ∃ φ ∈ offFamily r a, ∀ i ∈ I, φ i = 0 := by
    obtain ⟨φ, hφ, -⟩ := offFamily_isMDS r ha I hI 0
    exact ⟨φ, hφ.1, fun i hi => hφ.2 i hi⟩
  classical
  rw [phiI, dif_pos h]
  exact Classical.choose_spec h

theorem phiI_ne_zero {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I.card = r) {j : Fin q} (hj : j ∉ I) : phiI r a I j ≠ 0 :=
  offFamily_ne_zero ha (phiI_spec ha hI).1 hI (phiI_spec ha hI).2 hj

/-- The gluing map of the copy indexed by `I`: root vertices `(i, 0)` go to the clique
`graphOf (phiI I)` of the first booster, all other vertices to fresh vertices. -/
noncomputable def gfun (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) (x : Fin q × F) : ZV q F :=
  if x.2 = 0 then Sum.inl (x.1, phiI r a I x.1) else Sum.inr (I, x)

theorem gfun_injective (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) :
    Function.Injective (gfun r a I) := by
  intro x y h
  unfold gfun at h
  by_cases hx : x.2 = 0 <;> by_cases hy : y.2 = 0 <;> simp only [hx, hy, if_true, if_false] at h
  · obtain ⟨h1, -⟩ := Prod.mk.inj (Sum.inl_injective h)
    exact Prod.ext h1 (hx.trans hy.symm)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact (Prod.mk.inj (Sum.inr_injective h)).2

/-- The gluing embedding of the copy indexed by `I`. -/
noncomputable def gEmb (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) : (Fin q × F) ↪ ZV q F :=
  ⟨gfun r a I, gfun_injective r a I⟩

/-- The embedding of the first booster. -/
def inlE (q : ℕ) (F : Type) : (Fin q × F) ↪ ZV q F := ⟨Sum.inl, Sum.inl_injective⟩

/-- The root edge `{(i, 0) : i ∈ I}`. -/
def eI (I : Finset (Fin q)) : Finset (Fin q × F) := I.image (fun i => ((i, 0) : Fin q × F))

omit [Fintype F] in
theorem eI_subset_root (I : Finset (Fin q)) : eI (F := F) I ⊆ graphOf 0 := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := mem_image.1 hx
  exact mem_graphOf.2 rfl

omit [Fintype F] in
theorem card_eI (I : Finset (Fin q)) : (eI (F := F) I).card = I.card :=
  card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)

omit [Fintype F] in
theorem eI_injective : Function.Injective (eI (q := q) (F := F)) := by
  intro I J h
  ext i
  constructor
  · intro hi
    have : ((i, 0) : Fin q × F) ∈ eI J := h ▸ mem_image_of_mem _ hi
    obtain ⟨j, hj, hji⟩ := mem_image.1 this
    rw [← (Prod.mk.inj hji).1]; exact hj
  · intro hi
    have : ((i, 0) : Fin q × F) ∈ eI I := h.symm ▸ mem_image_of_mem _ hi
    obtain ⟨j, hj, hji⟩ := mem_image.1 this
    rw [← (Prod.mk.inj hji).1]; exact hj

/-- The off clique of the first booster through the root edge `eI I`. -/
noncomputable def Qp (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) : Finset (Fin q × F) :=
  graphOf (phiI r a I)

theorem eI_subset_Qp {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I.card = r) : eI I ⊆ Qp r a I := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
  exact mem_graphOf.2 ((phiI_spec ha hI).2 i hi).symm

theorem Qp_mem_off {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I.card = r) : Qp r a I ∈ boostOff r a :=
  mem_image_of_mem _ (phiI_spec ha hI).1

theorem Qp_inter_root {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I.card = r) : Qp r a I ∩ graphOf 0 = eI I :=
  boostOff_inter_root ha (eI_subset_root I) (by rw [card_eI, hI]) (Qp_mem_off ha hI)
    (eI_subset_Qp ha hI)

theorem Qp_injOn {a : Fin q → F} (ha : Function.Injective a) :
    Set.InjOn (Qp r a) (Iset q r : Set (Finset (Fin q))) := by
  intro I hI J hJ h
  have h1 := Qp_inter_root ha (mem_Iset.1 (mem_coe.1 hI))
  rw [h, Qp_inter_root ha (mem_Iset.1 (mem_coe.1 hJ))] at h1
  exact eI_injective h1.symm

theorem root_map_gEmb (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) :
    (graphOf (0 : Fin q → F)).map (gEmb r a I) = (Qp r a I).map (inlE q F) := by
  ext z
  simp only [mem_map, gEmb, inlE, Function.Embedding.coeFn_mk, Qp]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h0 := mem_graphOf.1 hx
    refine ⟨(x.1, phiI r a I x.1), mem_graphOf.2 rfl, ?_⟩
    simp [gfun, h0]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x.1, 0), mem_graphOf.2 rfl, ?_⟩
    simp [gfun, (mem_graphOf.1 hx).symm]

/-- The anti-edge clique of the root edge `eI I` in the glued graph. -/
noncomputable def Qhat (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) : Finset (ZV q F) :=
  (Qp r a I).map (gEmb r a I)

/-- Root of the glued graph. -/
def Shat (q : ℕ) (F : Type) [DecidableEq F] [Zero F] : Finset (ZV q F) :=
  (graphOf (0 : Fin q → F)).map (inlE q F)

/-- The glued graph `Z`. -/
noncomputable def Zg (q r : ℕ) (a : Fin q → F) : Finset (Finset (ZV q F)) :=
  gmap (inlE q F) (partiteGraph q r F) ∪ (Iset q r).biUnion (fun I =>
    gmap (gEmb r a I) (partiteGraph q r F \ cliqueEdges r (graphOf 0)))

/-- The "on" decomposition of `Z`. -/
noncomputable def D1 (q r : ℕ) (a : Fin q → F) : Finset (Finset (ZV q F)) :=
  gmap (inlE q F) (boostOn r a) ∪ (Iset q r).biUnion (fun I =>
    gmap (gEmb r a I) ((boostOn r a).erase (graphOf 0)))

/-- The "off" decomposition of `Z`. -/
noncomputable def D2 (q r : ℕ) (a : Fin q → F) : Finset (Finset (ZV q F)) :=
  gmap (inlE q F) (boostOff r a \ (Iset q r).image (Qp r a)) ∪
    (Iset q r).biUnion (fun I => gmap (gEmb r a I) (boostOff r a))

/-! ### Basic facts about the glued graph -/

theorem exists_not_root {e₀ : Finset (Fin q × F)}
    (he : e₀ ∈ partiteGraph q r F \ cliqueEdges r (graphOf 0)) : ∃ x ∈ e₀, x.2 ≠ 0 := by
  by_contra h
  push_neg at h
  have hc : e₀.card = r := (mem_powersetCard.1 (mem_filter.1 (mem_sdiff.1 he).1).1).2
  exact (mem_sdiff.1 he).2 (mem_powersetCard.2 ⟨fun x hx => mem_graphOf.2 (h x hx), hc⟩)

theorem gfun_eq_inr {a : Fin q → F} {I J : Finset (Fin q)} {x y : Fin q × F}
    (h : gfun r a J y = Sum.inr (I, x)) : J = I ∧ y = x := by
  unfold gfun at h
  by_cases hy : y.2 = 0
  · rw [if_pos hy] at h; exact absurd h (by simp)
  · rw [if_neg hy] at h; exact Prod.mk.inj (Sum.inr_injective h)

theorem gfun_of_ne {a : Fin q → F} {I : Finset (Fin q)} {x : Fin q × F} (hx : x.2 ≠ 0) :
    gfun r a I x = Sum.inr (I, x) := by simp [gfun, hx]

theorem inr_mem_map_gEmb {a : Fin q → F} {I : Finset (Fin q)}
    {e₀ : Finset (Fin q × F)} {x : Fin q × F} (hx : x ∈ e₀) (hx0 : x.2 ≠ 0) :
    (Sum.inr (I, x) : ZV q F) ∈ e₀.map (gEmb r a I) :=
  mem_map.2 ⟨x, hx, gfun_of_ne hx0⟩

theorem disj_inl_copy (a : Fin q → F) (G : Finset (Finset (Fin q × F))) (I : Finset (Fin q)) :
    Disjoint (gmap (inlE q F) G)
      (gmap (gEmb r a I) (partiteGraph q r F \ cliqueEdges r (graphOf 0))) := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨e₁, -, rfl⟩ := mem_gmap.1 hf
  obtain ⟨e₀, he₀, h⟩ := mem_gmap.1 hf'
  obtain ⟨x, hx, hx0⟩ := exists_not_root he₀
  have := h ▸ inr_mem_map_gEmb (a := a) (I := I) hx hx0
  obtain ⟨y, -, hy⟩ := mem_map.1 this
  exact absurd hy (by simp [inlE])

theorem disj_copy_copy (a : Fin q → F) {I J : Finset (Fin q)} (hIJ : I ≠ J) :
    Disjoint (gmap (gEmb r a I) (partiteGraph q r F \ cliqueEdges r (graphOf 0)))
      (gmap (gEmb r a J) (partiteGraph q r F \ cliqueEdges r (graphOf 0))) := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨e₀, he₀, rfl⟩ := mem_gmap.1 hf
  obtain ⟨e₁, -, h⟩ := mem_gmap.1 hf'
  obtain ⟨x, hx, hx0⟩ := exists_not_root he₀
  have := h.symm ▸ inr_mem_map_gEmb (a := a) (I := I) hx hx0
  obtain ⟨y, -, hy⟩ := mem_map.1 this
  exact hIJ (gfun_eq_inr hy).1.symm

theorem root_cliqueEdges_subset (r : ℕ) {a : Fin q → F} (ha : Function.Injective a) :
    cliqueEdges r (graphOf 0) ⊆ partiteGraph q r F :=
  (boostOn_isDecomposition r ha).cliqueEdges_subset (root_mem_boostOn r a)

theorem gmap_gEmb_partite (r : ℕ) {a : Fin q → F} (ha : Function.Injective a)
    (I : Finset (Fin q)) :
    gmap (gEmb r a I) (partiteGraph q r F) = gmap (inlE q F) (cliqueEdges r (Qp r a I)) ∪
      gmap (gEmb r a I) (partiteGraph q r F \ cliqueEdges r (graphOf 0)) := by
  conv_lhs => rw [← union_sdiff_of_subset (root_cliqueEdges_subset r ha)]
  rw [gmap_union, gmap_cliqueEdges, gmap_cliqueEdges, root_map_gEmb]

theorem D1_dec (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a) :
    IsDecomposition q r (Zg q r a) (D1 q r a) := by
  refine IsDecomposition.union hrq ?_ ((boostOn_isDecomposition r ha).gmap _) ?_
  · rw [disjoint_biUnion_right]
    intro I _
    exact disj_inl_copy a _ I
  · refine IsDecomposition.biUnion hrq _ _ _ ?_ fun I _ =>
      (((boostOn_isDecomposition r ha).erase (root_mem_boostOn r a)).gmap _)
    intro I _ J _ hIJ
    exact disj_copy_copy a hIJ

theorem Shat_mem_D1 (a : Fin q → F) : Shat q F ∈ D1 q r a :=
  mem_union_left _ (map_mem_gmap.2 (root_mem_boostOn r a))

theorem Zg_eq (r : ℕ) {a : Fin q → F} (ha : Function.Injective a) :
    Zg q r a = gmap (inlE q F) (partiteGraph q r F \
        ((Iset q r).image (Qp r a)).biUnion (cliqueEdges r)) ∪
      (Iset q r).biUnion (fun I => gmap (gEmb r a I) (partiteGraph q r F)) := by
  have hsub : ((Iset q r).image (Qp r a)).biUnion (cliqueEdges r) ⊆ partiteGraph q r F := by
    intro f hf
    obtain ⟨Q, hQ, hf⟩ := mem_biUnion.1 hf
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hQ
    exact (boostOff_isDecomposition r ha).cliqueEdges_subset (Qp_mem_off ha (mem_Iset.1 hI)) hf
  have hB : gmap (inlE q F) (partiteGraph q r F) =
      gmap (inlE q F) (partiteGraph q r F \ ((Iset q r).image (Qp r a)).biUnion (cliqueEdges r)) ∪
        gmap (inlE q F) (((Iset q r).image (Qp r a)).biUnion (cliqueEdges r)) := by
    rw [← gmap_union, sdiff_union_of_subset hsub]
  simp_rw [gmap_gEmb_partite r ha]
  rw [Zg, biUnion_union, hB, union_assoc]
  congr 2
  ext f
  simp only [mem_gmap, mem_biUnion, mem_image]
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    obtain ⟨Q, ⟨I, hI, rfl⟩, he⟩ := he₀
    exact ⟨I, hI, e₀, he, rfl⟩
  · rintro ⟨I, hI, e₀, he, rfl⟩
    exact ⟨e₀, ⟨Qp r a I, ⟨I, hI, rfl⟩, he⟩, rfl⟩

theorem D2_dec (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a) :
    IsDecomposition q r (Zg q r a) (D2 q r a) := by
  rw [Zg_eq r ha]
  have hC : (Iset q r).image (Qp r a) ⊆ boostOff r a := by
    intro Q hQ
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hQ
    exact Qp_mem_off ha (mem_Iset.1 hI)
  refine IsDecomposition.union hrq ?_
    (((boostOff_isDecomposition r ha).sdiff_biUnion hC).gmap _) ?_
  · rw [disjoint_biUnion_right]
    intro I hI
    rw [gmap_gEmb_partite r ha, disjoint_union_right]
    refine ⟨?_, disj_inl_copy a _ I⟩
    rw [disjoint_gmap, disjoint_left]
    intro f hf hf'
    exact (mem_sdiff.1 hf).2 (mem_biUnion.2 ⟨Qp r a I, mem_image_of_mem _ hI, hf'⟩)
  · refine IsDecomposition.biUnion hrq _ _ _ ?_ fun I _ =>
      ((boostOff_isDecomposition r ha).gmap _)
    intro I hI J hJ hIJ
    simp only [Function.onFun]
    rw [gmap_gEmb_partite r ha, gmap_gEmb_partite r ha, disjoint_union_left,
      disjoint_union_right, disjoint_union_right]
    refine ⟨⟨?_, disj_inl_copy a _ J⟩, ?_, disj_copy_copy a hIJ⟩
    · rw [disjoint_gmap]
      exact (boostOff_isDecomposition r ha).disjoint_cliqueEdges
        (Qp_mem_off ha (mem_Iset.1 hI)) (Qp_mem_off ha (mem_Iset.1 hJ))
        (fun h => hIJ (Qp_injOn ha hI hJ h))
    · exact (disj_inl_copy a _ I).symm

theorem Qhat_mem_D2 {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I ∈ Iset q r) : Qhat r a I ∈ D2 q r a :=
  mem_union_right _ (mem_biUnion.2 ⟨I, hI, map_mem_gmap.2 (Qp_mem_off ha (mem_Iset.1 hI))⟩)

/-! ### Root and private vertices; the absorber `Rest` -/

/-- Root vertices `(i, 0)` of the first booster. -/
def rvE (q : ℕ) (F : Type) [Zero F] : Fin q ↪ ZV q F :=
  ⟨fun i => Sum.inl (i, 0), fun _ _ h => (Prod.mk.inj (Sum.inl_injective h)).1⟩

/-- Enumeration of the complement of `I`. -/
noncomputable def jf (q r : ℕ) (I : Finset (Fin q)) (s : Fin (q - r)) : Fin q :=
  if h : (univ \ I).card = q - r then (univ \ I).orderEmbOfFin h s
  else ⟨0, by have := s.2; omega⟩

theorem card_compl_I {I : Finset (Fin q)} (hI : I ∈ Iset q r) : (univ \ I).card = q - r := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, mem_Iset.1 hI]

theorem jf_notMem {I : Finset (Fin q)} (hI : I ∈ Iset q r) (s : Fin (q - r)) :
    jf q r I s ∉ I := by
  rw [jf, dif_pos (card_compl_I hI)]
  exact (mem_sdiff.1 (orderEmbOfFin_mem _ _ s)).2

theorem jf_injective {I : Finset (Fin q)} (hI : I ∈ Iset q r) : Function.Injective (jf q r I) := by
  intro s t h
  simp only [jf, dif_pos (card_compl_I hI)] at h
  exact (orderEmbOfFin _ _).injective h

theorem exists_jf {I : Finset (Fin q)} (hI : I ∈ Iset q r) {j : Fin q} (hj : j ∉ I) :
    ∃ s, jf q r I s = j := by
  have hmem : j ∈ (univ \ I) := mem_sdiff.2 ⟨mem_univ _, hj⟩
  have : j ∈ Set.range ((univ \ I).orderEmbOfFin (card_compl_I hI)) := by
    rw [range_orderEmbOfFin]; exact hmem
  obtain ⟨s, hs⟩ := this
  exact ⟨s, by rw [jf, dif_pos (card_compl_I hI), hs]⟩

/-- Private vertices of the anti-edge of the root edge indexed by `I`. -/
noncomputable def yvF (r : ℕ) (a : Fin q → F) (I : Finset (Fin q)) (s : Fin (q - r)) : ZV q F :=
  Sum.inr (I, (jf q r I s, phiI r a I (jf q r I s)))

theorem Qhat_eq {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I ∈ Iset q r) : Qhat r a I = I.map (rvE q F) ∪ univ.image (yvF r a I) := by
  have hIc := mem_Iset.1 hI
  ext z
  simp only [Qhat, Qp, mem_map, mem_union, mem_image, mem_univ, true_and, gEmb,
    Function.Embedding.coeFn_mk, rvE]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx2 := mem_graphOf.1 hx
    by_cases hj : x.1 ∈ I
    · left
      refine ⟨x.1, hj, ?_⟩
      have h0 : x.2 = 0 := by rw [hx2]; exact (phiI_spec ha hIc).2 _ hj
      simp [gfun, h0, (phiI_spec ha hIc).2 _ hj] <;> rfl
    · right
      obtain ⟨s, hs⟩ := exists_jf hI hj
      have h0 : x.2 ≠ 0 := by rw [hx2]; exact phiI_ne_zero ha hIc hj
      refine ⟨s, ?_⟩
      rw [gfun_of_ne h0, yvF, hs, ← hx2]
  · rintro (⟨i, hi, rfl⟩ | ⟨s, rfl⟩)
    · refine ⟨(i, 0), mem_graphOf.2 ((phiI_spec ha hIc).2 i hi).symm, ?_⟩
      simp [gfun, (phiI_spec ha hIc).2 i hi] <;> rfl
    · refine ⟨(jf q r I s, phiI r a I (jf q r I s)), mem_graphOf.2 rfl, ?_⟩
      rw [gfun_of_ne (phiI_ne_zero ha hIc (jf_notMem hI s))]; rfl

omit [Fintype F] in
theorem Shat_eq : Shat q F = univ.map (rvE q F) := by
  ext z
  simp only [Shat, mem_map, inlE, rvE, Function.Embedding.coeFn_mk, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, congrArg Sum.inl (Prod.ext rfl (mem_graphOf.1 hx).symm)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(i, 0), mem_graphOf.2 rfl, rfl⟩

/-- The absorber for the anti-clique. -/
noncomputable def RestZ (q r : ℕ) (a : Fin q → F) : Finset (Finset (ZV q F)) :=
  Zg q r a \ (Iset q r).biUnion (fun I => cliqueEdges r (Qhat r a I))

theorem RestZ_dec (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a) :
    IsDecomposition q r (RestZ q r a) (D2 q r a \ (Iset q r).image (Qhat r a)) := by
  have hC : (Iset q r).image (Qhat r a) ⊆ D2 q r a := by
    intro Q hQ
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hQ
    exact Qhat_mem_D2 ha hI
  have := (D2_dec hrq ha).sdiff_biUnion hC
  have he : ((Iset q r).image (Qhat r a)).biUnion (cliqueEdges r) =
      (Iset q r).biUnion (fun I => cliqueEdges r (Qhat r a I)) := by
    ext f; simp only [mem_biUnion, mem_image]
    constructor
    · rintro ⟨_, ⟨I, hI, rfl⟩, hf⟩; exact ⟨I, hI, hf⟩
    · rintro ⟨I, hI, hf⟩; exact ⟨_, ⟨I, hI, rfl⟩, hf⟩
  rw [he] at this
  exact this

theorem Qhat_edges_subset (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a)
    {I : Finset (Fin q)} (hI : I ∈ Iset q r) : cliqueEdges r (Qhat r a I) ⊆ Zg q r a :=
  (D2_dec hrq ha).cliqueEdges_subset (Qhat_mem_D2 ha hI)

theorem yvF_ne_rvE {a : Fin q → F} (I : Finset (Fin q)) (s : Fin (q - r)) (i : Fin q) :
    yvF r a I s ≠ rvE q F i := by simp [yvF, rvE]

theorem Qhat_inter_Shat {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I ∈ Iset q r) {f : Finset (ZV q F)} (hf : f ⊆ Qhat r a I) (hfS : f ⊆ Shat q F) :
    f ⊆ I.map (rvE q F) := by
  intro z hz
  have h1 := hf hz
  rw [Qhat_eq ha hI, mem_union] at h1
  rcases h1 with h1 | h1
  · exact h1
  · obtain ⟨s, -, rfl⟩ := mem_image.1 h1
    have h2 := hfS hz
    rw [Shat_eq] at h2
    obtain ⟨i, -, hi⟩ := mem_map.1 h2
    exact absurd hi.symm (yvF_ne_rvE I s i)

omit [Fintype F] in
theorem cliqueEdges_Shat_subset {f : Finset (ZV q F)} (hf : f ∈ cliqueEdges r (Shat q F)) :
    ∃ I ∈ Iset q r, f = I.map (rvE q F) := by
  rw [cliqueEdges, mem_powersetCard, Shat_eq] at hf
  classical
  refine ⟨f.preimage (rvE q F) (rvE q F).injective.injOn, ?_, ?_⟩
  · rw [mem_Iset, ← hf.2, ← card_map (rvE q F)]
    congr 1
    ext z
    simp only [mem_map, mem_preimage]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hz
      obtain ⟨i, -, rfl⟩ := mem_map.1 (hf.1 hz)
      exact ⟨i, hz, rfl⟩
  · ext z
    simp only [mem_map, mem_preimage]
    constructor
    · intro hz
      obtain ⟨i, -, rfl⟩ := mem_map.1 (hf.1 hz)
      exact ⟨i, hz, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact hi

theorem rv_mem_Qhat {a : Fin q → F} (ha : Function.Injective a) {I : Finset (Fin q)}
    (hI : I ∈ Iset q r) : I.map (rvE q F) ∈ cliqueEdges r (Qhat r a I) := by
  rw [cliqueEdges, mem_powersetCard, Qhat_eq ha hI, card_map, mem_Iset.1 hI]
  exact ⟨subset_union_left, rfl⟩

omit [Fintype F] in
theorem rv_mem_Shat (I : Finset (Fin q)) (hI : I ∈ Iset q r) :
    I.map (rvE q F) ∈ cliqueEdges r (Shat q F) := by
  rw [cliqueEdges, mem_powersetCard, Shat_eq, card_map, mem_Iset.1 hI]
  exact ⟨map_subset_map.2 (subset_univ _), rfl⟩

theorem RestZ_union_AC (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a) :
    RestZ q r a ∪ (Iset q r).biUnion (fun I =>
      cliqueEdges r (I.map (rvE q F) ∪ univ.image (yvF r a I)) \ {I.map (rvE q F)}) =
      Zg q r a \ cliqueEdges r (Shat q F) := by
  have hcongr : (Iset q r).biUnion (fun I =>
      cliqueEdges r (I.map (rvE q F) ∪ univ.image (yvF r a I)) \ {I.map (rvE q F)}) =
      (Iset q r).biUnion (fun I => cliqueEdges r (Qhat r a I) \ {I.map (rvE q F)}) :=
    biUnion_congr rfl (fun I hI => by rw [Qhat_eq ha hI])
  rw [hcongr]
  ext f
  simp only [RestZ, mem_union, mem_sdiff, mem_biUnion, mem_singleton]
  constructor
  · rintro (⟨hZ, hX⟩ | ⟨I, hI, hfQ, hne⟩)
    · refine ⟨hZ, fun hS => ?_⟩
      obtain ⟨I, hI, rfl⟩ := cliqueEdges_Shat_subset hS
      exact hX ⟨I, hI, rv_mem_Qhat ha hI⟩
    · refine ⟨Qhat_edges_subset hrq ha hI hfQ, fun hS => hne ?_⟩
      have h1 := mem_powersetCard.1 hfQ
      have h2 := mem_powersetCard.1 hS
      have hsub := Qhat_inter_Shat ha hI h1.1 h2.1
      refine eq_of_subset_of_card_le hsub ?_
      rw [card_map, mem_Iset.1 hI, h1.2]
  · rintro ⟨hZ, hS⟩
    by_cases hX : ∃ I ∈ Iset q r, f ∈ cliqueEdges r (Qhat r a I)
    · obtain ⟨I, hI, hf⟩ := hX
      refine Or.inr ⟨I, hI, hf, fun h => hS (h ▸ rv_mem_Shat I hI)⟩
    · exact Or.inl ⟨hZ, hX⟩

theorem RestZ_AC_dec (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a) :
    HasDecomposition q r (RestZ q r a ∪ (Iset q r).biUnion (fun I =>
      cliqueEdges r (I.map (rvE q F) ∪ univ.image (yvF r a I)) \ {I.map (rvE q F)})) := by
  rw [RestZ_union_AC hrq ha]
  exact ⟨_, (D1_dec hrq ha).erase (Shat_mem_D1 a)⟩

theorem RestZ_indep (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a) :
    ∀ f ∈ RestZ q r a, ¬ f ⊆ univ.map (rvE q F) ∪
      (Iset q r).biUnion (fun I => univ.image (yvF r a I)) := by
  intro f hf hsub
  obtain ⟨hZ, hX⟩ := mem_sdiff.1 hf
  apply hX
  have hfc : f.card = r := (D1_dec hrq ha).rgraph f hZ
  rcases mem_union.1 hZ with h | h
  · obtain ⟨e₀, -, rfl⟩ := mem_gmap.1 h
    have hS : e₀.map (inlE q F) ⊆ Shat q F := by
      rw [Shat_eq]
      intro z hz
      rcases mem_union.1 (hsub hz) with h1 | h1
      · exact h1
      · obtain ⟨I, -, h2⟩ := mem_biUnion.1 h1
        obtain ⟨s, -, rfl⟩ := mem_image.1 h2
        obtain ⟨x, -, hx⟩ := mem_map.1 hz
        exact absurd hx (by simp [inlE, yvF])
    obtain ⟨I, hI, hIe⟩ := cliqueEdges_Shat_subset (r := r)
      (mem_powersetCard.2 ⟨hS, hfc⟩)
    exact mem_biUnion.2 ⟨I, hI, hIe ▸ rv_mem_Qhat ha hI⟩
  · obtain ⟨I, hI, h'⟩ := mem_biUnion.1 h
    obtain ⟨e₀, -, rfl⟩ := mem_gmap.1 h'
    refine mem_biUnion.2 ⟨I, hI, mem_powersetCard.2 ⟨?_, hfc⟩⟩
    have hIc := mem_Iset.1 hI
    intro z hz
    obtain ⟨x, -, rfl⟩ := mem_map.1 hz
    have hz' := hsub hz
    rw [Qhat_eq ha hI]
    by_cases hx : x.2 = 0
    · simp only [gEmb, Function.Embedding.coeFn_mk, gfun, hx, if_true] at hz' ⊢
      rcases mem_union.1 hz' with h1 | h1
      · obtain ⟨i, -, hi⟩ := mem_map.1 h1
        change (Sum.inl (i, (0 : F)) : ZV q F) = Sum.inl (x.1, phiI r a I x.1) at hi
        have hi0 : (0 : F) = phiI r a I x.1 := congrArg Prod.snd (Sum.inl.inj hi)
        have hxI : x.1 ∈ I := by
          by_contra hxI
          exact phiI_ne_zero ha hIc hxI hi0.symm
        refine mem_union_left _ (mem_map.2 ⟨x.1, hxI, ?_⟩)
        simp [rvE, (phiI_spec ha hIc).2 _ hxI] <;> rfl
      · obtain ⟨J, -, h2⟩ := mem_biUnion.1 h1
        obtain ⟨s, -, hs⟩ := mem_image.1 h2
        exact absurd hs (by simp [yvF])
    · simp only [gEmb, Function.Embedding.coeFn_mk, gfun_of_ne hx] at hz' ⊢
      rcases mem_union.1 hz' with h1 | h1
      · obtain ⟨i, -, hi⟩ := mem_map.1 h1
        exact absurd hi (by simp [rvE])
      · obtain ⟨J, -, h2⟩ := mem_biUnion.1 h1
        obtain ⟨s, -, hs⟩ := mem_image.1 h2
        simp only [yvF, Sum.inr.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, hs2⟩ := hs
        refine mem_union_right _ (mem_image.2 ⟨s, mem_univ _, ?_⟩)
        rw [yvF, hs2]

/-- **Existence of an absorber for the anti-clique** (from the booster over a finite field with
at least `q` elements). -/
theorem exists_ACAbsorber_of_field (hrq : r ≤ q) {a : Fin q → F} (ha : Function.Injective a) :
    Nonempty (ACAbsorber q r) := by
  refine ⟨@ACAbsorber.mk q r (ZV q F) _ _ (rvE q F) (yvF r a) ?_ ?_ (RestZ q r a)
    ⟨_, RestZ_dec hrq ha⟩ (RestZ_AC_dec hrq ha) (RestZ_indep hrq ha)⟩
  · intro I hI J hJ s t h
    simp only [yvF, Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, h2, -⟩ := h
    exact ⟨rfl, jf_injective hI h2⟩
  · intro I _ s i; exact yvF_ne_rvE I s i

end RefinedAbsorption.Absorber17

namespace RefinedAbsorption.Absorber17

/-- **Existence of an absorber for the anti-clique**, for all `r ≤ q`. -/
theorem exists_ACAbsorber {q r : ℕ} (hrq : r ≤ q) : Nonempty (ACAbsorber q r) := by
  obtain ⟨p, hpq, hp⟩ := Nat.exists_infinite_primes (q + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  refine exists_ACAbsorber_of_field (F := ZMod p) hrq (a := fun i : Fin q => (i.val : ZMod p)) ?_
  intro i j h
  have h' := congrArg ZMod.val h
  simp only at h'
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h'
  exact Fin.ext h'

end RefinedAbsorption.Absorber17
