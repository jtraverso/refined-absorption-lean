module
public import RefinedAbsorption.MultiRefiner.Basic

/-!
# Transporting residual multi-refiners

Two transport operations used to place a refine-down round inside `K_n^r`
(mathematics: M. Delcourt and L. Postle, arXiv:2402.17855; formalization: Juan Pablo Traverso
Gianini, Apache-2.0).

* `IsResidualMultiRefiner.mapEnds`: moving the vertices along a map `ψ : V → V'` which is
  injective on every copy.  Degrees of `S ⊆ V'` are sums of degrees of the pull-backs of `S`
  (`mdeg_mapEnds_eq_sum`), so divisibility survives even when different copies are glued.
* `IsResidualMultiRefiner.relabel`: renaming the copies along a map `g : E → E'` which is
  injective on the copies in use.
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown

open Finset RefinedAbsorption.MultiRefiner

variable {V V' E E' : Type*} [DecidableEq V] [DecidableEq V'] [DecidableEq E] [DecidableEq E']

/-! ### Moving vertices -/

/-- The copies after moving their vertices along `ψ`. -/
def mapEnds (ψ : V → V') (ends : E → Finset V) : E → Finset V' := fun c => (ends c).image ψ

/-- The pull-backs of `S` inside the vertex sets of `G`. -/
def pullbacks (ψ : V → V') (ends : E → Finset V) (G : Finset E) (S : Finset V') :
    Finset (Finset V) :=
  ((G.biUnion ends).powerset).filter fun S' => S'.image ψ = S ∧ S'.card = S.card

omit [DecidableEq E] in
theorem mem_pullbacks {ψ : V → V'} {ends : E → Finset V} {G : Finset E} {S : Finset V'}
    {S' : Finset V} : S' ∈ pullbacks ψ ends G S ↔
      S' ⊆ G.biUnion ends ∧ S'.image ψ = S ∧ S'.card = S.card := by
  simp [pullbacks]

omit [DecidableEq E] in
/-- If `ψ` is injective on every copy of `G`, the degree of `S` after moving is the sum of the
degrees of its pull-backs. -/
theorem mdeg_mapEnds_eq_sum {ψ : V → V'} {ends : E → Finset V} {G : Finset E}
    (hinj : ∀ c ∈ G, Set.InjOn ψ (ends c)) (S : Finset V') :
    mdeg (mapEnds ψ ends) G S = ∑ S' ∈ pullbacks ψ ends G S, mdeg ends G S' := by
  classical
  have key : ∀ c ∈ G, (if S ⊆ (ends c).image ψ then 1 else 0) =
      ((pullbacks ψ ends G S).filter fun S' => S' ⊆ ends c).card := by
    intro c hc
    split_ifs with hS
    · symm
      rw [card_eq_one]
      refine ⟨(ends c).filter fun v => ψ v ∈ S, ?_⟩
      ext S'
      simp only [mem_filter, mem_pullbacks, mem_singleton]
      constructor
      · rintro ⟨⟨-, himg, hcard⟩, hsub⟩
        ext v
        simp only [mem_filter]
        constructor
        · intro hv
          exact ⟨hsub hv, himg ▸ mem_image_of_mem ψ hv⟩
        · rintro ⟨hv, hvS⟩
          rw [← himg] at hvS
          obtain ⟨w, hw, hwv⟩ := mem_image.1 hvS
          have : w = v := hinj c hc (hsub hw) hv hwv
          exact this ▸ hw
      · rintro rfl
        have hsub : (ends c).filter (fun v => ψ v ∈ S) ⊆ ends c := filter_subset _ _
        have himg : ((ends c).filter fun v => ψ v ∈ S).image ψ = S := by
          ext x
          simp only [mem_image, mem_filter]
          constructor
          · rintro ⟨v, ⟨-, hv⟩, rfl⟩; exact hv
          · intro hx
            obtain ⟨v, hv, rfl⟩ := mem_image.1 (hS hx)
            exact ⟨v, ⟨hv, hx⟩, rfl⟩
        refine ⟨⟨hsub.trans (subset_biUnion_of_mem ends hc), himg, ?_⟩, hsub⟩
        exact (card_image_of_injOn (fun a ha b hb hab =>
          hinj c hc (hsub ha) (hsub hb) hab)).symm.trans (congrArg card himg)
    · symm
      rw [card_eq_zero, filter_eq_empty_iff]
      intro S' hS' hsub
      obtain ⟨-, himg, -⟩ := mem_pullbacks.1 hS'
      exact hS (himg ▸ image_subset_image hsub)
  unfold mdeg mapEnds
  rw [card_filter]
  rw [sum_congr rfl key]
  simp only [card_filter]
  exact sum_comm

omit [DecidableEq E] in
/-- Divisibility survives moving the vertices along a map injective on every copy. -/
theorem divisible_mapEnds {q r : ℕ} {ψ : V → V'} {ends : E → Finset V} {G : Finset E}
    (hinj : ∀ c ∈ G, Set.InjOn ψ (ends c)) (hG : MIsDivisible q r ends G) :
    MIsDivisible q r (mapEnds ψ ends) G := by
  intro S hS
  rw [mdeg_mapEnds_eq_sum hinj]
  refine dvd_sum fun S' hS' => ?_
  obtain ⟨-, -, hcard⟩ := mem_pullbacks.1 hS'
  have := hG S' (hcard ▸ hS)
  rwa [hcard] at this

omit [DecidableEq V] [DecidableEq E] in
theorem card_mapEnds {ψ : V → V'} {ends : E → Finset V} {c : E} (h : Set.InjOn ψ (ends c)) :
    (mapEnds ψ ends c).card = (ends c).card :=
  card_image_of_injOn h

omit [DecidableEq E] in
/-- If `ψ` is injective on all vertices of `G`, divisibility can be pulled back. -/
theorem divisible_of_mapEnds {q r : ℕ} {ψ : V → V'} {ends : E → Finset V} {G : Finset E}
    (hinj : Set.InjOn ψ (G.biUnion ends)) (hG : MIsDivisible q r (mapEnds ψ ends) G) :
    MIsDivisible q r ends G := by
  intro S' hS'
  by_cases hsub : S' ⊆ G.biUnion ends
  · have hcard : (S'.image ψ).card = S'.card :=
      card_image_of_injOn fun a ha b hb hab => hinj (hsub ha) (hsub hb) hab
    have hpb : pullbacks ψ ends G (S'.image ψ) = {S'} := by
      ext T
      rw [mem_pullbacks, mem_singleton]
      constructor
      · rintro ⟨hT, himg, -⟩
        ext v
        constructor
        · intro hv
          obtain ⟨w, hw, hwv⟩ := mem_image.1 (himg ▸ mem_image_of_mem ψ hv)
          rw [← hinj (hsub hw) (hT hv) hwv]; exact hw
        · intro hv
          obtain ⟨w, hw, hwv⟩ := mem_image.1 (himg.symm ▸ mem_image_of_mem ψ hv)
          rw [← hinj (hT hw) (hsub hv) hwv]; exact hw
      · rintro rfl; exact ⟨hsub, rfl, hcard.symm⟩
    have h := hG (S'.image ψ) (hcard ▸ hS')
    rw [mdeg_mapEnds_eq_sum (fun c hc a ha b hb hab =>
      hinj (subset_biUnion_of_mem ends hc ha) (subset_biUnion_of_mem ends hc hb) hab),
      hpb, sum_singleton, hcard] at h
    exact h
  · have : mdeg ends G S' = 0 := by
      rw [mdeg, card_eq_zero, filter_eq_empty_iff]
      intro c hc hS'c
      exact hsub (hS'c.trans (subset_biUnion_of_mem ends hc))
    rw [this]; exact dvd_zero _

/-- **Moving the vertices of a residual multi-refiner** along a map injective on every copy and
on the vertex set of `X`. -/
theorem residual_mapEnds {q r C : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (ψ : V → V')
    (hinj : ∀ c ∈ X ∪ R, Set.InjOn ψ (ends c)) (hinjX : Set.InjOn ψ (X.biUnion ends))
    (hY : Y ⊆ X ∪ R) :
    IsResidualMultiRefiner q r C (mapEnds ψ ends) X R Y 𝒲 := by
  refine ⟨fun c hc => (card_mapEnds (hinj c hc)).trans (h.rgraph c hc), h.disjoint,
    fun W hW => divisible_mapEnds (fun c hc => hinj c (h.subset W hW hc)) (h.divisible W hW),
    h.subset, h.card_le, h.mult_le, fun L hL hdiv => ?_⟩
  have hLdiv : MIsDivisible q r ends L :=
    divisible_of_mapEnds (hinjX.mono (by
      intro v hv
      obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 (mem_coe.1 hv)
      exact mem_coe.2 (mem_biUnion.2 ⟨c, hL hc, hvc⟩))) hdiv
  obtain ⟨𝒰, h𝒰, Res, hRes, hResd, hpw, hd, heq⟩ := h.decomp L hL hLdiv
  refine ⟨𝒰, h𝒰, Res, hRes, divisible_mapEnds (fun c hc => hinj c (hY (hRes hc))) hResd, hpw, hd, heq⟩

/-! ### Renaming copies -/

omit [DecidableEq E] in
theorem mdeg_image_eq {ends : E → Finset V} {ends' : E' → Finset V} {g : E → E'} {A G : Finset E}
    (hends : ∀ c ∈ A, ends' (g c) = ends c) (hg : Set.InjOn g A) (hGA : G ⊆ A) (S : Finset V) :
    mdeg ends' (G.image g) S = mdeg ends G S := by
  classical
  unfold mdeg
  rw [filter_image, card_image_of_injOn]
  · congr 1
    exact filter_congr fun c hc => by rw [hends c (hGA hc)]
  · exact hg.mono fun c hc => hGA (mem_filter.1 (mem_coe.1 hc)).1

omit [DecidableEq V] in
theorem sup_image_image (g : E → E') (𝒰 : Finset (Finset E)) :
    (𝒰.image (image g)).sup id = (𝒰.sup id).image g := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨W', hW', hxW'⟩ := mem_sup.1 hx
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hxW'
    exact mem_image_of_mem g (mem_sup.2 ⟨W, hW, hc⟩)
  · intro hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    obtain ⟨W, hW, hcW⟩ := mem_sup.1 hc
    exact mem_sup.2 ⟨W.image g, mem_image_of_mem _ hW, mem_image_of_mem g hcW⟩

omit [DecidableEq V] [DecidableEq E] in
theorem disjoint_image_of_injOn {g : E → E'} {A G H : Finset E} (hg : Set.InjOn g A)
    (hG : G ⊆ A) (hH : H ⊆ A) (hGH : Disjoint G H) : Disjoint (G.image g) (H.image g) := by
  classical
  rw [disjoint_left]
  rintro _ hx hx'
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
  obtain ⟨c', hc', hcc'⟩ := mem_image.1 hx'
  have : c' = c := hg (hH hc') (hG hc) hcc'
  subst this
  exact disjoint_left.1 hGH hc hc'

/-- **Renaming the copies of a residual multi-refiner** along a map injective on the copies in
use. -/
theorem residual_relabel {q r C : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (g : E → E')
    (ends' : E' → Finset V) (hends : ∀ c ∈ X ∪ R, ends' (g c) = ends c)
    (hg : Set.InjOn g ↑(X ∪ R)) (hY : Y ⊆ X ∪ R) :
    IsResidualMultiRefiner q r C ends' (X.image g) (R.image g) (Y.image g)
      (𝒲.image (image g)) := by
  have hdivi : ∀ G ⊆ X ∪ R, MIsDivisible q r ends G → MIsDivisible q r ends' (G.image g) := by
    intro G hG hd S hS
    rw [mdeg_image_eq hends hg hG]; exact hd S hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← image_union] at hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    rw [hends c hc]; exact h.rgraph c hc
  · exact disjoint_image_of_injOn hg subset_union_left subset_union_right h.disjoint
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    exact hdivi W (h.subset W hW) (h.divisible W hW)
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    rw [← image_union]; exact image_subset_image (h.subset W hW)
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    exact card_image_le.trans (h.card_le W hW)
  · intro x hx
    rw [← image_union] at hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    refine le_trans ?_ (h.mult_le c hc)
    rw [filter_image]
    refine card_image_le.trans (card_le_card fun W hW => ?_)
    obtain ⟨hW𝒲, hcW⟩ := mem_filter.1 hW
    refine mem_filter.2 ⟨hW𝒲, ?_⟩
    obtain ⟨c', hc', hcc'⟩ := mem_image.1 hcW
    rw [← hg (h.subset W hW𝒲 hc') hc hcc']; exact hc'
  · intro L hL hdiv
    classical
    set L₀ := X.filter fun c => g c ∈ L
    have hL₀ : L₀.image g = L := by
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
        exact (mem_filter.1 hc).2
      · intro hx
        obtain ⟨c, hc, rfl⟩ := mem_image.1 (hL hx)
        exact mem_image_of_mem g (mem_filter.2 ⟨hc, hx⟩)
    have hL₀X : L₀ ⊆ X := filter_subset _ _
    have hL₀d : MIsDivisible q r ends L₀ := by
      intro S hS
      have := hdiv S hS
      rwa [← hL₀, mdeg_image_eq hends hg (hL₀X.trans subset_union_left)] at this
    obtain ⟨𝒰, h𝒰, Res, hRes, hResd, hpw, hd, heq⟩ := h.decomp L₀ hL₀X hL₀d
    have hU : ∀ W ∈ 𝒰, W ⊆ X ∪ R := fun W hW => h.subset W (h𝒰 hW)
    have hsupU : 𝒰.sup id ⊆ X ∪ R := fun x hx => by
      obtain ⟨W, hW, hxW⟩ := mem_sup.1 hx
      exact hU W hW hxW
    have hResXR : Res ⊆ X ∪ R := hRes.trans hY
    refine ⟨𝒰.image (image g), image_subset_image h𝒰, Res.image g, image_subset_image hRes,
      hdivi Res hResXR hResd, ?_, ?_, ?_⟩
    · intro W₁' hW₁' W₂' hW₂' hne
      obtain ⟨W₁, hW₁, rfl⟩ := mem_image.1 (mem_coe.1 hW₁')
      obtain ⟨W₂, hW₂, rfl⟩ := mem_image.1 (mem_coe.1 hW₂')
      have hne' : W₁ ≠ W₂ := fun h' => hne (by rw [h'])
      exact disjoint_image_of_injOn hg (hU W₁ hW₁) (hU W₂ hW₂) (hpw hW₁ hW₂ hne')
    · rw [sup_image_image]
      exact disjoint_image_of_injOn hg hsupU hResXR hd
    · rw [sup_image_image, ← image_union, heq, image_union, hL₀]

end RefinedAbsorption.RefineDown
