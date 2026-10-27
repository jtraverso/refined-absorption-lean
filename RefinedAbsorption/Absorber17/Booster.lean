module
public import RefinedAbsorption.Absorbers

/-!
# An explicit booster with a strongly orthogonal root (Section 3.1)

Let `F` be a finite field and `a : Fin q → F` injective.  On the vertex set `Fin q × F`
consider the *partite* `r`-graph: all `r`-sets whose elements have pairwise distinct first
coordinates.  A function `φ : Fin q → F` gives the `q`-set `graphOf φ = {(i, φ i)}`.

* The graphs of the evaluations `i ↦ p(a i)` of the polynomials `p` of degree `< r` form a
  `K_q^r`-decomposition `boostOn` of the partite `r`-graph (Lagrange interpolation);
* the graphs of the evaluations of the monic polynomials `X^r + p` (`deg p < r`) form a second
  decomposition `boostOff`;
* the root `S = graphOf 0` belongs to `boostOn`, and for every `r`-subset `e` of `S` the clique
  of `boostOff` through `e` meets `S` exactly in `e` (a monic polynomial of degree `r` has at
  most `r` roots): `boostOff_inter_root`.
-/

@[expose] public section

namespace RefinedAbsorption.Absorber17

open Finset Polynomial

variable {q : ℕ} {F : Type*} [DecidableEq F]

/-- The graph `{(i, φ i)}` of a function `φ : Fin q → F`. -/
def graphOf (φ : Fin q → F) : Finset (Fin q × F) := univ.image (fun i => (i, φ i))

theorem mem_graphOf {φ : Fin q → F} {x : Fin q × F} : x ∈ graphOf φ ↔ x.2 = φ x.1 := by
  simp only [graphOf, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; rfl
  · intro h; exact ⟨x.1, Prod.ext rfl h.symm⟩

theorem card_graphOf (φ : Fin q → F) : (graphOf φ).card = q := by
  rw [graphOf, card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1), card_univ,
    Fintype.card_fin]

theorem graphOf_injective : Function.Injective (graphOf (q := q) (F := F)) := by
  intro φ ψ h
  funext i
  have : (i, φ i) ∈ graphOf ψ := h ▸ mem_graphOf.2 rfl
  exact mem_graphOf.1 this

theorem subset_graphOf_iff {φ : Fin q → F} {e : Finset (Fin q × F)} :
    e ⊆ graphOf φ ↔ ∀ x ∈ e, x.2 = φ x.1 :=
  ⟨fun h _ hx => mem_graphOf.1 (h hx), fun h x hx => mem_graphOf.2 (h x hx)⟩

variable [Fintype F] [Field F]

/-- The partite `r`-graph on `Fin q × F`. -/
def partiteGraph (q r : ℕ) (F : Type*) [DecidableEq F] [Fintype F] :
    Finset (Finset (Fin q × F)) :=
  (univ.powersetCard r).filter (fun e => ∀ x ∈ e, ∀ y ∈ e, x.1 = y.1 → x = y)

/-- A family of functions is MDS of strength `r` if any values prescribed on any `r` coordinates
are attained by exactly one member. -/
def IsMDS (r : ℕ) (Φ : Finset (Fin q → F)) : Prop :=
  ∀ I : Finset (Fin q), I.card = r → ∀ y : Fin q → F, ∃! φ, φ ∈ Φ ∧ ∀ i ∈ I, φ i = y i

/-- The graphs of an MDS family form a `K_q^r`-decomposition of the partite `r`-graph. -/
theorem isDecomposition_of_isMDS {r : ℕ} {Φ : Finset (Fin q → F)} (h : IsMDS r Φ) :
    IsDecomposition q r (partiteGraph q r F) (Φ.image graphOf) := by
  refine ⟨fun e he => (mem_powersetCard.1 (mem_filter.1 he).1).2, fun Q hQ => ?_, fun e he => ?_⟩
  · obtain ⟨φ, -, rfl⟩ := mem_image.1 hQ
    exact card_graphOf φ
  · rw [cliqueMult, filter_image, card_image_of_injective _ graphOf_injective]
    by_cases hp : ∀ x ∈ e, ∀ y ∈ e, x.1 = y.1 → x = y
    · have hmem : e ∈ partiteGraph q r F :=
        mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, he⟩, hp⟩
      rw [if_pos hmem]
      set I := e.image Prod.fst with hI
      have hIc : I.card = r := by
        rw [hI, card_image_of_injOn (fun x hx y hy hxy => hp x hx y hy hxy), he]
      classical
      set y : Fin q → F := fun i => if hi : ∃ x ∈ e, x.1 = i then (Classical.choose hi).2 else 0
      have hy : ∀ x ∈ e, y x.1 = x.2 := by
        intro x hx
        have hi : ∃ z ∈ e, z.1 = x.1 := ⟨x, hx, rfl⟩
        simp only [y, dif_pos hi]
        have := Classical.choose_spec hi
        rw [hp _ this.1 x hx this.2]
      have hiff : ∀ φ, e ⊆ graphOf φ ↔ ∀ i ∈ I, φ i = y i := by
        intro φ
        rw [subset_graphOf_iff]
        constructor
        · intro h1 i hi
          obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
          rw [hy x hx, h1 x hx]
        · intro h1 x hx
          rw [h1 x.1 (mem_image_of_mem _ hx), hy x hx]
      obtain ⟨φ₀, ⟨hφ₀, hφ₀'⟩, huniq⟩ := h I hIc y
      rw [card_eq_one]
      refine ⟨φ₀, ?_⟩
      ext φ
      simp only [mem_filter, mem_singleton, hiff]
      constructor
      · rintro ⟨h1, h2⟩; exact huniq φ ⟨h1, h2⟩
      · rintro rfl; exact ⟨hφ₀, hφ₀'⟩
    · have hmem : e ∉ partiteGraph q r F := fun h' => hp (mem_filter.1 h').2
      rw [if_neg hmem, card_eq_zero, filter_eq_empty_iff]
      intro φ _ hsub
      apply hp
      intro x hx z hz hxz
      rw [subset_graphOf_iff] at hsub
      have h1 := hsub x hx
      have h2 := hsub z hz
      exact Prod.ext hxz (by rw [h1, h2, hxz])

/-- The polynomial of degree `< r` with coefficient vector `c`. -/
noncomputable def lowPoly (r : ℕ) (c : Fin r → F) : F[X] :=
  ((degreeLTEquiv F r).symm c : F[X])

omit [DecidableEq F] [Fintype F] in
theorem degree_lowPoly_lt (r : ℕ) (c : Fin r → F) : (lowPoly r c).degree < r :=
  mem_degreeLT.1 ((degreeLTEquiv F r).symm c).2

omit [DecidableEq F] [Fintype F] in
theorem exists_lowPoly_eq {r : ℕ} {p : F[X]} (hp : p.degree < r) : ∃ c, lowPoly r c = p :=
  ⟨degreeLTEquiv F r ⟨p, mem_degreeLT.2 hp⟩, by simp [lowPoly]⟩

/-- The "on" family: evaluations of the polynomials of degree `< r` at the points `a i`. -/
noncomputable def onFamily (r : ℕ) (a : Fin q → F) : Finset (Fin q → F) :=
  univ.image (fun c : Fin r → F => fun i => (lowPoly r c).eval (a i))

/-- The "off" family: evaluations of the monic polynomials `X^r + p` with `deg p < r`. -/
noncomputable def offFamily (r : ℕ) (a : Fin q → F) : Finset (Fin q → F) :=
  univ.image (fun c : Fin r → F => fun i => (X ^ r + lowPoly r c).eval (a i))

omit [Fintype F] [Field F] in
theorem card_image_a {a : Fin q → F} (ha : Function.Injective a) (I : Finset (Fin q)) :
    (I.image a).card = I.card := card_image_of_injective _ ha

theorem onFamily_isMDS (r : ℕ) {a : Fin q → F} (ha : Function.Injective a) :
    IsMDS r (onFamily r a) := by
  intro I hI y
  have hinj : Set.InjOn a I := fun x _ y _ h => ha h
  set p := Lagrange.interpolate I a y
  have hdeg : p.degree < r := hI ▸ Lagrange.degree_interpolate_lt y hinj
  obtain ⟨c, hc⟩ := exists_lowPoly_eq hdeg
  refine ⟨fun i => (lowPoly r c).eval (a i), ⟨mem_image.2 ⟨c, mem_univ _, rfl⟩, fun i hi => ?_⟩,
    ?_⟩
  · rw [hc]; exact Lagrange.eval_interpolate_at_node y hinj hi
  · rintro φ ⟨hφ, hφ'⟩
    obtain ⟨c', -, rfl⟩ := mem_image.1 hφ
    have : lowPoly r c' = lowPoly r c := by
      refine eq_of_degree_sub_lt_of_eval_finset_eq (I.image a) ?_ ?_
      · rw [card_image_a ha, hI]
        exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_lowPoly_lt r c')
          (degree_lowPoly_lt r c))
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
        have h1 := hφ' i hi
        simp only at h1
        rw [h1, hc, Lagrange.eval_interpolate_at_node y hinj hi]
    funext i
    rw [this]

theorem offFamily_isMDS (r : ℕ) {a : Fin q → F} (ha : Function.Injective a) :
    IsMDS r (offFamily r a) := by
  intro I hI y
  have hinj : Set.InjOn a I := fun x _ y _ h => ha h
  set p := Lagrange.interpolate I a (fun i => y i - a i ^ r)
  have hdeg : p.degree < r := hI ▸ Lagrange.degree_interpolate_lt _ hinj
  obtain ⟨c, hc⟩ := exists_lowPoly_eq hdeg
  refine ⟨fun i => (X ^ r + lowPoly r c).eval (a i),
    ⟨mem_image.2 ⟨c, mem_univ _, rfl⟩, fun i hi => ?_⟩, ?_⟩
  · simp only [eval_add, eval_pow, eval_X]
    rw [hc, Lagrange.eval_interpolate_at_node _ hinj hi]; ring
  · rintro φ ⟨hφ, hφ'⟩
    obtain ⟨c', -, rfl⟩ := mem_image.1 hφ
    have : lowPoly r c' = lowPoly r c := by
      refine eq_of_degree_sub_lt_of_eval_finset_eq (I.image a) ?_ ?_
      · rw [card_image_a ha, hI]
        exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_lowPoly_lt r c')
          (degree_lowPoly_lt r c))
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
        have h1 := hφ' i hi
        simp only [eval_add, eval_pow, eval_X] at h1
        rw [hc, Lagrange.eval_interpolate_at_node _ hinj hi]
        linear_combination h1
    funext i
    rw [this]

/-- The "on" decomposition of the booster. -/
noncomputable def boostOn (r : ℕ) (a : Fin q → F) : Finset (Finset (Fin q × F)) :=
  (onFamily r a).image graphOf

/-- The "off" decomposition of the booster. -/
noncomputable def boostOff (r : ℕ) (a : Fin q → F) : Finset (Finset (Fin q × F)) :=
  (offFamily r a).image graphOf

theorem boostOn_isDecomposition (r : ℕ) {a : Fin q → F} (ha : Function.Injective a) :
    IsDecomposition q r (partiteGraph q r F) (boostOn r a) :=
  isDecomposition_of_isMDS (onFamily_isMDS r ha)

theorem boostOff_isDecomposition (r : ℕ) {a : Fin q → F} (ha : Function.Injective a) :
    IsDecomposition q r (partiteGraph q r F) (boostOff r a) :=
  isDecomposition_of_isMDS (offFamily_isMDS r ha)

/-- The root clique `S = graphOf 0` belongs to the "on" decomposition. -/
theorem root_mem_boostOn (r : ℕ) (a : Fin q → F) : graphOf (0 : Fin q → F) ∈ boostOn r a := by
  refine mem_image.2 ⟨0, mem_image.2 ⟨0, mem_univ _, ?_⟩, rfl⟩
  funext i
  simp [lowPoly]

/-- A member of the off family vanishing on an `r`-set `I` vanishes nowhere else. -/
theorem offFamily_ne_zero {r : ℕ} {a : Fin q → F} (ha : Function.Injective a) {φ : Fin q → F}
    (hφ : φ ∈ offFamily r a) {I : Finset (Fin q)} (hI : I.card = r) (h0 : ∀ i ∈ I, φ i = 0)
    {j : Fin q} (hj : j ∉ I) : φ j ≠ 0 := by
  intro hφj
  obtain ⟨c, -, rfl⟩ := mem_image.1 hφ
  have hdeg : (X ^ r + lowPoly r c).degree = (r : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt] <;> simp [degree_lowPoly_lt]
  have : X ^ r + lowPoly r c = 0 := by
    refine eq_of_degree_sub_lt_of_eval_finset_eq ((insert j I).image a) ?_ ?_
    · rw [sub_zero, hdeg, card_image_a ha, card_insert_of_notMem hj, hI]
      exact_mod_cast Nat.lt_succ_self r
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      rw [eval_zero]
      rcases mem_insert.1 hi with rfl | hi
      · exact hφj
      · exact h0 i hi
  rw [this, degree_zero] at hdeg
  exact WithBot.bot_ne_coe hdeg

/-- **Strong orthogonality of the root.**  For every `r`-subset `e` of the root `S = graphOf 0`,
every clique of the "off" decomposition containing `e` meets `S` exactly in `e`. -/
theorem boostOff_inter_root {r : ℕ} {a : Fin q → F} (ha : Function.Injective a)
    {e Q : Finset (Fin q × F)} (he : e ⊆ graphOf 0) (hec : e.card = r) (hQ : Q ∈ boostOff r a)
    (heQ : e ⊆ Q) : Q ∩ graphOf 0 = e := by
  obtain ⟨φ, hφ, rfl⟩ := mem_image.1 hQ
  set I := e.image Prod.fst
  have hinj : Set.InjOn Prod.fst (e : Set (Fin q × F)) := by
    intro x hx y hy hxy
    have h1 := mem_graphOf.1 (he hx)
    have h2 := mem_graphOf.1 (he hy)
    exact Prod.ext hxy (by rw [h1, h2]; rfl)
  have hIc : I.card = r := by rw [card_image_of_injOn hinj, hec]
  have h0 : ∀ i ∈ I, φ i = 0 := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
    rw [← mem_graphOf.1 (heQ hx), mem_graphOf.1 (he hx)]; rfl
  ext x
  simp only [mem_inter]
  constructor
  · rintro ⟨hx1, hx2⟩
    have h1 := mem_graphOf.1 hx1
    have h2 := mem_graphOf.1 hx2
    by_cases hxI : x.1 ∈ I
    · obtain ⟨y, hy, hyx⟩ := mem_image.1 hxI
      have : y = x := Prod.ext hyx (by rw [mem_graphOf.1 (he hy), h2, hyx])
      rw [← this]; exact hy
    · exact absurd (h1.symm.trans h2) (offFamily_ne_zero ha hφ hIc h0 hxI)
  · intro hx; exact ⟨heQ hx, he hx⟩

end RefinedAbsorption.Absorber17
