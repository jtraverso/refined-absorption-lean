module
public import RefinedAbsorption.Placement.PlacedFlat
public import RefinedAbsorption.Placement.Balance
public import RefinedAbsorption.FlatDown.ChainLink

/-!
# The last flat step in `Fin n`: spread `1`-uniform link refiners

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, the step from
`(r-1)`-flat to `(r-2)`-flat).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

For an `(r-1)`-flat `r`-multigraph `X` on `Fin n` with respect to a reserve `Z`, the link of an
outside `(r-1)`-set `T` is `1`-uniform: its copies are single reserve vertices `z_{T,0}, …`.  We
refine each link with the chain refiner of `FlatDown.ChainLink`: the reservoir labels of the
input `i` sit at its own vertex `z_{T,i}`, and the connecting labels sit at a pivot `p_{T,i} ∈ Z`.
The pivots of all slots `(T, i)` are chosen at once by greedy balancing (`greedy_balance`) so
that

* every `(r-2)`-set `A` and vertex `v` have at most `cap` slots `(T, i)` with `A ⊆ T` and
  `p_{T,i} = v`;
* every `(r-3)`-set `B` and vertices `w, v` have at most `cap` slots `(T, i)` with `B ⊆ T`,
  `w ∈ {z_{T,i}, z_{T,i+1}}` and `p_{T,i} = v`.

Since no piece contains two input vertices, these two families of bounds control both the
degrees of the link refiners and the density of their pieces.  The result is
`placedLastFlatStep`: the step from `(r-1)`-flat to `(r-2)`-flat, inside `Fin n`, with **no**
hypothesis on link refiners: if `Δ_{r-1}(X) ≤ D`, the copies of `X` lie in a set `U` with
`|U| ≤ K |Z|`, and `Cs · D ≤ |Z|`, then the new copies have `(r-1)`-degrees `≤ C' · D`.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown
  RefinedAbsorption.FlatDown.ChainLink RefinedAbsorption.ChainRefiner

section Setup

variable {n : ℕ} {E : Type} [DecidableEq E]

/-- The unique element of a one-element set (a default otherwise). -/
noncomputable def theElt {V : Type} (s : Finset V) (v₀ : V) : V :=
  if h : s.card = 1 then (card_eq_one.1 h).choose else v₀

theorem eq_singleton_theElt {V : Type} {s : Finset V} (v₀ : V) (h : s.card = 1) :
    s = {theElt s v₀} := by
  unfold theElt
  rw [dif_pos h]
  exact (card_eq_one.1 h).choose_spec

variable (ends : E → Finset (Fin n)) (Z : Finset (Fin n)) (X : Finset E)

/-- The number of copies in the link of `T`. -/
noncomputable def lfM (T : Finset (Fin n)) : ℕ := (lnk ends Z X T).card

/-- An enumeration of the link of `T`. -/
noncomputable def lfX (e₀ : E) (T : Finset (Fin n)) (i : ℕ) : E :=
  if h : i < lfM ends Z X T then ((lnk ends Z X T).equivFin.symm ⟨i, h⟩).1 else e₀

/-- The reserve vertex of the `i`-th copy of the link of `T`. -/
noncomputable def lfZ (e₀ : E) (v₀ : Fin n) (T : Finset (Fin n)) (i : ℕ) : Fin n :=
  theElt (ends (lfX ends Z X e₀ T i) ∩ Z) v₀

variable {ends Z X}

theorem lfX_mem {e₀ : E} {T : Finset (Fin n)} {i : ℕ} (hi : i < lfM ends Z X T) :
    lfX ends Z X e₀ T i ∈ lnk ends Z X T := by
  unfold lfX; rw [dif_pos hi]; exact Subtype.prop _

theorem lfX_injOn (e₀ : E) (T : Finset (Fin n)) :
    Set.InjOn (lfX ends Z X e₀ T) (range (lfM ends Z X T)) := by
  intro i hi j hj h
  rw [coe_range, Set.mem_Iio] at hi hj
  unfold lfX at h
  rw [dif_pos hi, dif_pos hj] at h
  have := (lnk ends Z X T).equivFin.symm.injective (Subtype.ext h)
  exact congrArg Fin.val this

theorem image_lfX (e₀ : E) (T : Finset (Fin n)) :
    (range (lfM ends Z X T)).image (lfX ends Z X e₀ T) = lnk ends Z X T := by
  ext x
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact lfX_mem hi
  · intro hx
    refine ⟨((lnk ends Z X T).equivFin ⟨x, hx⟩).1, Fin.is_lt _, ?_⟩
    unfold lfX
    rw [dif_pos (show ((lnk ends Z X T).equivFin ⟨x, hx⟩ : ℕ) < lfM ends Z X T from Fin.is_lt _)]
    simp

theorem mem_lnk' {T : Finset (Fin n)} {x : E} :
    x ∈ lnk ends Z X T ↔ x ∈ X ∧ ends x \ Z = T := by
  simp [lnk]

/-- For an `(r-1)`-flat `r`-multigraph, the link copies are single reserve vertices. -/
theorem lk_lfX {r : ℕ} (hXr : MIsRGraph r ends X) {e₀ : E} {v₀ : Fin n} {T : Finset (Fin n)}
    (hT : T ∈ outParts ends Z (r - 1) X) {i : ℕ} (hi : i < lfM ends Z X T) (hr : 1 ≤ r) :
    lk ends Z (lfX ends Z X e₀ T i) = {lfZ ends Z X e₀ v₀ T i} := by
  obtain ⟨hx, hxT⟩ := mem_lnk'.1 (lfX_mem (e₀ := e₀) hi)
  have hc := hXr _ hx
  have hTc := (outParts_card hT).1
  apply eq_singleton_theElt
  have h1 := card_sdiff_add_card_inter (ends (lfX ends Z X e₀ T i)) Z
  rw [hxT, hTc, hc] at h1
  unfold lk
  omega

theorem lfM_pos {T : Finset (Fin n)} {i : ℕ} (hT : T ∈ outParts ends Z i X) :
    1 ≤ lfM ends Z X T := by
  obtain ⟨x, hx, -, hxT⟩ := mem_outParts.1 hT
  exact one_le_card.2 ⟨x, mem_lnk'.2 ⟨hx, hxT⟩⟩

end Setup


section Slots

variable {n : ℕ} {E : Type} [DecidableEq E]

/-- Slots `(T, i)`: an outside part and the index of a copy of its link. -/
abbrev LfItem (n : ℕ) := Σ _ : Finset (Fin n), ℕ

variable (ends : E → Finset (Fin n)) (Z : Finset (Fin n)) (X : Finset E) (r : ℕ) (e₀ : E)
  (v₀ : Fin n)

/-- All slots. -/
noncomputable def lfI : Finset (LfItem n) :=
  (outParts ends Z (r - 1) X).sigma fun T => range (lfM ends Z X T)

/-- The input vertices adjacent to the pivot of the slot `t`. -/
noncomputable def lfZs (t : LfItem n) : Finset (Fin n) :=
  {lfZ ends Z X e₀ v₀ t.1 t.2} ∪
    (if t.2 + 1 < lfM ends Z X t.1 then {lfZ ends Z X e₀ v₀ t.1 (t.2 + 1)} else ∅)

/-- The keys touched by the slot `t`. -/
noncomputable def lfK (t : LfItem n) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (t.1.powersetCard (r - 2)).image (fun A => (A, ∅)) ∪
    ((t.1.powersetCard (r - 3)) ×ˢ lfZs ends Z X e₀ v₀ t).image (fun bw => (bw.1, {bw.2}))

variable {ends Z X r e₀ v₀}

theorem mem_lfI {t : LfItem n} :
    t ∈ lfI ends Z X r ↔ t.1 ∈ outParts ends Z (r - 1) X ∧ t.2 < lfM ends Z X t.1 := by
  simp [lfI, mem_sigma]

theorem mem_lfK_A {t : LfItem n} {A : Finset (Fin n)} :
    (A, ∅) ∈ lfK ends Z X r e₀ v₀ t ↔ A ⊆ t.1 ∧ A.card = r - 2 := by
  simp only [lfK, mem_union, mem_image, mem_powersetCard, mem_product, Prod.mk.injEq]
  constructor
  · rintro (⟨A', h, rfl, -⟩ | ⟨⟨B, w⟩, -, -, h⟩)
    · exact h
    · exact absurd h (by simp)
  · intro h; exact Or.inl ⟨A, h, rfl, trivial⟩

theorem mem_lfK_B {t : LfItem n} {B : Finset (Fin n)} {w : Fin n} :
    (B, {w}) ∈ lfK ends Z X r e₀ v₀ t ↔
      B ⊆ t.1 ∧ B.card = r - 3 ∧ w ∈ lfZs ends Z X e₀ v₀ t := by
  simp only [lfK, mem_union, mem_image, mem_powersetCard, mem_product, Prod.mk.injEq]
  constructor
  · rintro (⟨A', -, -, h⟩ | ⟨⟨B', w'⟩, ⟨⟨h1, h2⟩, h3⟩, rfl, h4⟩)
    · exact absurd h.symm (by simp)
    · rw [singleton_inj] at h4
      subst h4
      exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact Or.inr ⟨(B, w), ⟨⟨h1, h2⟩, h3⟩, rfl, rfl⟩

theorem card_lfK_le (t : LfItem n) :
    (lfK ends Z X r e₀ v₀ t).card ≤ 3 * 2 ^ t.1.card := by
  have h1 : (t.1.powersetCard (r - 2)).card ≤ 2 ^ t.1.card := by
    rw [card_powersetCard]; exact Nat.choose_le_two_pow _ _
  have h2 : (t.1.powersetCard (r - 3)).card ≤ 2 ^ t.1.card := by
    rw [card_powersetCard]; exact Nat.choose_le_two_pow _ _
  have h3 : (lfZs ends Z X e₀ v₀ t).card ≤ 2 := by
    unfold lfZs
    refine (card_union_le _ _).trans ?_
    split_ifs <;> simp
  unfold lfK
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add card_image_le card_image_le).trans ?_
  rw [card_product]
  calc _ ≤ 2 ^ t.1.card + 2 ^ t.1.card * 2 := Nat.add_le_add h1 (Nat.mul_le_mul h2 h3)
    _ = 3 * 2 ^ t.1.card := by ring

/-- The copy of the slot `t`. -/
noncomputable def lfXof (e₀ : E) (t : LfItem n) : E := lfX ends Z X e₀ t.1 t.2

theorem lfXof_mem {t : LfItem n} (ht : t ∈ lfI ends Z X r) :
    lfXof (ends := ends) (Z := Z) (X := X) e₀ t ∈ X ∧
      ends (lfXof (ends := ends) (Z := Z) (X := X) e₀ t) \ Z = t.1 :=
  mem_lnk'.1 (lfX_mem (mem_lfI.1 ht).2)

theorem lfXof_injOn : Set.InjOn (lfXof (ends := ends) (Z := Z) (X := X) e₀)
    (lfI ends Z X r : Set (LfItem n)) := by
  intro t ht t' ht' h
  have h1 := (lfXof_mem (e₀ := e₀) ht).2
  have h2 := (lfXof_mem (e₀ := e₀) ht').2
  rw [h] at h1
  have hT : t.1 = t'.1 := h1.symm.trans h2
  obtain ⟨T, i⟩ := t
  obtain ⟨T', i'⟩ := t'
  simp only at hT
  subst hT
  have := lfX_injOn (ends := ends) (Z := Z) (X := X) e₀ T
    (by simpa using (mem_lfI.1 ht).2) (by simpa using (mem_lfI.1 ht').2) h
  simp only at this
  rw [this]

/-- Counting slots by their copies. -/
theorem card_lfI_filter_le (P : LfItem n → Prop) [DecidablePred P] (Q : E → Prop)
    [DecidablePred Q] (h : ∀ t ∈ lfI ends Z X r, P t → Q (lfXof (ends := ends) (Z := Z) (X := X) e₀ t)) :
    ((lfI ends Z X r).filter P).card ≤ (X.filter Q).card := by
  refine card_le_card_of_injOn (lfXof (ends := ends) (Z := Z) (X := X) e₀) ?_ ?_
  · intro t ht
    rw [mem_coe, mem_filter] at ht ⊢
    exact ⟨(lfXof_mem ht.1).1, h t ht.1 ht.2⟩
  · exact lfXof_injOn.mono (by intro t ht; exact (mem_filter.1 ht).1)

/-- The reserve vertex of the copy of a slot. -/
theorem lfXof_ends {r' : ℕ} (hXr : MIsRGraph r' ends X) (hr : 1 ≤ r') (hrr : r = r')
    {t : LfItem n} (ht : t ∈ lfI ends Z X r) :
    ends (lfXof (ends := ends) (Z := Z) (X := X) e₀ t) = t.1 ∪ {lfZ ends Z X e₀ v₀ t.1 t.2} := by
  subst hrr
  have hlk := lk_lfX (e₀ := e₀) (v₀ := v₀) hXr (mem_lfI.1 ht).1 (mem_lfI.1 ht).2 hr
  unfold lk at hlk
  have hx := (lfXof_mem (e₀ := e₀) ht).2
  calc ends (lfXof (ends := ends) (Z := Z) (X := X) e₀ t)
      = (ends (lfXof (ends := ends) (Z := Z) (X := X) e₀ t) \ Z) ∪
          (ends (lfXof (ends := ends) (Z := Z) (X := X) e₀ t) ∩ Z) :=
        (sdiff_union_inter _ _).symm
    _ = _ := by rw [hx]; unfold lfXof; rw [hlk]

/-- Slots and sums over outside parts. -/
theorem sum_card_slots (F : Finset (Finset (Fin n))) (hF : F ⊆ outParts ends Z (r - 1) X)
    (P : Finset (Fin n) → ℕ → Prop) [∀ T i, Decidable (P T i)] :
    ∑ T ∈ F, ((range (lfM ends Z X T)).filter (P T)).card =
      ((lfI ends Z X r).filter fun t => t.1 ∈ F ∧ P t.1 t.2).card := by
  have : ((lfI ends Z X r).filter fun t => t.1 ∈ F ∧ P t.1 t.2) =
      F.sigma fun T => (range (lfM ends Z X T)).filter (P T) := by
    ext ⟨T, i⟩
    simp only [mem_filter, mem_lfI, mem_sigma, mem_range]
    constructor
    · rintro ⟨⟨-, hi⟩, hT, hP⟩; exact ⟨hT, hi, hP⟩
    · rintro ⟨hT, hi, hP⟩; exact ⟨⟨hF hT, hi⟩, hT, hP⟩
  rw [this, card_sigma]

end Slots

section Pivots

variable {n : ℕ} {E : Type} [DecidableEq E] {ends : E → Finset (Fin n)} {Z U : Finset (Fin n)}
  {X : Finset E} {r : ℕ} {e₀ : E} {v₀ : Fin n}

/-- Degrees of smaller sets, from the `(r-1)`-degrees (`rootIncidence_of_subset`). -/
theorem mdeg_le_pow (hXr : MIsRGraph r ends X) (hU : ∀ x ∈ X, ends x ⊆ U) {D : ℕ}
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) {J : Finset (Fin n)}
    (hJ : J.card ≤ r - 1) : mdeg ends X J ≤ D * U.card ^ (r - 1 - J.card) :=
  rootIncidence_of_subset X ends U D hU (fun x hx => by rw [hXr x hx]; omega) hdeg J hJ

theorem lfZ_mem (hXr : MIsRGraph r ends X) (hr : 1 ≤ r) {t : LfItem n}
    (ht : t ∈ lfI ends Z X r) : lfZ ends Z X e₀ v₀ t.1 t.2 ∈ Z := by
  have hlk := lk_lfX (e₀ := e₀) (v₀ := v₀) hXr (mem_lfI.1 ht).1 (mem_lfI.1 ht).2 hr
  have : lfZ ends Z X e₀ v₀ t.1 t.2 ∈ lk ends Z (lfX ends Z X e₀ t.1 t.2) := by
    rw [hlk]; exact mem_singleton_self _
  exact (mem_inter.1 this).2

theorem lfI_disjoint {t : LfItem n} (ht : t ∈ lfI ends Z X r) : Disjoint t.1 Z :=
  (outParts_card (mem_lfI.1 ht).1).2

theorem lfI_card {t : LfItem n} (ht : t ∈ lfI ends Z X r) : t.1.card = r - 1 :=
  (outParts_card (mem_lfI.1 ht).1).1

/-- Slots of a given outside part and input vertex. -/
theorem card_slots_input_le (hXr : MIsRGraph r ends X) (hr : 1 ≤ r) (A : Finset (Fin n))
    (w : Fin n) :
    ((lfI ends Z X r).filter fun t => A ⊆ t.1 ∧ lfZ ends Z X e₀ v₀ t.1 t.2 = w).card ≤
      mdeg ends X (insert w A) := by
  unfold mdeg
  refine card_lfI_filter_le (e₀ := e₀) _ _ fun t ht hP => ?_
  rw [lfXof_ends (v₀ := v₀) hXr hr rfl ht, hP.2]
  exact insert_subset (mem_union_right _ (mem_singleton_self _))
    (hP.1.trans subset_union_left)

/-- Shifted slots. -/
theorem card_slots_next_le (A : Finset (Fin n)) (w : Fin n) :
    ((lfI ends Z X r).filter fun t => A ⊆ t.1 ∧ t.2 + 1 < lfM ends Z X t.1 ∧
        lfZ ends Z X e₀ v₀ t.1 (t.2 + 1) = w).card ≤
      ((lfI ends Z X r).filter fun t => A ⊆ t.1 ∧ lfZ ends Z X e₀ v₀ t.1 t.2 = w).card := by
  refine card_le_card_of_injOn (fun t => ⟨t.1, t.2 + 1⟩) ?_ ?_
  · intro t ht
    rw [mem_coe, mem_filter] at ht ⊢
    obtain ⟨ht, h1, h2, h3⟩ := ht
    exact ⟨mem_lfI.2 ⟨(mem_lfI.1 ht).1, h2⟩, h1, h3⟩
  · intro t _ t' _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    obtain ⟨T, i⟩ := t
    obtain ⟨T', i'⟩ := t'
    simp only at h
    obtain ⟨rfl, h⟩ := h
    have : i = i' := by omega
    rw [this]

/-- The key totals of the first kind. -/
theorem lf_totA (hXr : MIsRGraph r ends X) (hr : 2 ≤ r) {D : ℕ}
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) (A : Finset (Fin n)) :
    ((lfI ends Z X r).filter fun t => (A, (∅ : Finset (Fin n))) ∈ lfK ends Z X r e₀ v₀ t).card ≤
      D * Z.card := by
  simp only [mem_lfK_A]
  by_cases hA : A.card = r - 2 ∧ Disjoint A Z
  · have hmaps : ∀ t ∈ (lfI ends Z X r).filter fun t => A ⊆ t.1 ∧ A.card = r - 2,
        lfZ ends Z X e₀ v₀ t.1 t.2 ∈ Z := fun t ht => lfZ_mem hXr (by omega) (mem_filter.1 ht).1
    rw [card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun w hw => ?_
    rw [filter_filter]
    refine le_trans (card_le_card (t := (lfI ends Z X r).filter fun t =>
      A ⊆ t.1 ∧ lfZ ends Z X e₀ v₀ t.1 t.2 = w) ?_) ?_
    · intro t ht; exact mem_filter.2 ⟨(mem_filter.1 ht).1, (mem_filter.1 ht).2.1.1,
        (mem_filter.1 ht).2.2⟩
    refine (card_slots_input_le hXr (by omega) A w).trans (hdeg _ ?_)
    rw [card_insert_of_notMem (fun h => disjoint_left.1 hA.2 h hw), hA.1]
    omega
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    rw [filter_eq_empty_iff]
    rintro t ht ⟨hAt, hAc⟩
    exact hA ⟨hAc, disjoint_of_subset_left hAt (lfI_disjoint ht)⟩

/-- The key totals of the second kind. -/
theorem lf_totB (hXr : MIsRGraph r ends X) (hr : 2 ≤ r) (hU : ∀ x ∈ X, ends x ⊆ U) {D : ℕ}
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) (B : Finset (Fin n))
    (w : Fin n) :
    ((lfI ends Z X r).filter fun t => (B, ({w} : Finset (Fin n))) ∈ lfK ends Z X r e₀ v₀ t).card ≤
      2 * (D * (U.card + 1)) := by
  simp only [mem_lfK_B]
  by_cases hB3 : B.card = r - 3
  swap
  · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun t _ h => hB3 h.2.1)]; exact Nat.zero_le _
  have hF1 : ((lfI ends Z X r).filter fun t => B ⊆ t.1 ∧ B.card = r - 3 ∧
      lfZ ends Z X e₀ v₀ t.1 t.2 = w).card ≤ D * (U.card + 1) := by
    by_cases hB : B.card = r - 3 ∧ w ∉ B
    · refine le_trans (card_le_card (t := (lfI ends Z X r).filter fun t =>
        B ⊆ t.1 ∧ lfZ ends Z X e₀ v₀ t.1 t.2 = w) ?_) ?_
      · intro t ht; exact mem_filter.2 ⟨(mem_filter.1 ht).1, (mem_filter.1 ht).2.1,
          (mem_filter.1 ht).2.2.2⟩
      refine (card_slots_input_le hXr (by omega) B w).trans ?_
      have hc : (insert w B).card ≤ r - 1 := by rw [card_insert_of_notMem hB.2]; omega
      refine (mdeg_le_pow hXr hU hdeg hc).trans (Nat.mul_le_mul_left _ ?_)
      rw [card_insert_of_notMem hB.2, hB.1]
      calc U.card ^ (r - 1 - (r - 3 + 1)) ≤ U.card ^ 1 ⊔ 1 := by
            rcases Nat.lt_or_ge r 3 with h | h
            · rw [show r - 1 - (r - 3 + 1) = 0 by omega]; simp
            · rw [show r - 1 - (r - 3 + 1) = 1 by omega]; exact le_max_left _ _
        _ ≤ U.card + 1 := by rw [pow_one]; exact max_le (by omega) (by omega)
    · rw [card_eq_zero.2]
      · exact Nat.zero_le _
      rw [filter_eq_empty_iff]
      rintro t ht ⟨hBt, hBc, hz⟩
      refine hB ⟨hBc, fun hwB => ?_⟩
      have := lfZ_mem (e₀ := e₀) (v₀ := v₀) hXr (by omega) ht
      rw [hz] at this
      exact disjoint_left.1 (lfI_disjoint ht) (hBt hwB) this
  have hsub : ((lfI ends Z X r).filter fun t => B ⊆ t.1 ∧ B.card = r - 3 ∧
      w ∈ lfZs ends Z X e₀ v₀ t) ⊆
      ((lfI ends Z X r).filter fun t => B ⊆ t.1 ∧ B.card = r - 3 ∧
        lfZ ends Z X e₀ v₀ t.1 t.2 = w) ∪
      ((lfI ends Z X r).filter fun t => B ⊆ t.1 ∧ t.2 + 1 < lfM ends Z X t.1 ∧
        lfZ ends Z X e₀ v₀ t.1 (t.2 + 1) = w) := by
    intro t ht
    rw [mem_filter] at ht
    obtain ⟨ht, hB, hBc, hw⟩ := ht
    unfold lfZs at hw
    rw [mem_union, mem_singleton] at hw
    rcases hw with hw | hw
    · exact mem_union_left _ (mem_filter.2 ⟨ht, hB, hBc, hw.symm⟩)
    · split_ifs at hw with h
      · exact mem_union_right _ (mem_filter.2 ⟨ht, hB, h, (mem_singleton.1 hw).symm⟩)
      · simp at hw
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [two_mul]
  refine Nat.add_le_add hF1 ((card_slots_next_le B w).trans ?_)
  refine le_trans (card_le_card ?_) hF1
  intro t ht
  rw [mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, hB3, ht.2.2⟩

/-- The cap of the pivot loads. -/
def lfCap (r K D : ℕ) : ℕ := 3 * 2 ^ (r - 1) * D * (3 + 2 * K) + 1

theorem mem_lfK_cases {t : LfItem n} {A W : Finset (Fin n)}
    (h : (A, W) ∈ lfK ends Z X r e₀ v₀ t) : W = ∅ ∨ ∃ w, W = {w} := by
  simp only [lfK, mem_union, mem_image, Prod.mk.injEq] at h
  rcases h with ⟨A', -, -, h⟩ | ⟨⟨B, w⟩, -, -, h⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨w, h.symm⟩

/-- **The pivots**: greedy balancing of all slots. -/
theorem lf_pivots (hXr : MIsRGraph r ends X) (hr : 2 ≤ r) (hU : ∀ x ∈ X, ends x ⊆ U) {K D : ℕ}
    (hUK : U.card ≤ K * Z.card) (hZ : 0 < Z.card)
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) :
    ∃ σ : LfItem n → Fin n, (∀ t ∈ lfI ends Z X r, σ t ∈ Z) ∧
      ∀ k v, ((lfI ends Z X r).filter fun t =>
        k ∈ lfK ends Z X r e₀ v₀ t ∧ σ t = v).card ≤ lfCap r K D := by
  set N := 3 * 2 ^ (r - 1)
  set τ := D * Z.card + 2 * (D * (U.card + 1))
  refine greedy_balance _ Z _ N τ _ ?_ ?_ ?_
  · intro t ht
    have := card_lfK_le (ends := ends) (Z := Z) (X := X) (r := r) (e₀ := e₀) (v₀ := v₀) t
    rwa [lfI_card ht] at this
  · rintro ⟨A, W⟩
    by_cases hW : W = ∅
    · subst hW
      exact (lf_totA hXr hr hdeg A).trans (Nat.le_add_right _ _)
    · by_cases hW' : ∃ w, W = {w}
      · obtain ⟨w, rfl⟩ := hW'
        exact (lf_totB hXr hr hU hdeg A w).trans (Nat.le_add_left _ _)
      · rw [card_eq_zero.2]
        · exact Nat.zero_le _
        rw [filter_eq_empty_iff]
        intro t _ h
        rcases mem_lfK_cases h with h | h
        · exact hW h
        · exact hW' h
  · have h1 : τ ≤ D * Z.card * (3 + 2 * K) := by
      have : D * (U.card + 1) ≤ D * (K * Z.card) + D * Z.card := by
        rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      calc τ ≤ D * Z.card + 2 * (D * (K * Z.card) + D * Z.card) := by
            simp only [τ]; omega
        _ = D * Z.card * (3 + 2 * K) := by ring
    have h2 : Z.card * lfCap r K D = N * (D * Z.card * (3 + 2 * K)) + Z.card := by
      unfold lfCap; ring
    calc N * τ ≤ N * (D * Z.card * (3 + 2 * K)) := Nat.mul_le_mul_left _ h1
      _ < Z.card * lfCap r K D := by rw [h2]; omega

end Pivots

section Counts

variable {n : ℕ} {E : Type} [DecidableEq E] {ends : E → Finset (Fin n)} {Z U : Finset (Fin n)}
  {X : Finset E} {r : ℕ} {e₀ : E} {v₀ : Fin n}

/-- The good slots of `(T, i)` for a set `A` (the slot predicate of the chain refiners). -/
def lfGood (ends : E → Finset (Fin n)) (Z : Finset (Fin n)) (X : Finset E) (e₀ : E) (v₀ : Fin n)
    (σ : LfItem n → Fin n) (A : Finset (Fin n)) (t : LfItem n) : Prop :=
  GoodSlot (lfM ends Z X t.1) (lfZ ends Z X e₀ v₀ t.1) (fun i => σ ⟨t.1, i⟩) A t.2

noncomputable instance (σ : LfItem n → Fin n) (A : Finset (Fin n)) (t : LfItem n) :
    Decidable (lfGood ends Z X e₀ v₀ σ A t) := by
  unfold lfGood; infer_instance

theorem lf_count_piv1 (hr : 2 ≤ r) (hU : ∀ x ∈ X, ends x ⊆ U) {σ : LfItem n → Fin n} {cap : ℕ}
    (hload : ∀ k v, ((lfI ends Z X r).filter fun t =>
      k ∈ lfK ends Z X r e₀ v₀ t ∧ σ t = v).card ≤ cap)
    (A : Finset (Fin n)) (hA : A.card ≤ r - 2) (w : Fin n) :
    ((lfI ends Z X r).filter fun t => A ⊆ t.1 ∧ σ t = w).card ≤
      cap * U.card ^ (r - 2 - A.card) := by
  have h := rootIncidence_of_subset (r := r - 1) ((lfI ends Z X r).filter fun t => σ t = w)
    (fun t => t.1) U cap
    (fun t ht => by
      have h1 := (lfXof_mem (e₀ := e₀) (mem_filter.1 ht).1)
      show t.1 ⊆ U
      rw [← h1.2]; exact sdiff_subset.trans (hU _ h1.1))
    (fun t ht => by rw [lfI_card (mem_filter.1 ht).1]; omega)
    (fun S hS => by
      refine le_trans (card_le_card ?_) (hload (S, ∅) w)
      intro t ht
      simp only [mem_filter] at ht ⊢
      exact ⟨ht.1.1, mem_lfK_A.2 ⟨ht.2, by omega⟩, ht.1.2⟩)
    A (by omega)
  rw [show r - 1 - 1 - A.card = r - 2 - A.card by omega] at h
  refine le_trans (card_le_card ?_) h
  intro t ht
  simp only [mem_filter] at ht ⊢
  exact ⟨⟨ht.1, ht.2.2⟩, ht.2.1⟩

theorem lf_count_piv2 (hr : 2 ≤ r) (hU : ∀ x ∈ X, ends x ⊆ U) {σ : LfItem n → Fin n} {cap : ℕ}
    (hload : ∀ k v, ((lfI ends Z X r).filter fun t =>
      k ∈ lfK ends Z X r e₀ v₀ t ∧ σ t = v).card ≤ cap)
    (A : Finset (Fin n)) (hA : A.card ≤ r - 3) (w₁ w₂ : Fin n) :
    ((lfI ends Z X r).filter fun t => A ⊆ t.1 ∧ σ t = w₂ ∧ w₁ ∈ lfZs ends Z X e₀ v₀ t).card ≤
      cap * U.card ^ (r - 3 - A.card) := by
  have h := rootIncidence_of_subset (r := r - 2)
    ((lfI ends Z X r).filter fun t => σ t = w₂ ∧ w₁ ∈ lfZs ends Z X e₀ v₀ t)
    (fun t => t.1) U cap
    (fun t ht => by
      have h1 := (lfXof_mem (e₀ := e₀) (mem_filter.1 ht).1)
      show t.1 ⊆ U
      rw [← h1.2]; exact sdiff_subset.trans (hU _ h1.1))
    (fun t ht => by rw [lfI_card (mem_filter.1 ht).1]; omega)
    (fun S hS => by
      refine le_trans (card_le_card ?_) (hload (S, {w₁}) w₂)
      intro t ht
      simp only [mem_filter] at ht ⊢
      exact ⟨ht.1.1, mem_lfK_B.2 ⟨ht.2, by omega, ht.1.2.2⟩, ht.1.2.1⟩)
    A (by omega)
  rw [show r - 2 - 1 - A.card = r - 3 - A.card by omega] at h
  refine le_trans (card_le_card ?_) h
  intro t ht
  simp only [mem_filter] at ht ⊢
  exact ⟨⟨ht.1, ht.2.2⟩, ht.2.1⟩

/-- **The slot count.**  For every `J` with `|J| ≤ r - 1`, the slots `(T, i)` with `T ⊇ J \ Z`
whose pair contains `J ∩ Z` number at most `(2D + 2 cap) · |U|^(r-1-|J|)`. -/
theorem lf_slot_count (hXr : MIsRGraph r ends X) (hr : 2 ≤ r) (hU : ∀ x ∈ X, ends x ⊆ U)
    {D : ℕ} (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D)
    {σ : LfItem n → Fin n} {cap : ℕ}
    (hload : ∀ k v, ((lfI ends Z X r).filter fun t =>
      k ∈ lfK ends Z X r e₀ v₀ t ∧ σ t = v).card ≤ cap)
    (J : Finset (Fin n)) (hJ : J.card ≤ r - 1) :
    ((lfI ends Z X r).filter fun t => J \ Z ⊆ t.1 ∧ lfGood ends Z X e₀ v₀ σ (J ∩ Z) t).card ≤
      (2 * D + 2 * cap) * U.card ^ (r - 1 - J.card) := by
  have hsplit := card_sdiff_add_card_inter J Z
  have hin : ∀ w, J ∩ Z = {w} →
      ((lfI ends Z X r).filter fun t => J \ Z ⊆ t.1 ∧ lfZ ends Z X e₀ v₀ t.1 t.2 = w).card ≤
        D * U.card ^ (r - 1 - J.card) := by
    intro w hw
    refine (card_slots_input_le hXr (by omega) _ w).trans ?_
    have : insert w (J \ Z) = J := by
      ext v
      simp only [mem_insert, mem_sdiff]
      constructor
      · rintro (h | ⟨h, -⟩)
        · have : w ∈ J ∩ Z := hw ▸ mem_singleton_self w
          rw [h]; exact (mem_inter.1 this).1
        · exact h
      · intro hv
        by_cases hz : v ∈ Z
        · left
          have : v ∈ J ∩ Z := mem_inter.2 ⟨hv, hz⟩
          rw [hw] at this
          exact mem_singleton.1 this
        · exact Or.inr ⟨hv, hz⟩
    rw [this]
    exact mdeg_le_pow hXr hU hdeg hJ
  rcases Nat.lt_or_ge (J ∩ Z).card 3 with h3 | h3
  · interval_cases hc : (J ∩ Z).card
    · -- no reserve vertex
      rw [card_eq_zero] at hc
      have hJZ : J \ Z = J := by
        rw [← sdiff_union_inter J Z, hc, union_empty]
        ext v; simp only [mem_sdiff]; tauto
      refine le_trans ?_ (Nat.mul_le_mul_right _ (show D ≤ 2 * D + 2 * cap by omega))
      refine le_trans ?_ (mdeg_le_pow hXr hU hdeg hJ)
      unfold mdeg
      refine card_lfI_filter_le (e₀ := e₀) _ _ fun t ht hP => ?_
      rw [← hJZ]
      exact hP.1.trans ((lfXof_mem ht).2 ▸ sdiff_subset)
    · -- one reserve vertex
      obtain ⟨w, hw⟩ := card_eq_one.1 hc
      have hsub : ((lfI ends Z X r).filter fun t =>
          J \ Z ⊆ t.1 ∧ lfGood ends Z X e₀ v₀ σ (J ∩ Z) t) ⊆
          (((lfI ends Z X r).filter fun t => J \ Z ⊆ t.1 ∧ lfZ ends Z X e₀ v₀ t.1 t.2 = w) ∪
            ((lfI ends Z X r).filter fun t => J \ Z ⊆ t.1 ∧ t.2 + 1 < lfM ends Z X t.1 ∧
              lfZ ends Z X e₀ v₀ t.1 (t.2 + 1) = w)) ∪
            ((lfI ends Z X r).filter fun t => J \ Z ⊆ t.1 ∧ σ t = w) := by
        intro t ht
        rw [mem_filter] at ht
        obtain ⟨ht, hT, hg⟩ := ht
        unfold lfGood GoodSlot at hg
        rw [hw] at hg
        simp only [singleton_subset_iff, mem_insert, mem_singleton] at hg
        simp only [mem_union, mem_filter]
        rcases hg with (h | h) | ⟨h1, h | h⟩
        · exact Or.inl (Or.inl ⟨ht, hT, h.symm⟩)
        · exact Or.inr ⟨ht, hT, h.symm⟩
        · exact Or.inr ⟨ht, hT, h.symm⟩
        · exact Or.inl (Or.inr ⟨ht, hT, h1, h.symm⟩)
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      have hpiv := lf_count_piv1 hr hU hload (J \ Z) (by omega) w
      rw [show r - 2 - (J \ Z).card = r - 1 - J.card by omega] at hpiv
      have hA := hin w hw
      have hB := (card_slots_next_le (e₀ := e₀) (v₀ := v₀) (J \ Z) w).trans hA
      calc _ ≤ (D * U.card ^ (r - 1 - J.card) + D * U.card ^ (r - 1 - J.card)) +
            cap * U.card ^ (r - 1 - J.card) :=
            Nat.add_le_add ((card_union_le _ _).trans (Nat.add_le_add hA hB)) hpiv
        _ ≤ _ := by nlinarith [Nat.zero_le (U.card ^ (r - 1 - J.card))]
    · -- two reserve vertices
      obtain ⟨w₁, w₂, hne, hw⟩ := card_eq_two.1 hc
      have hsub : ((lfI ends Z X r).filter fun t =>
          J \ Z ⊆ t.1 ∧ lfGood ends Z X e₀ v₀ σ (J ∩ Z) t) ⊆
          ((lfI ends Z X r).filter fun t =>
            J \ Z ⊆ t.1 ∧ σ t = w₂ ∧ w₁ ∈ lfZs ends Z X e₀ v₀ t) ∪
          ((lfI ends Z X r).filter fun t =>
            J \ Z ⊆ t.1 ∧ σ t = w₁ ∧ w₂ ∈ lfZs ends Z X e₀ v₀ t) := by
        intro t ht
        rw [mem_filter] at ht
        obtain ⟨ht, hT, hg⟩ := ht
        unfold lfGood GoodSlot at hg
        rw [hw] at hg
        simp only [mem_union, mem_filter, lfZs, mem_singleton]
        have key : ∀ a b : Fin n, ({w₁, w₂} : Finset (Fin n)) ⊆ {a, b} →
            (w₁ = a ∧ w₂ = b) ∨ (w₁ = b ∧ w₂ = a) := by
          intro a b hab
          have h1 := hab (mem_insert_self _ _)
          have h2 := hab (mem_insert_of_mem (mem_singleton_self _))
          simp only [mem_insert, mem_singleton] at h1 h2
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
          · exact absurd rfl hne
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl hne
        rcases hg with hg | ⟨hlt, hg⟩
        · rcases key _ _ hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨ht, hT, h2.symm, Or.inl h1⟩
          · exact Or.inr ⟨ht, hT, h1.symm, Or.inl h2⟩
        · rcases key _ _ hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine Or.inr ⟨ht, hT, h1.symm, Or.inr ?_⟩
            rw [if_pos hlt]; exact mem_singleton.2 h2
          · refine Or.inl ⟨ht, hT, h2.symm, Or.inr ?_⟩
            rw [if_pos hlt]; exact mem_singleton.2 h1
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      have e : r - 3 - (J \ Z).card = r - 1 - J.card := by omega
      have h1 := lf_count_piv2 hr hU hload (J \ Z) (by omega) w₁ w₂
      have h2 := lf_count_piv2 hr hU hload (J \ Z) (by omega) w₂ w₁
      rw [e] at h1 h2
      calc _ ≤ cap * U.card ^ (r - 1 - J.card) + cap * U.card ^ (r - 1 - J.card) :=
            Nat.add_le_add h1 h2
        _ ≤ _ := by nlinarith [Nat.zero_le (U.card ^ (r - 1 - J.card))]
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    rw [filter_eq_empty_iff]
    rintro t - ⟨-, hg⟩
    unfold lfGood GoodSlot at hg
    rcases hg with hg | ⟨-, hg⟩
    · have := (card_le_card hg).trans (card_insert_le _ _); simp at this; omega
    · have := (card_le_card hg).trans (card_insert_le _ _); simp at this; omega

end Counts

section Links

variable {n : ℕ} {E : Type} [DecidableEq E] {ends : E → Finset (Fin n)} {Z U : Finset (Fin n)}
  {X : Finset E} {r : ℕ} {e₀ : E} {v₀ : Fin n}

variable (ends Z X e₀ v₀) in
/-- The ends of the reservoir labels of the link refiner of `T`. -/
noncomputable def lfEndsN (σ : LfItem n → Fin n) (T : Finset (Fin n)) (y : Lab) :
    Finset (Fin n) :=
  {vtx (lfM ends Z X T) (lfZ ends Z X e₀ v₀ T) (fun i => σ ⟨T, i⟩) y}

variable (ends Z X) in
/-- The reservoir of the link refiner of `T`. -/
noncomputable def lfRN (q : ℕ) (T : Finset (Fin n)) : Finset Lab := chainRN q (lfM ends Z X T)

variable (ends Z X e₀) in
/-- The pieces of the link refiner of `T`. -/
noncomputable def lfW (q : ℕ) (T : Finset (Fin n)) : Finset (Finset (E ⊕ Lab)) :=
  chainFam q (lfM ends Z X T) (lfX ends Z X e₀ T)

theorem lE_lfEndsN (σ : LfItem n → Fin n) (T : Finset (Fin n)) :
    lE ends Z (lfEndsN ends Z X e₀ v₀ σ) T =
      cEnds (lk ends Z) (lfM ends Z X T) (lfZ ends Z X e₀ v₀ T) (fun i => σ ⟨T, i⟩) := by
  funext c; cases c <;> rfl

/-- **The spread link refiners** of an `(r-1)`-flat multigraph. -/
theorem lf_linkRefiners {q : ℕ} (hXr : MIsRGraph r ends X) (hr : 2 ≤ r) (hrq : r < q)
    {σ : LfItem n → Fin n} (hσZ : ∀ t ∈ lfI ends Z X r, σ t ∈ Z) :
    LinkRefiners q r (r - 1) (4 * (q - (r - 1)) + 1) ends Z X (lfEndsN ends Z X e₀ v₀ σ)
      (lfRN ends Z X (q - (r - 1))) (lfW ends Z X e₀ (q - (r - 1))) := by
  refine ⟨fun T hT => ?_, fun T hT y hy => ?_⟩
  · rw [show r - (r - 1) = 1 by omega, lE_lfEndsN]
    have hX : (lnk ends Z X T).image Sum.inl = chainX (lfM ends Z X T) (lfX ends Z X e₀ T) := by
      rw [chainX, ← image_lfX e₀ T, image_image]; rfl
    rw [hX]
    exact chainLink_refiner (by omega) (lfX_injOn e₀ T)
      (fun i hi => lk_lfX hXr hT hi (by omega))
  · have hm := lfM_pos hT
    unfold lfEndsN
    rw [singleton_subset_iff]
    unfold lfRN chainRN at hy
    rcases lab_cases y with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
    · exact absurd hy not_mem_Rlab_xl
    · simp only [vtx, zl, vb]
      split_ifs with h
      · exact lfZ_mem (t := ⟨T, k / 2⟩) hXr (by omega) (mem_lfI.2 ⟨hT, by simp; omega⟩)
      · exact hσZ ⟨T, _⟩ (mem_lfI.2 ⟨hT, by simp; omega⟩)

/-- **Density of the link pieces.** -/
theorem lf_density {q : ℕ} (hXr : MIsRGraph r ends X) (hr : 2 ≤ r) (hU : ∀ x ∈ X, ends x ⊆ U)
    {D : ℕ} (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D)
    {σ : LfItem n → Fin n} {cap : ℕ}
    (hload : ∀ k v, ((lfI ends Z X r).filter fun t =>
      k ∈ lfK ends Z X r e₀ v₀ t ∧ σ t = v).card ≤ cap)
    (J : Finset (Fin n)) (hJ : J.card ≤ r - 1) :
    ∑ T ∈ (outParts ends Z (r - 1) X).filter (fun T => J \ Z ⊆ T),
      ((lfW ends Z X e₀ q T).filter fun W =>
        J ∩ Z ⊆ W.biUnion (lE ends Z (lfEndsN ends Z X e₀ v₀ σ) T)).card ≤
      (4 * q + 1) * ((2 * D + 2 * cap) * U.card ^ (r - 1 - J.card)) := by
  set F := (outParts ends Z (r - 1) X).filter (fun T => J \ Z ⊆ T)
  calc _ ≤ ∑ T ∈ F, (4 * q + 1) * ((range (lfM ends Z X T)).filter
        (GoodSlot (lfM ends Z X T) (lfZ ends Z X e₀ v₀ T) (fun i => σ ⟨T, i⟩) (J ∩ Z))).card := by
        refine sum_le_sum fun T hT => ?_
        have hT' := (mem_filter.1 hT).1
        rw [lE_lfEndsN]
        exact chainFam_count_le (lfM_pos hT') (lfX_injOn e₀ T)
          (fun i hi => lk_lfX hXr hT' hi (by omega)) _
    _ = (4 * q + 1) * ((lfI ends Z X r).filter fun t =>
          t.1 ∈ F ∧ lfGood ends Z X e₀ v₀ σ (J ∩ Z) t).card := by
        rw [← mul_sum]
        congr 1
        exact sum_card_slots F (filter_subset _ _) _
    _ ≤ (4 * q + 1) * ((lfI ends Z X r).filter fun t =>
          J \ Z ⊆ t.1 ∧ lfGood ends Z X e₀ v₀ σ (J ∩ Z) t).card := by
        refine Nat.mul_le_mul_left _ (card_le_card fun t ht => ?_)
        simp only [mem_filter, F] at ht ⊢
        exact ⟨ht.1, ht.2.1.2, ht.2.2⟩
    _ ≤ _ := Nat.mul_le_mul_left _ (lf_slot_count hXr hr hU hdeg hload J hJ)

theorem mdeg_empty_eq {α β : Type*} [DecidableEq β] (f : α → Finset β) (G : Finset α) :
    mdeg f G ∅ = G.card := by
  unfold mdeg; rw [filter_true_of_mem (fun _ _ => empty_subset _)]

/-- **Degrees of the link refiners.** -/
theorem lf_degSum {q : ℕ} (hXr : MIsRGraph r ends X) (hr : 2 ≤ r) (hq : 1 ≤ q)
    {D : ℕ} (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D)
    {σ : LfItem n → Fin n} {cap : ℕ}
    (hload : ∀ k v, ((lfI ends Z X r).filter fun t =>
      k ∈ lfK ends Z X r e₀ v₀ t ∧ σ t = v).card ≤ cap)
    (S : Finset (Fin n)) (hS : S.card = r - 1) :
    ∑ T ∈ (outParts ends Z (r - 1) X).filter (fun T => S \ Z ⊆ T),
      mdeg (lfEndsN ends Z X e₀ v₀ σ T) (lfRN ends Z X q T) (S ∩ Z) ≤
      4 * (q - 1) * D + (q - 1) * (D + 3 * cap) := by
  set F := (outParts ends Z (r - 1) X).filter (fun T => S \ Z ⊆ T)
  have hsplit := card_sdiff_add_card_inter S Z
  rcases Nat.lt_or_ge (S ∩ Z).card 2 with h2 | h2
  · interval_cases hc : (S ∩ Z).card
    · rw [card_eq_zero] at hc
      have hSZ : S \ Z = S := by
        ext v; simp only [mem_sdiff]
        constructor
        · exact fun h => h.1
        · intro hv; refine ⟨hv, fun hz => ?_⟩
          have : v ∈ S ∩ Z := mem_inter.2 ⟨hv, hz⟩
          rw [hc] at this; simp at this
      have hF : F ⊆ {S} := by
        intro T hT
        simp only [F, mem_filter, hSZ] at hT
        rw [mem_singleton]
        exact (eq_of_subset_of_card_le hT.2 (by rw [(outParts_card hT.1).1]; omega)).symm
      by_cases hS' : S ∈ outParts ends Z (r - 1) X
      · refine le_trans (sum_le_sum_of_subset hF) ?_
        rw [sum_singleton, hc, mdeg_empty_eq]
        refine le_trans ?_ (Nat.le_add_right _ _)
        have hm : lfM ends Z X S ≤ D := by
          refine le_trans (card_le_card ?_) (hdeg S hS)
          intro x hx
          obtain ⟨hx, hxS⟩ := mem_lnk'.1 hx
          exact mem_filter.2 ⟨hx, hxS ▸ sdiff_subset⟩
        have hm1 := lfM_pos hS'
        calc (lfRN ends Z X q S).card ≤ (2 * lfM ends Z X S + 2) * (q - 1) := card_chainRN_le hq
          _ ≤ (4 * lfM ends Z X S) * (q - 1) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ 4 * (q - 1) * D := by nlinarith
      · have : F = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro T hT
          have := mem_singleton.1 (hF hT)
          subst this
          exact hS' (mem_filter.1 hT).1
        rw [this, sum_empty]; exact Nat.zero_le _
    · obtain ⟨w, hw⟩ := card_eq_one.1 hc
      rw [hw]
      refine le_trans ?_ (Nat.le_add_left _ _)
      calc _ ≤ ∑ T ∈ F, (q - 1) * (((range (lfM ends Z X T)).filter
            fun i => lfZ ends Z X e₀ v₀ T i = w).card +
            3 * ((range (lfM ends Z X T)).filter fun i => σ ⟨T, i⟩ = w).card) :=
            sum_le_sum fun T hT => mdeg_chainRN_singleton (lfM_pos (mem_filter.1 hT).1) _ _ w
        _ = (q - 1) * (((lfI ends Z X r).filter fun t =>
              t.1 ∈ F ∧ lfZ ends Z X e₀ v₀ t.1 t.2 = w).card +
            3 * ((lfI ends Z X r).filter fun t => t.1 ∈ F ∧ σ t = w).card) := by
            rw [← mul_sum, sum_add_distrib, ← mul_sum,
              sum_card_slots F (filter_subset _ _) (fun T i => lfZ ends Z X e₀ v₀ T i = w),
              sum_card_slots F (filter_subset _ _) (fun T i => σ ⟨T, i⟩ = w)]
        _ ≤ (q - 1) * (D + 3 * cap) := by
            refine Nat.mul_le_mul_left _ (Nat.add_le_add ?_ (Nat.mul_le_mul_left _ ?_))
            · refine le_trans (card_le_card ?_)
                ((card_slots_input_le (Z := Z) (e₀ := e₀) (v₀ := v₀) hXr (by omega) (S \ Z) w).trans ?_)
              · intro t ht
                simp only [mem_filter, F] at ht ⊢
                exact ⟨ht.1, ht.2.1.2, ht.2.2⟩
              · have : insert w (S \ Z) = S := by
                  ext v
                  simp only [mem_insert, mem_sdiff]
                  constructor
                  · rintro (h | ⟨h, -⟩)
                    · have : w ∈ S ∩ Z := hw ▸ mem_singleton_self w
                      rw [h]; exact (mem_inter.1 this).1
                    · exact h
                  · intro hv
                    by_cases hz : v ∈ Z
                    · left
                      have : v ∈ S ∩ Z := mem_inter.2 ⟨hv, hz⟩
                      rw [hw] at this
                      exact mem_singleton.1 this
                    · exact Or.inr ⟨hv, hz⟩
                rw [this]; exact hdeg S hS
            · refine le_trans (card_le_card ?_) (hload (S \ Z, ∅) w)
              intro t ht
              simp only [mem_filter, F] at ht ⊢
              exact ⟨ht.1, mem_lfK_A.2 ⟨ht.2.1.2, by omega⟩, ht.2.2⟩
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    exact sum_eq_zero fun T _ => mdeg_chainRN_eq_zero _ _ h2

end Links

/-- **The last flat step in `Fin n`, with spread `1`-uniform link refiners.**  For `2 ≤ r < q`
and `K` there are constants `Cs, C'` such that: if `X` is an `(r-1)`-flat `r`-multigraph on
`Fin n` with respect to a reserve `Z` with `|Z| ≥ q + r`, all copies of `X` lie in a set `U` with
`|U| ≤ K · |Z|`, every `(r-1)`-set lies in at most `D` copies of `X` (`1 ≤ D`) and
`Cs · D ≤ |Z|`, then `X` has a residual `K_q^r`-refiner whose residue is `(r-2)`-flat and lies in
`X ∪ R`, whose new copies lie in `T ∪ Z` for an outside part `T`, and whose new copies have
`(r-1)`-degrees at most `C' · D`.  No link refiners are assumed: they are the spread chain
refiners built above. -/
theorem placedLastFlatStep (q r K : ℕ) (hr : 2 ≤ r) (hrq : r < q) :
    ∃ Cs C' : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat (r - 1) Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      ∃ (endsN : Finset (Fin n) → Lab → Finset (Fin n)) (R Y : Finset (E ⊕ FLab (Fin n) E Lab))
        (𝒲' : Finset (Finset (E ⊕ FLab (Fin n) E Lab))),
        IsResidualMultiRefiner q r (flatConst q r (4 * (q - (r - 1)) + 1)) (fEnds ends endsN)
          (X.image Sum.inl) R Y 𝒲' ∧
        IsFlat (r - 1 - 1) Z (fEnds ends endsN) Y ∧
        (∀ x, Sum.inl x ∈ Y → x ∈ X ∧ (ends x \ Z).card < r - 1) ∧
        Y ⊆ X.image Sum.inl ∪ R ∧ (∀ c ∈ R, ∀ x, c ≠ Sum.inl x) ∧
        (∀ c ∈ R, ∃ T ∈ outParts ends Z (r - 1) X, fEnds ends endsN c ⊆ T ∪ Z) ∧
        ∀ S : Finset (Fin n), S.card = r - 1 → mdeg (fEnds ends endsN) R S ≤ C' * D := by
  set q' := q - (r - 1) with hq'
  obtain ⟨Cs, Cs', hCs, hflat⟩ := placedFlatStep_link q r (r - 1) (4 * q' + 1) (by omega) hrq
  set capC := 3 * 2 ^ (r - 1) * (3 + 2 * K) + 1 with hcapC
  set Cd := (4 * q' + 1) * (2 + 2 * capC) * (K + 1) ^ (r - 1) with hCd
  have hCd0 : 0 < Cd := by positivity
  refine ⟨Cs, 4 * (q' - 1) + (q' - 1) * (1 + 3 * capC) + Cs' * Cd, hCs, ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 hCD hdeg
  have hZ0 : 0 < Z.card := by omega
  obtain ⟨v₀, -⟩ := card_pos.1 hZ0
  have hCDd : Cs ≤ Z.card := hCD
  have hcap : lfCap r K D ≤ capC * D := by
    have e : lfCap r K D = (3 * 2 ^ (r - 1) * (3 + 2 * K)) * D + 1 := by unfold lfCap; ring
    have e2 : capC * D = (3 * 2 ^ (r - 1) * (3 + 2 * K)) * D + D := by rw [hcapC]; ring
    omega
  have hpow : ∀ e ≤ r - 1, U.card ^ e ≤ (K + 1) ^ (r - 1) * Z.card ^ e := by
    intro e he
    calc U.card ^ e ≤ ((K + 1) * Z.card) ^ e :=
          Nat.pow_le_pow_left (hUK.trans (Nat.mul_le_mul_right _ (by omega))) _
      _ = (K + 1) ^ e * Z.card ^ e := mul_pow _ _ _
      _ ≤ (K + 1) ^ (r - 1) * Z.card ^ e :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) he)
  by_cases hXne : X.Nonempty
  · obtain ⟨e₀, -⟩ := hXne
    obtain ⟨σ, hσZ, hload⟩ := lf_pivots (e₀ := e₀) (v₀ := v₀) hXr hr hU hUK hZ0 hdeg
    obtain ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, h7, -⟩ := hflat n ends Z (lfEndsN ends Z X e₀ v₀ σ) X
      (lfRN ends Z X q') (lfW ends Z X e₀ q') (Cd * D) hXr hX
      (lf_linkRefiners hXr hr hrq hσZ) hZq hCDd (fun J hJ => by
        refine (lf_density hXr hr hU hdeg hload J hJ).trans ?_
        have h2D : 2 * D + 2 * lfCap r K D ≤ (2 + 2 * capC) * D := by nlinarith
        calc (4 * q' + 1) * ((2 * D + 2 * lfCap r K D) * U.card ^ (r - 1 - J.card))
            ≤ (4 * q' + 1) * (((2 + 2 * capC) * D) *
                ((K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card))) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul h2D (hpow _ (by omega)))
          _ = Cd * D * Z.card ^ (r - 1 - J.card) := by rw [hCd]; ring)
    refine ⟨lfEndsN ends Z X e₀ v₀ σ, R, Y, 𝒲', h1, h2, h3, h4, h5, h6, fun S hS => ?_⟩
    refine (h7 S hS).trans ?_
    have hsum := lf_degSum (q := q') hXr hr (by omega) hdeg hload S hS
    have hb : 4 * (q' - 1) * D + (q' - 1) * (D + 3 * lfCap r K D) ≤
        (4 * (q' - 1) + (q' - 1) * (1 + 3 * capC)) * D := by
      have : (q' - 1) * (D + 3 * lfCap r K D) ≤ (q' - 1) * ((1 + 3 * capC) * D) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      nlinarith
    calc _ ≤ (4 * (q' - 1) + (q' - 1) * (1 + 3 * capC)) * D + Cs' * (Cd * D) :=
          Nat.add_le_add_right (hsum.trans hb) _
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty] at hXne
    subst hXne
    have hout : outParts ends Z (r - 1) (∅ : Finset E) = ∅ := by simp [outParts]
    obtain ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, h7, -⟩ := hflat n ends Z
      (fun _ _ => (∅ : Finset (Fin n))) (∅ : Finset E) (fun _ => (∅ : Finset Lab))
      (fun _ => ∅) (Cd * D) hXr hX
      ⟨fun T hT => by rw [hout] at hT; simp at hT, fun T hT => by rw [hout] at hT; simp at hT⟩
      hZq hCDd (fun J _ => by rw [hout]; simp)
    refine ⟨fun _ _ => ∅, R, Y, 𝒲', h1, h2, h3, h4, h5, h6, fun S hS => ?_⟩
    refine (h7 S hS).trans ?_
    rw [hout, filter_empty, sum_empty, zero_add]
    calc Cs' * (Cd * D) ≤ (4 * (q' - 1) + (q' - 1) * (1 + 3 * capC)) * D + Cs' * (Cd * D) :=
          Nat.le_add_left _ _
      _ = _ := by ring

end RefinedAbsorption.Placement
