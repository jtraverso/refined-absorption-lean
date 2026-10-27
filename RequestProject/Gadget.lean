module
public import RequestProject.Counting

/-!
# Edge gadgets

For `r ≤ q` there are weights `w 0, …, w r` (depending only on `q` and `r`) with the following
property: whenever `e` is an `r`-set and `W` a disjoint `q`-set, giving every `q`-subset `Q` of
`e ∪ W` the weight `w |Q ∩ e|` produces total weight `1` on `e` and `0` on every other
`r`-subset of `e ∪ W`.  (The linear system for the weights is triangular.)

These gadgets are used to correct the clique degrees in the proof of the boost lemma.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V]

/-- `ccount m s j` is the number of `j`-subsets of an `m`-set containing a fixed `s`-subset. -/
def ccount (m s j : ℕ) : ℕ := if s ≤ j then (m - s).choose (j - s) else 0

theorem card_filter_superset_eq_ccount {T P : Finset V} (hP : P ⊆ T) (j : ℕ) :
    ((T.powersetCard j).filter (fun Q => P ⊆ Q)).card = ccount T.card P.card j := by
  unfold ccount
  split_ifs with h
  · exact card_powersetCard_filter_superset hP h
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro Q hQ hPQ
    exact h ((card_le_card hPQ).trans (mem_powersetCard.1 hQ).2.le)

/-- Counting the `q`-subsets `Q ⊇ f` of `e ∪ W` with `|Q ∩ e| = j`. -/
theorem card_gadget_fiber {e W f : Finset V} (heW : Disjoint e W) (hf : f ⊆ e ∪ W) {q j : ℕ}
    (hj : j ≤ q) :
    (((e ∪ W).powersetCard q).filter (fun Q => f ⊆ Q ∧ (Q ∩ e).card = j)).card =
      ccount e.card (f ∩ e).card j * ccount W.card (f ∩ W).card (q - j) := by
  rw [← card_filter_superset_eq_ccount inter_subset_right,
    ← card_filter_superset_eq_ccount inter_subset_right, ← card_product]
  refine card_nbij' (fun Q => (Q ∩ e, Q ∩ W)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro Q hQ
    simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hQ
    obtain ⟨⟨hQs, hQc⟩, hfQ, hQe⟩ := hQ
    have hsplit : (Q ∩ e).card + (Q ∩ W).card = Q.card := by
      rw [← card_union_of_disjoint (disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right heW))]
      congr 1
      ext a; simp only [mem_union, mem_inter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h; rcases mem_union.1 (hQs h) with h' | h' <;> simp [h, h']
    simp only [coe_product, coe_filter, mem_powersetCard, Set.mem_prod, Set.mem_setOf_eq]
    refine ⟨⟨⟨inter_subset_right, hQe⟩, inter_subset_inter_right hfQ⟩,
      ⟨⟨inter_subset_right, by omega⟩, inter_subset_inter_right hfQ⟩⟩
  · rintro ⟨A, B⟩ h
    simp only [coe_product, coe_filter, mem_powersetCard, Set.mem_prod, Set.mem_setOf_eq] at h
    obtain ⟨⟨⟨hAe, hAc⟩, hfA⟩, ⟨⟨hBW, hBc⟩, hfB⟩⟩ := h
    have hAB : Disjoint A B := disjoint_of_subset_left hAe (disjoint_of_subset_right hBW heW)
    simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq]
    refine ⟨⟨union_subset_union hAe hBW, by rw [card_union_of_disjoint hAB]; omega⟩, ?_, ?_⟩
    · intro a ha
      rcases mem_union.1 (hf ha) with h | h
      · exact mem_union_left _ (hfA (mem_inter.2 ⟨ha, h⟩))
      · exact mem_union_right _ (hfB (mem_inter.2 ⟨ha, h⟩))
    · rw [union_inter_distrib_right, inter_eq_left.2 hAe,
        disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hBW heW.symm), union_empty, hAc]
  · intro Q hQ
    simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hQ
    simp only
    rw [← inter_union_distrib_left, inter_eq_left.2 hQ.1.1]
  · rintro ⟨A, B⟩ h
    simp only [coe_product, coe_filter, mem_powersetCard, Set.mem_prod, Set.mem_setOf_eq] at h
    obtain ⟨⟨⟨hAe, -⟩, -⟩, ⟨⟨hBW, -⟩, -⟩⟩ := h
    simp only [Prod.mk.injEq]
    constructor
    · rw [union_inter_distrib_right, inter_eq_left.2 hAe,
        disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hBW heW.symm), union_empty]
    · rw [union_inter_distrib_right, inter_eq_left.2 hBW,
        disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hAe heW), empty_union]

/-- The (upper triangular) matrix of the linear system defining the gadget weights. -/
noncomputable def gadgetMatrix (q r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => ((ccount r i j * ccount q (r - i) (q - j) : ℕ) : ℝ)

theorem gadgetMatrix_det_ne_zero {q r : ℕ} (hrq : r ≤ q) : (gadgetMatrix q r).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular]
  · rw [prod_ne_zero_iff]
    intro i _
    have hi := i.isLt
    simp only [gadgetMatrix, ccount, le_refl, if_true, Nat.sub_self, Nat.choose_zero_right,
      one_mul, Nat.cast_ne_zero]
    rw [if_pos (by omega)]
    exact (Nat.choose_pos (by omega)).ne'
  · intro i j hij
    simp only [gadgetMatrix, ccount]
    rw [if_neg (by exact not_le.2 hij)]
    simp

/-- The vector of gadget weights. -/
noncomputable def gadgetVec (q r : ℕ) : Fin (r + 1) → ℝ :=
  (gadgetMatrix q r)⁻¹.mulVec (Pi.single (Fin.last r) 1)

/-- The gadget weight of a `q`-subset meeting the special edge in `j` vertices. -/
noncomputable def gadgetWeight (q r : ℕ) (j : ℕ) : ℝ :=
  if h : j < r + 1 then gadgetVec q r ⟨j, h⟩ else 0

theorem gadgetMatrix_mulVec {q r : ℕ} (hrq : r ≤ q) :
    (gadgetMatrix q r).mulVec (gadgetVec q r) = Pi.single (Fin.last r) 1 := by
  unfold gadgetVec
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.2 (gadgetMatrix_det_ne_zero hrq)), Matrix.one_mulVec]

/-- A uniform bound for the gadget weights. -/
noncomputable def gadgetBound (q r : ℕ) : ℝ := ∑ j, |gadgetVec q r j|

theorem abs_gadgetWeight_le (q r j : ℕ) : |gadgetWeight q r j| ≤ gadgetBound q r := by
  unfold gadgetWeight gadgetBound
  split_ifs with h
  · exact single_le_sum (f := fun j => |gadgetVec q r j|) (fun _ _ => abs_nonneg _)
      (mem_univ (⟨j, h⟩ : Fin (r + 1)))
  · simp only [abs_zero]
    exact sum_nonneg fun _ _ => abs_nonneg _

theorem gadgetBound_nonneg (q r : ℕ) : 0 ≤ gadgetBound q r :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- **The gadget identity.**  For an `r`-set `e`, a disjoint `q`-set `W` and an `r`-set
`f ⊆ e ∪ W`, the total gadget weight of the `q`-subsets of `e ∪ W` containing `f` is `1` if
`f = e` and `0` otherwise. -/
theorem gadget_sum {q r : ℕ} (hrq : r ≤ q) {e W f : Finset V} (heW : Disjoint e W)
    (he : e.card = r) (hW : W.card = q) (hf : f ⊆ e ∪ W) (hfr : f.card = r) :
    ∑ Q ∈ ((e ∪ W).powersetCard q).filter (fun Q => f ⊆ Q), gadgetWeight q r (Q ∩ e).card =
      if f = e then 1 else 0 := by
  set i := (f ∩ e).card with hi
  have hir : i ≤ r := he ▸ card_le_card inter_subset_right
  have hfW : (f ∩ W).card = r - i := by
    have : (f ∩ e).card + (f ∩ W).card = f.card := by
      rw [← card_union_of_disjoint (disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right heW)), ← inter_union_distrib_left,
        inter_eq_left.2 hf]
    omega
  rw [← sum_fiberwise_of_maps_to (g := fun Q => (Q ∩ e).card) (t := range (r + 1))]
  swap
  · intro Q _
    rw [mem_range, Nat.lt_succ_iff, ← he]
    exact card_le_card inter_subset_right
  rw [sum_range]
  have h1 : ∀ j : Fin (r + 1),
      ∑ Q ∈ (((e ∪ W).powersetCard q).filter (fun Q => f ⊆ Q)).filter
        (fun Q => (Q ∩ e).card = j), gadgetWeight q r (Q ∩ e).card =
      gadgetMatrix q r ⟨i, by omega⟩ j * gadgetVec q r j := by
    intro j
    have hj' : (j : ℕ) < r + 1 := j.isLt
    rw [sum_congr rfl (g := fun _ => gadgetWeight q r j) (fun Q hQ => by
      rw [(mem_filter.1 hQ).2]), sum_const, filter_filter, card_gadget_fiber heW hf (by omega),
      he, hW, hfW]
    simp [gadgetMatrix, gadgetWeight, hj', nsmul_eq_mul, hi]
  rw [Fintype.sum_congr _ _ h1]
  have h2 := congrFun (gadgetMatrix_mulVec (q := q) hrq) ⟨i, by omega⟩
  simp only [Matrix.mulVec, dotProduct] at h2
  rw [h2]
  have hfe : f = e ↔ i = r := by
    constructor
    · rintro rfl; rw [hi, inter_self, hfr]
    · intro h
      have h3 : f ∩ e = e := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact (eq_of_subset_of_card_le (h3 ▸ inter_subset_left : e ⊆ f) (by omega)).symm
  by_cases h : i = r
  · rw [if_pos (hfe.2 h)]
    have : (⟨i, by omega⟩ : Fin (r + 1)) = Fin.last r := Fin.ext h
    rw [this, Pi.single_eq_same]
  · rw [if_neg (fun h' => h (hfe.1 h'))]
    have : (⟨i, by omega⟩ : Fin (r + 1)) ≠ Fin.last r := fun h' => h (congrArg Fin.val h')
    rw [Pi.single_eq_of_ne this]

end RefinedAbsorption
