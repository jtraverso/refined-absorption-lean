module
public import RequestProject.RefinerOne.Chain
public import RequestProject.MultiRefiner.Basic

/-!
# Spread chain refiners for `1`-uniform links

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, the case of
`1`-uniform links).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

In the last flat step (from `(r-1)`-flat to `(r-2)`-flat) the links are `1`-uniform: each copy of
the link of an outside `(r-1)`-set `T` is a single reserve vertex `z_i`.  We refine such a link
with the chain refiner of the case `r = 1` (`ChainRefiner`), run on `2m` slots: the input `i`
sits at the even slot `2i`, the odd slots are dummy slots.  The labels of the chain are placed as
follows:

* the labels of block `2i` sit at the vertex `z_i` of the `i`-th input (so the reservoir is
  spread exactly like the link itself);
* the labels of block `2i + 1` sit at a *pivot* `p_i`, a reserve vertex that can be chosen freely
  (later, by a greedy balancing argument);
* the last two blocks sit at `p_{m-1}`.

Then every piece has vertex set inside `{z_i, p_i}` or `{p_i, z_{i+1}}` for some `i`
(`chainFam_support`): no piece contains two input vertices.  This is what makes the pieces of the
links of different outside sets spread over the reserve.

* `chainLink_refiner`: the construction is a `K_q^1`-multi-refiner with constant `4q + 1`.
* `chainFam_count_le`: number of pieces whose vertex set contains a given set.
* `chainR_count_le`, `card_chainR_le`: the reservoir labels at a given vertex, and their total.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown.ChainLink

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.ChainRefiner

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The vertex of the labels of block `k`. -/
def vb (m : ℕ) (z p : ℕ → V) (k : ℕ) : V :=
  if k % 2 = 0 ∧ k < 2 * m then z (k / 2) else p (min (k / 2) (m - 1))

/-- The vertex of a label (input labels sit at their input vertex). -/
def vtx (m : ℕ) (z p : ℕ → V) : Lab → V
  | Sum.inl k => z (k / 2)
  | Sum.inr kj => vb m z p kj.1

/-- The relabelling of the chain labels: valid input labels become the link copies. -/
def labMap (m : ℕ) (x : ℕ → E) : Lab → E ⊕ Lab
  | Sum.inl k => if k % 2 = 0 ∧ k < 2 * m then Sum.inl (x (k / 2)) else Sum.inr (Sum.inl k)
  | Sum.inr kj => Sum.inr (Sum.inr kj)

/-- The ends of the chain refiner. -/
def cEnds (lkE : E → Finset V) (m : ℕ) (z p : ℕ → V) : E ⊕ Lab → Finset V :=
  Sum.elim lkE fun y => {vtx m z p y}

/-- The admissible piece indices: no input at the dummy (odd) slots. -/
def cIdx (q m : ℕ) : Finset (ℕ × ℕ × Bool) :=
  (Idx q (2 * m)).filter fun i => ¬ (i.1 % 2 = 1 ∧ i.2.2 = true)

/-- The pieces of the chain refiner. -/
def chainFam (q m : ℕ) (x : ℕ → E) : Finset (Finset (E ⊕ Lab)) :=
  (cIdx q m).image (fun i => (piece q i.1 i.2.1 i.2.2).image (labMap m x)) ∪
    {(finPiece q (2 * m)).image (labMap m x)}

/-- The inputs. -/
def chainX (m : ℕ) (x : ℕ → E) : Finset (E ⊕ Lab) := (range m).image fun i => Sum.inl (x i)

/-- The reservoir labels. -/
def chainRN (q m : ℕ) : Finset Lab := Rlab q (2 * m)

/-- The reservoir. -/
def chainR (q m : ℕ) : Finset (E ⊕ Lab) := (chainRN q m).image Sum.inr

theorem labMap_injective {m : ℕ} {x : ℕ → E} (hx : Set.InjOn x (range m)) :
    Function.Injective (labMap m x) := by
  intro a b h
  rcases a with k | kj <;> rcases b with k' | kj'
  · simp only [labMap] at h
    split_ifs at h with h1 h2 h2
    · have := hx (by simp; omega) (by simp; omega) (Sum.inl_injective h)
      congr 1; omega
    all_goals simp at h
    rw [h]
  · simp only [labMap] at h; split_ifs at h <;> simp at h
  · simp only [labMap] at h; split_ifs at h <;> simp at h
  · simp [labMap] at h; rw [h]

theorem labMap_zl (m : ℕ) (x : ℕ → E) (k j : ℕ) :
    labMap m x (zl k j) = Sum.inr (zl k j) := rfl

theorem labMap_xl_even {m : ℕ} (x : ℕ → E) {i : ℕ} (hi : i < m) :
    labMap m x (xl (2 * i)) = Sum.inl (x i) := by
  simp only [labMap, xl]
  rw [if_pos (by omega)]
  congr 2; omega

theorem labMap_of_mem_Rlab {q M m : ℕ} (x : ℕ → E) {y : Lab} (hy : y ∈ Rlab q M) :
    labMap m x y = Sum.inr y := by
  rcases lab_cases y with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · exact absurd hy not_mem_Rlab_xl
  · rfl

/-- The labels of an admissible piece go to the inputs or to the reservoir. -/
theorem labMap_piece_mem {q m : ℕ} (hq : 1 ≤ q) (x : ℕ → E) {i : ℕ × ℕ × Bool}
    (hi : i ∈ cIdx q m) {a : Lab} (ha : a ∈ piece q i.1 i.2.1 i.2.2) :
    labMap m x a ∈ chainX m x ∪ chainR q m := by
  simp only [cIdx, Idx, mem_filter, mem_product, mem_range, mem_univ, and_true] at hi
  obtain ⟨⟨hk, ht⟩, hodd⟩ := hi
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · rw [mem_piece_xl] at ha
    obtain ⟨he, rfl⟩ := ha
    have hev : i.1 % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one i.1 with h | h
      · exact h
      · exact absurd ⟨h, he⟩ hodd
    have h2 : i.1 = 2 * (i.1 / 2) := by omega
    rw [h2, labMap_xl_even x (by omega)]
    exact mem_union_left _ (mem_image.2 ⟨i.1 / 2, mem_range.2 (by omega), rfl⟩)
  · have hs := piece_subset (m := 2 * m) hq hk ht ha
    rw [mem_union] at hs
    rcases hs with hs | hs
    · rw [labMap_zl]
      exact mem_union_right _ (mem_image.2 ⟨_, hs, rfl⟩)
    · exact absurd hs not_mem_Xlab_zl

theorem labMap_finPiece_mem {q m : ℕ} (hq : 1 ≤ q) (x : ℕ → E) {a : Lab}
    (ha : a ∈ finPiece q (2 * m)) : labMap m x a ∈ chainR q m := by
  have hs := finPiece_subset hq ha
  rw [mem_union] at hs
  rcases hs with hs | hs
  · rw [labMap_of_mem_Rlab x hs]; exact mem_image.2 ⟨_, hs, rfl⟩
  · rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
    · exact absurd ha not_mem_finPiece_xl
    · exact absurd hs not_mem_Xlab_zl

theorem exists_labMap_eq {q m : ℕ} {x : ℕ → E} {c : E ⊕ Lab}
    (hc : c ∈ chainX m x ∪ chainR q m) : ∃ a, labMap m x a = c := by
  rcases mem_union.1 hc with hc | hc
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
    exact ⟨_, labMap_xl_even x (mem_range.1 hi)⟩
  · obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    exact ⟨y, labMap_of_mem_Rlab x hy⟩

theorem card_filter_chainFam_le {q m : ℕ} {x : ℕ → E} (hx : Set.InjOn x (range m)) (a : Lab) :
    ((chainFam q m x).filter fun W => labMap m x a ∈ W).card ≤ 4 * q + 1 := by
  have hinj := labMap_injective hx
  unfold chainFam
  rw [filter_union]
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ ((card_filter_le _ _).trans (by simp)))
  rw [filter_image]
  refine card_image_le.trans ?_
  refine le_trans (card_le_card ?_) (card_filter_piece_le q (2 * m) a)
  intro i hi
  simp only [mem_filter, Function.comp, hinj.mem_finset_image] at hi ⊢
  simp only [cIdx, mem_filter] at hi
  exact ⟨hi.1.1, hi.2⟩

theorem card_piece_dvd {q k t : ℕ} {e : Bool} (hq : 1 ≤ q) (ht : t < q) :
    q ∣ (piece q k t e).card := by
  rw [card_piece hq ht]; split_ifs <;> simp

theorem card_finPiece_dvd {q M : ℕ} (hq : 1 ≤ q) : q ∣ (finPiece q M).card := by
  rw [card_finPiece hq]; split_ifs <;> simp

/-- `K_q^1`-divisibility is divisibility of the number of copies by `q`. -/
theorem mIsDivisible_one_iff {q : ℕ} {ends : E ⊕ Lab → Finset V} {W : Finset (E ⊕ Lab)} :
    MIsDivisible q 1 ends W ↔ q ∣ W.card := by
  constructor
  · intro h
    have := h ∅ (by simp)
    simpa [mdeg] using this
  · intro h S hS
    have : S = ∅ := card_eq_zero.1 (by omega)
    subst this
    simpa [mdeg] using h

/-- The selection of the chain run for an input set `L`. -/
def selB (m : ℕ) (x : ℕ → E) (L : Finset (E ⊕ Lab)) (k : ℕ) : Bool :=
  decide (k % 2 = 0 ∧ k < 2 * m ∧ Sum.inl (x (k / 2)) ∈ L)

theorem image_Llab_selB {m : ℕ} {x : ℕ → E} {L : Finset (E ⊕ Lab)} (hL : L ⊆ chainX m x) :
    (Llab (selB m x L) (2 * m)).image (labMap m x) = L := by
  ext c
  simp only [mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [Llab, mem_image, mem_filter, mem_range] at ha
    obtain ⟨k, ⟨hk, hb⟩, rfl⟩ := ha
    simp only [selB, decide_eq_true_eq] at hb
    simp only [labMap, xl, if_pos (show k % 2 = 0 ∧ k < 2 * m from ⟨hb.1, hb.2.1⟩)]
    exact hb.2.2
  · intro hc
    obtain ⟨i, hi, rfl⟩ := mem_image.1 (hL hc)
    rw [mem_range] at hi
    refine ⟨xl (2 * i), ?_, labMap_xl_even x hi⟩
    simp only [Llab, mem_image, mem_filter, mem_range]
    refine ⟨2 * i, ⟨by omega, ?_⟩, rfl⟩
    simp only [selB, decide_eq_true_eq]
    refine ⟨by omega, by omega, ?_⟩
    rwa [show 2 * i / 2 = i by omega]

/-- **The chain refiner of a `1`-uniform link** is a `K_q^1`-multi-refiner with constant
`4q + 1`, for any placement `z` of the inputs and any choice of pivots `p`. -/
theorem chainLink_refiner {q m : ℕ} (hq : 1 ≤ q) {x : ℕ → E} (hx : Set.InjOn x (range m))
    {lkE : E → Finset V} {z p : ℕ → V} (hlk : ∀ i < m, lkE (x i) = {z i}) :
    IsMultiRefiner q 1 (4 * q + 1) (cEnds lkE m z p) (chainX m x) (chainR q m)
      (chainFam q m x) := by
  have hinj := labMap_injective hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
      simp [cEnds, hlk i (mem_range.1 hi)]
    · obtain ⟨y, -, rfl⟩ := mem_image.1 hc
      simp [cEnds]
  · rw [disjoint_left]
    intro c h1 h2
    obtain ⟨i, -, rfl⟩ := mem_image.1 h1
    obtain ⟨y, -, hy⟩ := mem_image.1 h2
    simp at hy
  · intro W hW
    rw [mIsDivisible_one_iff]
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      simp only [cIdx, Idx, mem_filter, mem_product, mem_range] at hi
      rw [card_image_of_injective _ hinj]
      exact card_piece_dvd hq hi.1.2.1
    · rw [mem_singleton.1 hW, card_image_of_injective _ hinj]
      exact card_finPiece_dvd hq
  · intro W hW c hc
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
      exact labMap_piece_mem hq x hi ha
    · rw [mem_singleton.1 hW] at hc
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
      exact mem_union_right _ (labMap_finPiece_mem hq x ha)
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      simp only [cIdx, Idx, mem_filter, mem_product, mem_range] at hi
      rw [card_image_of_injective _ hinj, card_piece hq hi.1.2.1]
      split_ifs <;> omega
    · rw [mem_singleton.1 hW, card_image_of_injective _ hinj, card_finPiece hq]
      split_ifs <;> omega
  · intro c hc
    obtain ⟨a, rfl⟩ := exists_labMap_eq hc
    exact card_filter_chainFam_le hx a
  · intro L hL hdiv
    rw [mIsDivisible_one_iff] at hdiv
    set b := selB m x L with hb
    have hcnt : q ∣ cnt b (2 * m) := by
      rw [cnt_eq_card, ← card_image_of_injective _ hinj, image_Llab_selB hL]
      exact hdiv
    set 𝒰 : Finset (Finset (E ⊕ Lab)) :=
      (range (2 * m)).image (fun k => (chosen q b k).image (labMap m x)) ∪
        {(finPiece q (2 * m)).image (labMap m x)} with h𝒰
    refine ⟨𝒰, ?_, ∅, subset_rfl, mIsDivisible_empty _ _ _, ?_, by simp, ?_⟩
    · intro W hW
      rcases mem_union.1 hW with hW | hW
      · obtain ⟨k, hk, rfl⟩ := mem_image.1 hW
        refine mem_union_left _ (mem_image.2 ⟨(k, tSeq q b k, b k), ?_, rfl⟩)
        simp only [cIdx, Idx, mem_filter, mem_product, mem_range, mem_univ, and_true]
        refine ⟨⟨mem_range.1 hk, tSeq_lt hq b k⟩, ?_⟩
        rintro ⟨hodd, he⟩
        simp only [hb, selB, decide_eq_true_eq] at he
        omega
      · exact mem_union_right _ hW
    · have hmem : ∀ W ∈ 𝒰, (∃ k < 2 * m, W = (chosen q b k).image (labMap m x)) ∨
          W = (finPiece q (2 * m)).image (labMap m x) := by
        intro W hW
        rcases mem_union.1 hW with hW | hW
        · obtain ⟨k, hk, rfl⟩ := mem_image.1 hW
          exact Or.inl ⟨k, mem_range.1 hk, rfl⟩
        · exact Or.inr (mem_singleton.1 hW)
      intro W hW W' hW' hne
      rw [Function.onFun, id, id, disjoint_left]
      intro c hc hc'
      rcases hmem W hW with ⟨k, hk, rfl⟩ | rfl <;> rcases hmem W' hW' with ⟨k', hk', rfl⟩ | rfl
      · obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
        rw [hinj.mem_finset_image] at hc'
        exact hne (by rw [chosen_unique ha hc'])
      · obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
        rw [hinj.mem_finset_image] at hc'
        exact chosen_not_fin hq hcnt hk ha hc'
      · obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
        rw [hinj.mem_finset_image] at hc'
        exact chosen_not_fin hq hcnt hk' hc' ha
      · exact hne rfl
    · rw [union_empty]
      have hcov := cover hq b (2 * m) hcnt
      have himg : (Rlab q (2 * m) ∪ Llab b (2 * m)).image (labMap m x) = chainR q m ∪ L := by
        rw [image_union, image_Llab_selB hL]
        congr 1
        ext c
        simp only [chainR, chainRN, mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (labMap_of_mem_Rlab x hy).symm⟩
        · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, labMap_of_mem_Rlab x hy⟩
      rw [← himg]
      ext c
      rw [mem_sup, mem_image]
      constructor
      · rintro ⟨W, hW, hcW⟩
        rw [id] at hcW
        rcases mem_union.1 hW with hW | hW
        · obtain ⟨k, hk, rfl⟩ := mem_image.1 hW
          obtain ⟨a, ha, rfl⟩ := mem_image.1 hcW
          exact ⟨a, (hcov a).1 (Or.inl ⟨k, mem_range.1 hk, ha⟩), rfl⟩
        · rw [mem_singleton.1 hW] at hcW
          obtain ⟨a, ha, rfl⟩ := mem_image.1 hcW
          exact ⟨a, (hcov a).1 (Or.inr ha), rfl⟩
      · rintro ⟨a, ha, rfl⟩
        rcases (hcov a).2 ha with ⟨k, hk, hak⟩ | hak
        · exact ⟨_, mem_union_left _ (mem_image.2 ⟨k, mem_range.2 hk, rfl⟩),
            mem_image_of_mem _ hak⟩
        · exact ⟨_, mem_union_right _ (mem_singleton_self _), mem_image_of_mem _ hak⟩

/-! ### Where the pieces and the reservoir sit -/

theorem cEnds_labMap {m : ℕ} {x : ℕ → E} {lkE : E → Finset V} {z p : ℕ → V}
    (hlk : ∀ i < m, lkE (x i) = {z i}) (a : Lab) :
    cEnds lkE m z p (labMap m x a) = {vtx m z p a} := by
  rcases a with k | kj
  · simp only [labMap]
    split_ifs with h
    · simp only [cEnds, Sum.elim_inl, vtx]
      exact hlk _ (by omega)
    · rfl
  · rfl

/-- The vertex set of an image piece. -/
theorem biUnion_image_labMap {m : ℕ} {x : ℕ → E} {lkE : E → Finset V} {z p : ℕ → V}
    (hx : Set.InjOn x (range m)) (hlk : ∀ i < m, lkE (x i) = {z i}) (P : Finset Lab) :
    (P.image (labMap m x)).biUnion (cEnds lkE m z p) = P.image (vtx m z p) := by
  rw [image_biUnion]
  ext v
  simp only [mem_biUnion, cEnds_labMap hlk, mem_singleton, mem_image]
  constructor <;> rintro ⟨a, ha, h⟩ <;> exact ⟨a, ha, h.symm⟩

/-- The pair of vertices supporting slot `i`. -/
def GoodSlot (m : ℕ) (z p : ℕ → V) (A : Finset V) (i : ℕ) : Prop :=
  A ⊆ {z i, p i} ∨ (i + 1 < m ∧ A ⊆ {p i, z (i + 1)})

instance (m : ℕ) (z p : ℕ → V) (A : Finset V) (i : ℕ) : Decidable (GoodSlot m z p A i) := by
  unfold GoodSlot; infer_instance

theorem vb_even {m : ℕ} (z p : ℕ → V) {i : ℕ} (hi : i < m) : vb m z p (2 * i) = z i := by
  simp only [vb]; rw [if_pos (by omega)]; congr 1; omega

theorem vb_odd {m : ℕ} (z p : ℕ → V) {i : ℕ} (hi : i < m) : vb m z p (2 * i + 1) = p i := by
  simp only [vb]; rw [if_neg (by omega)]; congr 1; omega

theorem vb_ge {m : ℕ} (z p : ℕ → V) {k : ℕ} (hk : 2 * m ≤ k) : vb m z p k = p (m - 1) := by
  simp only [vb]; rw [if_neg (by omega)]; congr 1; omega

/-- Every admissible piece sits on the pair of vertices of its slot. -/
theorem image_vtx_piece_subset {q m : ℕ} (z p : ℕ → V) {i : ℕ × ℕ × Bool}
    (hi : i ∈ cIdx q m) {A : Finset V}
    (hA : A ⊆ (piece q i.1 i.2.1 i.2.2).image (vtx m z p)) : GoodSlot m z p A (i.1 / 2) := by
  simp only [cIdx, Idx, mem_filter, mem_product, mem_range, mem_univ, and_true] at hi
  obtain ⟨⟨hk, -⟩, hodd⟩ := hi
  obtain ⟨k, t, e⟩ := i
  simp only at hk hodd hA ⊢
  rcases Nat.mod_two_eq_zero_or_one k with hev | hod
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i := ⟨k / 2, by omega⟩
    rw [show 2 * i / 2 = i by omega]
    left
    refine hA.trans ?_
    intro v hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    rcases lab_cases a with ⟨k', rfl⟩ | ⟨k', j, rfl⟩
    · rw [mem_piece_xl] at ha
      obtain ⟨-, rfl⟩ := ha
      simp [vtx, xl, show 2 * i / 2 = i by omega]
    · rw [mem_piece_zl] at ha
      rcases ha with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simp only [vtx, zl]; rw [vb_even z p (by omega)]; simp
      · simp only [vtx, zl]; rw [vb_odd z p (by omega)]; simp
  · have he : e = false := by
      cases e
      · rfl
      · exact absurd ⟨hod, rfl⟩ hodd
    subst he
    obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
    rw [show (2 * i + 1) / 2 = i by omega]
    by_cases hlt : i + 1 < m
    · right
      refine ⟨hlt, hA.trans ?_⟩
      intro v hv
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
      rcases lab_cases a with ⟨k', rfl⟩ | ⟨k', j, rfl⟩
      · rw [mem_piece_xl] at ha; simp at ha
      · rw [mem_piece_zl] at ha
        rcases ha with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · simp only [vtx, zl]; rw [vb_odd z p (by omega)]; simp
        · simp only [vtx, zl]
          rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, vb_even z p hlt]
          simp
    · left
      refine hA.trans ?_
      intro v hv
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
      rcases lab_cases a with ⟨k', rfl⟩ | ⟨k', j, rfl⟩
      · rw [mem_piece_xl] at ha; simp at ha
      · rw [mem_piece_zl] at ha
        rcases ha with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · simp only [vtx, zl]; rw [vb_odd z p (by omega)]; simp
        · simp only [vtx, zl]
          rw [vb_ge z p (by omega), show m - 1 = i by omega]
          simp

theorem image_vtx_finPiece_subset {q m : ℕ} (hm : 1 ≤ m) (z p : ℕ → V) {A : Finset V}
    (hA : A ⊆ (finPiece q (2 * m)).image (vtx m z p)) : GoodSlot m z p A (m - 1) := by
  left
  refine hA.trans ?_
  intro v hv
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
  rcases lab_cases a with ⟨k', rfl⟩ | ⟨k', j, rfl⟩
  · exact absurd ha not_mem_finPiece_xl
  · rw [mem_finPiece_zl] at ha
    simp only [vtx, zl]
    rw [vb_ge z p (by omega)]
    simp

/-- **Pieces through a set.**  The number of pieces of the chain refiner whose vertex set contains
`A` is at most `4q + 1` times the number of slots `i` whose pair `{z_i, p_i}` or
`{p_i, z_{i+1}}` contains `A`. -/
theorem chainFam_count_le {q m : ℕ} (hm : 1 ≤ m) {x : ℕ → E} (hx : Set.InjOn x (range m))
    {lkE : E → Finset V} {z p : ℕ → V} (hlk : ∀ i < m, lkE (x i) = {z i}) (A : Finset V) :
    ((chainFam q m x).filter fun W => A ⊆ W.biUnion (cEnds lkE m z p)).card ≤
      (4 * q + 1) * ((range m).filter (GoodSlot m z p A)).card := by
  unfold chainFam
  rw [filter_union]
  have hfin : (({(finPiece q (2 * m)).image (labMap m x)} : Finset (Finset (E ⊕ Lab))).filter
      fun W => A ⊆ W.biUnion (cEnds lkE m z p)).card ≤
      ((range m).filter (GoodSlot m z p A)).card := by
    rw [filter_singleton]
    split_ifs with h
    · rw [card_singleton, one_le_card]
      refine ⟨m - 1, mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩⟩
      rw [biUnion_image_labMap hx hlk] at h
      exact image_vtx_finPiece_subset hm z p h
    · simp
  refine (card_union_le _ _).trans ?_
  rw [add_mul, one_mul]
  refine Nat.add_le_add ?_ hfin
  rw [filter_image]
  refine card_image_le.trans ?_
  refine card_le_mul_card_image_of_maps_to (f := fun i => i.1 / 2) ?_ (4 * q) ?_
  · intro i hi
    simp only [mem_filter, Function.comp] at hi
    rw [biUnion_image_labMap hx hlk] at hi
    refine mem_filter.2 ⟨?_, image_vtx_piece_subset z p hi.1 hi.2⟩
    simp only [cIdx, Idx, mem_filter, mem_product, mem_range] at hi
    exact mem_range.2 (show i.1 / 2 < m by omega)
  · intro j _
    calc _ ≤ (({2 * j, 2 * j + 1} : Finset ℕ) ×ˢ range q ×ˢ (univ : Finset Bool)).card := by
          apply card_le_card
          intro i hi
          simp only [mem_filter, cIdx, Idx, mem_product, mem_range, mem_univ, and_true] at hi
          simp only [mem_product, mem_insert, mem_singleton, mem_range, mem_univ, and_true]
          exact ⟨by omega, hi.1.1.1.2⟩
      _ ≤ 2 * (q * 2) := by
          rw [card_product, card_product, card_univ, Fintype.card_bool, card_range]
          exact Nat.mul_le_mul_right _ (card_insert_le _ _)
      _ = 4 * q := by ring

/-- Blocks at a given vertex. -/
theorem card_blocks_at_le {m : ℕ} (hm : 1 ≤ m) (z p : ℕ → V) (v : V) :
    ((range (2 * m + 2)).filter fun k => vb m z p k = v).card ≤
      ((range m).filter fun i => z i = v).card + 3 * ((range m).filter fun i => p i = v).card := by
  set Zf := (range m).filter fun i => z i = v
  set Pf := (range m).filter fun i => p i = v
  have hsub : ((range (2 * m + 2)).filter fun k => vb m z p k = v) ⊆
      (Zf.image (fun i => 2 * i) ∪ Pf.image (fun i => 2 * i + 1)) ∪
        (if p (m - 1) = v then {2 * m, 2 * m + 1} else ∅) := by
    intro k hk
    rw [mem_filter, mem_range] at hk
    obtain ⟨hk, hv⟩ := hk
    by_cases hkm : k < 2 * m
    · rcases Nat.mod_two_eq_zero_or_one k with he | ho
      · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i := ⟨k / 2, by omega⟩
        rw [vb_even z p (by omega)] at hv
        exact mem_union_left _ (mem_union_left _ (mem_image.2 ⟨i,
          mem_filter.2 ⟨mem_range.2 (by omega), hv⟩, rfl⟩))
      · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
        rw [vb_odd z p (by omega)] at hv
        exact mem_union_left _ (mem_union_right _ (mem_image.2 ⟨i,
          mem_filter.2 ⟨mem_range.2 (by omega), hv⟩, rfl⟩))
    · rw [vb_ge z p (by omega)] at hv
      refine mem_union_right _ ?_
      rw [if_pos hv]
      simp only [mem_insert, mem_singleton]
      omega
  have hP : (if p (m - 1) = v then ({2 * m, 2 * m + 1} : Finset ℕ) else ∅).card ≤ 2 * Pf.card := by
    split_ifs with h
    · have : 1 ≤ Pf.card := one_le_card.2 ⟨m - 1, mem_filter.2 ⟨mem_range.2 (by omega), h⟩⟩
      exact (card_insert_le _ _).trans (by rw [card_singleton]; omega)
    · simp
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (Zf.image (fun i => 2 * i)).card + (Pf.image (fun i => 2 * i + 1)).card +
          (if p (m - 1) = v then ({2 * m, 2 * m + 1} : Finset ℕ) else ∅).card :=
        (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ Zf.card + Pf.card + 2 * Pf.card :=
        Nat.add_le_add (Nat.add_le_add card_image_le card_image_le) hP
    _ = _ := by ring

/-- **Reservoir labels at a vertex.** -/
theorem mdeg_chainRN_singleton {q m : ℕ} (hm : 1 ≤ m) (z p : ℕ → V) (v : V) :
    mdeg (fun y => {vtx m z p y}) (chainRN q m) {v} ≤
      (q - 1) * (((range m).filter fun i => z i = v).card +
        3 * ((range m).filter fun i => p i = v).card) := by
  unfold mdeg
  have hsub : ((chainRN q m).filter fun y => ({v} : Finset V) ⊆ {vtx m z p y}) ⊆
      (((range (2 * m + 2)).filter fun k => vb m z p k = v) ×ˢ range (q - 1)).image
        (fun kj => zl kj.1 kj.2) := by
    intro y hy
    rw [mem_filter, singleton_subset_iff, mem_singleton] at hy
    obtain ⟨hy, hv⟩ := hy
    rcases lab_cases y with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
    · exact absurd hy not_mem_Rlab_xl
    · rw [chainRN, mem_Rlab_zl] at hy
      simp only [vtx, zl] at hv
      refine mem_image.2 ⟨(k, j), ?_, rfl⟩
      simp only [mem_product, mem_filter, mem_range]
      refine ⟨⟨by omega, hv.symm⟩, ?_⟩
      rcases hy with h | ⟨-, h⟩
      · exact h.2
      · have := finT_lt (show 1 ≤ q by
          rcases Nat.eq_zero_or_pos q with hq | hq
          · subst hq; simp at h
          · exact hq) (2 * m)
        have := Nat.mod_lt (q - finT q (2 * m)) (show 0 < q by omega)
        omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = ((range (2 * m + 2)).filter fun k => vb m z p k = v).card * (q - 1) := by
        rw [card_product, card_range]
    _ ≤ _ := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (card_blocks_at_le hm z p v)

/-- Reservoir labels contain no set of two or more vertices. -/
theorem mdeg_chainRN_eq_zero {q m : ℕ} (z p : ℕ → V) {A : Finset V} (hA : 2 ≤ A.card) :
    mdeg (fun y => {vtx m z p y}) (chainRN q m) A = 0 := by
  unfold mdeg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro y _ hy
  have := card_le_card hy
  rw [card_singleton] at this
  omega

theorem card_chainRN_le {q m : ℕ} (hq : 1 ≤ q) : (chainRN q m).card ≤ (2 * m + 2) * (q - 1) :=
  card_Rlab_le hq

end RefinedAbsorption.FlatDown.ChainLink
