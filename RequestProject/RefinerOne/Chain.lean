module
public import RequestProject.MathlibImports

/-!
# A chain refiner for `r = 1` (label level)

For `r = 1`, edges are single vertices and `K_q^1`-divisibility means that the number of
vertices is a multiple of `q`.  We build, on the abstract label set `ℕ ⊕ (ℕ × ℕ)`, a family of
`q`-sets ("pieces") of bounded multiplicity such that for every subset `L` of the
`m` "input" labels `xl 0, …, xl (m-1)` with `q ∣ |L|`, the reservoir `Rlab` together with `L`
is partitioned by pieces.

The construction is a finite automaton: block `i` consists of the `q - 1` labels `zl i j`; the
state `tSeq i ∈ {0, …, q-1}` records how many labels of block `i` are carried into step `i`,
where they are grouped with `xl i` (if it is used) and the tail of block `i + 1`.
-/

@[expose] public section

namespace RefinedAbsorption.ChainRefiner

open Finset

/-- Labels: `inl i` is the `i`-th input vertex, `inr (i, j)` is the `j`-th vertex of block `i`. -/
abbrev Lab := ℕ ⊕ (ℕ × ℕ)

/-- The `i`-th input label. -/
def xl (i : ℕ) : Lab := Sum.inl i

/-- The `j`-th label of block `i`. -/
def zl (i j : ℕ) : Lab := Sum.inr (i, j)

/-- The bit `e` as a natural number. -/
def bit (e : Bool) : ℕ := if e then 1 else 0

/-- The next carry state. -/
def nextT (q t : ℕ) (e : Bool) : ℕ := (t + bit e + (q - 1)) % q

/-- The piece used at step `i` with incoming carry `t` and input bit `e`: the first `t` labels
of block `i`, the input `xl i` if `e`, and the labels `nextT q t e, …, q-2` of block `i+1`. -/
def piece (q i t : ℕ) (e : Bool) : Finset Lab :=
  (range t).image (zl i) ∪ ((if e then {xl i} else ∅) ∪
    (Ico (nextT q t e) (q - 1)).image (zl (i + 1)))

/-- The final carry state (independent of the input set, when its size is divisible). -/
def finT (q m : ℕ) : ℕ := (q - 1 + (q - 1) * m) % q

/-- The final piece: the carried labels of block `m` together with padding from block `m+1`. -/
def finPiece (q m : ℕ) : Finset Lab :=
  (range (finT q m)).image (zl m) ∪ (range ((q - finT q m) % q)).image (zl (m + 1))

/-- The reservoir: blocks `0, …, m` and the padding of block `m+1`. -/
def Rlab (q m : ℕ) : Finset Lab :=
  (range (m + 1) ×ˢ range (q - 1)).image (fun p => zl p.1 p.2) ∪
    (range ((q - finT q m) % q)).image (zl (m + 1))

/-- The input labels. -/
def Xlab (m : ℕ) : Finset Lab := (range m).image xl

/-- The input labels selected by `b`. -/
def Llab (b : ℕ → Bool) (m : ℕ) : Finset Lab := ((range m).filter (fun i => b i)).image xl

/-- All labels used. -/
def Ulab (q m : ℕ) : Finset Lab :=
  Xlab m ∪ (range (m + 2) ×ˢ range (q - 1)).image (fun p => zl p.1 p.2)

/-- The index set of all pieces. -/
def Idx (q m : ℕ) : Finset (ℕ × ℕ × Bool) := range m ×ˢ range q ×ˢ univ

/-- The carry states along the input `b`. -/
def tSeq (q : ℕ) (b : ℕ → Bool) : ℕ → ℕ
  | 0 => q - 1
  | i + 1 => nextT q (tSeq q b i) (b i)

/-- Number of selected inputs among the first `i`. -/
def cnt (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => cnt b i + bit (b i)

/-- The piece chosen at step `i` for the input `b`. -/
def chosen (q : ℕ) (b : ℕ → Bool) (i : ℕ) : Finset Lab := piece q i (tSeq q b i) (b i)

lemma bit_le (e : Bool) : bit e ≤ 1 := by cases e <;> simp [bit]

lemma xl_ne_zl (i k j : ℕ) : xl i ≠ zl k j := by simp [xl, zl]

lemma zl_inj {i j k l : ℕ} : zl i j = zl k l ↔ i = k ∧ j = l := by simp [zl]

lemma xl_inj {i k : ℕ} : xl i = xl k ↔ i = k := by simp [xl]

lemma nextT_lt {q : ℕ} (hq : 1 ≤ q) (t : ℕ) (e : Bool) : nextT q t e < q :=
  Nat.mod_lt _ (by omega)

lemma finT_lt {q : ℕ} (hq : 1 ≤ q) (m : ℕ) : finT q m < q := Nat.mod_lt _ (by omega)

lemma tSeq_lt {q : ℕ} (hq : 1 ≤ q) (b : ℕ → Bool) (i : ℕ) : tSeq q b i < q := by
  cases i with
  | zero => simp [tSeq]; omega
  | succ i => exact nextT_lt hq _ _

lemma tSeq_eq {q : ℕ} (hq : 1 ≤ q) (b : ℕ → Bool) (i : ℕ) :
    tSeq q b i = (q - 1 + cnt b i + (q - 1) * i) % q := by
  induction i with
  | zero => simp [tSeq, cnt, Nat.mod_eq_of_lt (show q - 1 < q by omega)]
  | succ i ih =>
    simp only [tSeq, nextT, ih, cnt]
    rw [add_assoc, Nat.mod_add_mod]
    congr 1
    rw [Nat.mul_succ]
    ring

lemma tSeq_final {q : ℕ} (hq : 1 ≤ q) (b : ℕ → Bool) (m : ℕ) (hdiv : q ∣ cnt b m) :
    tSeq q b m = finT q m := by
  rw [tSeq_eq hq, finT]
  obtain ⟨k, hk⟩ := hdiv
  rw [hk, show q - 1 + q * k + (q - 1) * m = q - 1 + (q - 1) * m + q * k by ring,
    Nat.add_mul_mod_self_left]

/-! ### Membership -/

lemma mem_piece_xl {q i t k : ℕ} {e : Bool} : xl k ∈ piece q i t e ↔ e = true ∧ k = i := by
  cases e <;> simp [piece, xl, zl, eq_comm]

lemma mem_piece_zl {q i t k j : ℕ} {e : Bool} :
    zl k j ∈ piece q i t e ↔
      (k = i ∧ j < t) ∨ (k = i + 1 ∧ nextT q t e ≤ j ∧ j < q - 1) := by
  cases e <;> simp [piece, xl, zl] <;> omega

lemma not_mem_finPiece_xl {q m k : ℕ} : xl k ∉ finPiece q m := by
  simp [finPiece, xl, zl]

lemma mem_finPiece_zl {q m k j : ℕ} :
    zl k j ∈ finPiece q m ↔
      (k = m ∧ j < finT q m) ∨ (k = m + 1 ∧ j < (q - finT q m) % q) := by
  simp [finPiece, zl]; omega

lemma mem_Rlab_zl {q m k j : ℕ} :
    zl k j ∈ Rlab q m ↔ (k ≤ m ∧ j < q - 1) ∨ (k = m + 1 ∧ j < (q - finT q m) % q) := by
  simp [Rlab, zl]; omega

lemma not_mem_Rlab_xl {q m k : ℕ} : xl k ∉ Rlab q m := by simp [Rlab, xl, zl]

lemma mem_Llab_xl {b : ℕ → Bool} {m k : ℕ} : xl k ∈ Llab b m ↔ k < m ∧ b k = true := by
  simp [Llab, xl]

lemma not_mem_Llab_zl {b : ℕ → Bool} {m k j : ℕ} : zl k j ∉ Llab b m := by
  simp [Llab, xl, zl]

lemma mem_Xlab_xl {m k : ℕ} : xl k ∈ Xlab m ↔ k < m := by simp [Xlab, xl]

lemma not_mem_Xlab_zl {m k j : ℕ} : zl k j ∉ Xlab m := by simp [Xlab, xl, zl]

lemma mem_Ulab_zl {q m k j : ℕ} : zl k j ∈ Ulab q m ↔ k < m + 2 ∧ j < q - 1 := by
  simp [Ulab, Xlab, xl, zl]

lemma mem_Ulab_xl {q m k : ℕ} : xl k ∈ Ulab q m ↔ k < m := by
  simp [Ulab, Xlab, xl, zl]

/-- Every label is an input label or a block label. -/
lemma lab_cases (a : Lab) : (∃ k, a = xl k) ∨ (∃ k j, a = zl k j) := by
  rcases a with k | ⟨k, j⟩
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr ⟨k, j, rfl⟩

/-! ### Containment -/

lemma piece_subset {q m i t : ℕ} {e : Bool} (hq : 1 ≤ q) (hi : i < m) (ht : t < q) :
    piece q i t e ⊆ Rlab q m ∪ Xlab m := by
  intro a ha
  rw [mem_union]
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · rw [mem_piece_xl] at ha
    exact Or.inr (mem_Xlab_xl.2 (by omega))
  · rw [mem_piece_zl] at ha
    left; rw [mem_Rlab_zl]; omega

lemma finPiece_subset {q m : ℕ} (hq : 1 ≤ q) : finPiece q m ⊆ Rlab q m ∪ Xlab m := by
  intro a ha
  rw [mem_union]
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · exact absurd ha not_mem_finPiece_xl
  · rw [mem_finPiece_zl] at ha
    have := finT_lt hq m
    left; rw [mem_Rlab_zl]; omega

lemma Rlab_subset_Ulab {q m : ℕ} (hq : 1 ≤ q) : Rlab q m ⊆ Ulab q m := by
  intro a ha
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · exact absurd ha not_mem_Rlab_xl
  · rw [mem_Rlab_zl] at ha
    rw [mem_Ulab_zl]
    rcases ha with h | h
    · omega
    · refine ⟨by omega, ?_⟩
      have := finT_lt hq m
      by_cases h0 : finT q m = 0
      · rw [h0, Nat.sub_zero, Nat.mod_self] at h; omega
      · have : (q - finT q m) % q ≤ q - finT q m := Nat.mod_le _ _
        omega

lemma Xlab_subset_Ulab {q m : ℕ} : Xlab m ⊆ Ulab q m := subset_union_left

lemma Rlab_union_Xlab_subset {q m : ℕ} (hq : 1 ≤ q) : Rlab q m ∪ Xlab m ⊆ Ulab q m :=
  union_subset (Rlab_subset_Ulab hq) Xlab_subset_Ulab

/-! ### Sizes -/

lemma card_piece {q i t : ℕ} {e : Bool} (hq : 1 ≤ q) (ht : t < q) :
    (piece q i t e).card = if t = 0 ∧ e = false then 0 else q := by
  have hd1 : Disjoint ((range t).image (zl i))
      ((if e then {xl i} else ∅) ∪ (Ico (nextT q t e) (q - 1)).image (zl (i + 1))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_image, mem_range] at ha
    obtain ⟨j, -, rfl⟩ := ha
    cases e <;> simp [zl, xl] at hb
  have hd2 : Disjoint (if e then {xl i} else ∅)
      ((Ico (nextT q t e) (q - 1)).image (zl (i + 1))) := by
    cases e <;> simp [zl, xl]
  have hz : ∀ k, Function.Injective (zl k) := fun k a b h => (zl_inj.1 h).2
  rw [piece, card_union_of_disjoint hd1, card_union_of_disjoint hd2,
    card_image_of_injective _ (hz i), card_image_of_injective _ (hz (i + 1)), card_range,
    Nat.card_Ico]
  have hite : (if e then ({xl i} : Finset Lab) else ∅).card = bit e := by
    cases e <;> simp [bit]
  rw [hite]
  unfold nextT
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hb := bit_le e
  by_cases h0 : t = 0 ∧ e = false
  · obtain ⟨rfl, rfl⟩ := h0
    simp [bit, Nat.mod_eq_of_lt (show p < p + 1 by omega)]
  · rw [if_neg h0]
    have hpos : 1 ≤ t + bit e := by
      by_contra hc
      apply h0
      refine ⟨by omega, ?_⟩
      cases e <;> simp_all [bit]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma card_finPiece {q m : ℕ} (hq : 1 ≤ q) :
    (finPiece q m).card = if finT q m = 0 then 0 else q := by
  have hd : Disjoint ((range (finT q m)).image (zl m))
      ((range ((q - finT q m) % q)).image (zl (m + 1))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_image, mem_range] at ha hb
    obtain ⟨j, -, rfl⟩ := ha
    obtain ⟨j', -, h⟩ := hb
    simp [zl] at h
  have hz : ∀ k, Function.Injective (zl k) := fun k a b h => (zl_inj.1 h).2
  rw [finPiece, card_union_of_disjoint hd, card_image_of_injective _ (hz m),
    card_image_of_injective _ (hz (m + 1)), card_range, card_range]
  have := finT_lt hq m
  split_ifs with h0
  · rw [h0]; simp
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

lemma card_Rlab_le {q m : ℕ} (hq : 1 ≤ q) : (Rlab q m).card ≤ (m + 2) * (q - 1) := by
  calc (Rlab q m).card ≤ ((range (m + 2) ×ˢ range (q - 1)).image
        (fun p => zl p.1 p.2)).card := by
        apply card_le_card
        intro a ha
        have h := Rlab_subset_Ulab hq ha
        rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
        · exact absurd ha not_mem_Rlab_xl
        · rw [mem_Ulab_zl] at h
          simp only [mem_image, mem_product, mem_range]
          exact ⟨(k, j), ⟨h.1, h.2⟩, rfl⟩
    _ ≤ (range (m + 2) ×ˢ range (q - 1)).card := card_image_le
    _ = (m + 2) * (q - 1) := by simp

/-! ### The partition -/

lemma chosen_xl {q : ℕ} {b : ℕ → Bool} {i k : ℕ} :
    xl k ∈ chosen q b i ↔ b i = true ∧ k = i := mem_piece_xl

lemma chosen_zl {q : ℕ} {b : ℕ → Bool} {i k j : ℕ} :
    zl k j ∈ chosen q b i ↔
      (k = i ∧ j < tSeq q b i) ∨ (k = i + 1 ∧ tSeq q b (i + 1) ≤ j ∧ j < q - 1) :=
  mem_piece_zl

/-- **Covering.**  If `q ∣ |L|`, the chosen pieces and the final piece cover exactly
`Rlab ∪ L`. -/
theorem cover {q : ℕ} (hq : 1 ≤ q) (b : ℕ → Bool) (m : ℕ) (hdiv : q ∣ cnt b m) (a : Lab) :
    ((∃ i < m, a ∈ chosen q b i) ∨ a ∈ finPiece q m) ↔ a ∈ Rlab q m ∪ Llab b m := by
  have hfin := tSeq_final hq b m hdiv
  have hT := tSeq_lt hq b
  have hfl := finT_lt hq m
  rw [mem_union]
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · simp only [chosen_xl, mem_Llab_xl]
    simp only [not_mem_finPiece_xl, not_mem_Rlab_xl, or_false, false_or]
    constructor
    · rintro ⟨i, hi, hb, rfl⟩; exact ⟨hi, hb⟩
    · rintro ⟨hk, hb⟩; exact ⟨k, hk, hb, rfl⟩
  · simp only [chosen_zl, mem_finPiece_zl, mem_Rlab_zl]
    simp only [not_mem_Llab_zl, or_false]
    constructor
    · rintro (⟨i, hi, h | h⟩ | h)
      · have := hT i; left; omega
      · left; omega
      · rcases h with h | h
        · left; omega
        · right; exact h
    · rintro (⟨hk, hj⟩ | h)
      · by_cases hjt : j < tSeq q b k
        · by_cases hkm : k < m
          · exact Or.inl ⟨k, hkm, Or.inl ⟨rfl, hjt⟩⟩
          · have : k = m := by omega
            subst this
            exact Or.inr (Or.inl ⟨rfl, hfin ▸ hjt⟩)
        · cases k with
          | zero => simp [tSeq] at hjt; omega
          | succ k => exact Or.inl ⟨k, by omega, Or.inr ⟨rfl, by omega, hj⟩⟩
      · exact Or.inr (Or.inr h)

/-- **Uniqueness** among the chosen pieces. -/
theorem chosen_unique {q : ℕ} {b : ℕ → Bool} {i i' : ℕ} {a : Lab}
    (h : a ∈ chosen q b i) (h' : a ∈ chosen q b i') : i = i' := by
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · rw [chosen_xl] at h h'
    omega
  · rw [chosen_zl] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · omega
    · obtain ⟨rfl, hj⟩ := h
      obtain ⟨hk, hj', -⟩ := h'
      subst hk; omega
    · obtain ⟨rfl, hj⟩ := h'
      obtain ⟨hk, hj', -⟩ := h
      subst hk; omega
    · omega

/-- **Uniqueness** between the chosen pieces and the final piece. -/
theorem chosen_not_fin {q : ℕ} (hq : 1 ≤ q) {b : ℕ → Bool} {m i : ℕ} (hdiv : q ∣ cnt b m)
    (hi : i < m) {a : Lab} (h : a ∈ chosen q b i) : a ∉ finPiece q m := by
  have hfin := tSeq_final hq b m hdiv
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · exact not_mem_finPiece_xl
  · rw [chosen_zl] at h
    rw [mem_finPiece_zl]
    rintro (⟨rfl, hj⟩ | ⟨rfl, -⟩)
    · rcases h with h | ⟨hk, hj', -⟩
      · omega
      · rw [← hk, hfin] at hj'; omega
    · omega

lemma chosen_eq_piece (q : ℕ) (b : ℕ → Bool) (i : ℕ) :
    chosen q b i = piece q i (tSeq q b i) (b i) := rfl

/-! ### Multiplicity -/

/-- Every label lies in at most `4q` pieces. -/
theorem card_filter_piece_le (q m : ℕ) (a : Lab) :
    ((Idx q m).filter (fun x => a ∈ piece q x.1 x.2.1 x.2.2)).card ≤ 4 * q := by
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · calc _ ≤ ({k} ×ˢ range q ×ˢ (univ : Finset Bool)).card := by
          apply card_le_card
          intro x hx
          simp only [Idx, mem_filter, mem_product, mem_range, mem_piece_xl] at hx
          simp only [mem_product, mem_singleton, mem_range, mem_univ, and_true]
          exact ⟨hx.2.2.symm, hx.1.2.1⟩
      _ ≤ 4 * q := by simp; omega
  · calc _ ≤ (({k} ∪ {k - 1}) ×ˢ range q ×ˢ (univ : Finset Bool)).card := by
          apply card_le_card
          intro x hx
          simp only [Idx, mem_filter, mem_product, mem_range, mem_piece_zl] at hx
          simp only [mem_product, mem_union, mem_singleton, mem_range, mem_univ, and_true]
          exact ⟨by omega, hx.1.2.1⟩
      _ ≤ (({k} ∪ {k - 1} : Finset ℕ)).card * (q * 2) := by simp
      _ ≤ 2 * (q * 2) := by
          gcongr
          exact (card_union_le _ _).trans (by simp)
      _ = 4 * q := by ring

lemma cnt_eq_card (b : ℕ → Bool) (m : ℕ) : cnt b m = (Llab b m).card := by
  rw [Llab, card_image_of_injective _ (fun a b h => xl_inj.1 h)]
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    rw [cnt, ih, range_add_one, filter_insert]
    cases hb : b m
    · simp [bit]
    · rw [if_pos rfl, card_insert_of_notMem (by simp)]
      simp [bit]

end RefinedAbsorption.ChainRefiner
