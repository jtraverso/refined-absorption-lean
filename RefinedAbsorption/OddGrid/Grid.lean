module
public import RefinedAbsorption.OddGrid.Merge

/-!
# Grids of vertices and rook pairs

A `Grid n` places some vertices of `Fin n` (the *active* ones) injectively on the cells of an
`R × C` board.  A *rook pair* is a pair of distinct active vertices in the same row or in the
same column.

* `Grid.deg_le`: in a set of rook pairs every vertex lies in at most `R + C` pairs.
* `Grid.card_le`: a set of rook pairs has at most `(R C)²` elements.
* `Grid.swap`: exchanging rows and columns does not change the rook pairs.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset Classical

variable {n : ℕ}

/-- Active vertices placed injectively on an `R × C` board. -/
structure Grid (n : ℕ) where
  act : Fin n → Prop
  co : Fin n → ℕ × ℕ
  R : ℕ
  C : ℕ
  inj : ∀ v w, act v → act w → co v = co w → v = w
  bdd : ∀ v, act v → (co v).1 < R ∧ (co v).2 < C

namespace Grid

variable (G : Grid n)

/-- Rook pairs of a grid. -/
def Rook (e : Finset (Fin n)) : Prop :=
  ∃ v w, v ≠ w ∧ e = {v, w} ∧ G.act v ∧ G.act w ∧
    ((G.co v).1 = (G.co w).1 ∨ (G.co v).2 = (G.co w).2)

/-- Every cell of the board carries an active vertex. -/
def Full : Prop := ∀ a < G.R, ∀ b < G.C, ∃ v, G.act v ∧ G.co v = (a, b)

/-- The vertex on the cell `p`, or `d` if there is none. -/
noncomputable def cellOr (p : ℕ × ℕ) (d : Fin n) : Fin n :=
  if hx : ∃ v, G.act v ∧ G.co v = p then hx.choose else d

lemma cellOr_spec {G : Grid n} (hF : G.Full) {a b : ℕ} (ha : a < G.R) (hb : b < G.C)
    (d : Fin n) : G.act (G.cellOr (a, b) d) ∧ G.co (G.cellOr (a, b) d) = (a, b) := by
  have hx := hF a ha b hb
  unfold cellOr
  rw [dif_pos hx]
  exact hx.choose_spec

lemma rook_card {G : Grid n} {e : Finset (Fin n)} (he : G.Rook e) : e.card = 2 := by
  obtain ⟨v, w, hvw, rfl, -⟩ := he
  exact card_pair hvw

lemma card_row_le (x : Fin n) :
    (univ.filter (fun w => G.act w ∧ (G.co w).1 = (G.co x).1)).card ≤ G.C := by
  calc _ ≤ (range G.C).card := by
        apply card_le_card_of_injOn (fun w => (G.co w).2)
        · intro w hw
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
          simpa using (G.bdd w hw.1).2
        · intro w hw w' hw' hww'
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
          exact G.inj w w' hw.1 hw'.1 (Prod.ext (hw.2.trans hw'.2.symm) hww')
    _ = G.C := card_range _

lemma card_col_le (x : Fin n) :
    (univ.filter (fun w => G.act w ∧ (G.co w).2 = (G.co x).2)).card ≤ G.R := by
  calc _ ≤ (range G.R).card := by
        apply card_le_card_of_injOn (fun w => (G.co w).1)
        · intro w hw
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
          simpa using (G.bdd w hw.1).1
        · intro w hw w' hw' hww'
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
          exact G.inj w w' hw.1 hw'.1 (Prod.ext hww' (hw.2.trans hw'.2.symm))
    _ = G.R := card_range _

/-- **Degrees in rook pairs.** -/
lemma deg_le {P : Finset (Finset (Fin n))} (hP : ∀ e ∈ P, G.Rook e) (x : Fin n) :
    (P.filter (x ∈ ·)).card ≤ G.R + G.C := by
  set Wr := univ.filter (fun w => G.act w ∧ (G.co w).1 = (G.co x).1)
  set Wc := univ.filter (fun w => G.act w ∧ (G.co w).2 = (G.co x).2)
  have hsub : P.filter (x ∈ ·) ⊆ (Wr ∪ Wc).image (fun w => {x, w}) := by
    intro e he
    obtain ⟨he, hx⟩ := mem_filter.1 he
    obtain ⟨v, w, hvw, rfl, hv, hw, hrc⟩ := hP _ he
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · refine mem_image.2 ⟨w, ?_, rfl⟩
      rcases hrc with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hw, h.symm⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hw, h.symm⟩)
    · refine mem_image.2 ⟨v, ?_, pair_comm x v⟩
      rcases hrc with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hv, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hv, h⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (Wr ∪ Wc).card := card_image_le
    _ ≤ Wr.card + Wc.card := card_union_le _ _
    _ ≤ G.C + G.R := add_le_add (G.card_row_le x) (G.card_col_le x)
    _ = G.R + G.C := add_comm _ _

lemma card_act_le : (univ.filter G.act).card ≤ G.R * G.C := by
  calc _ ≤ (range G.R ×ˢ range G.C).card := by
        apply card_le_card_of_injOn G.co
        · intro w hw
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
          simpa using G.bdd w hw
        · intro w hw w' hw' h
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
          exact G.inj w w' hw hw' h
    _ = G.R * G.C := by simp

/-- **Number of rook pairs.** -/
lemma card_le {P : Finset (Finset (Fin n))} (hP : ∀ e ∈ P, G.Rook e) :
    P.card ≤ (G.R * G.C) ^ 2 := by
  set A := univ.filter G.act
  have hsub : P ⊆ (A ×ˢ A).image (fun p => {p.1, p.2}) := by
    intro e he
    obtain ⟨v, w, -, rfl, hv, hw, -⟩ := hP e he
    exact mem_image.2 ⟨(v, w), mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, hv⟩,
      mem_filter.2 ⟨mem_univ _, hw⟩⟩, rfl⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (A ×ˢ A).card := card_image_le
    _ = A.card * A.card := card_product _ _
    _ ≤ (G.R * G.C) * (G.R * G.C) := Nat.mul_le_mul G.card_act_le G.card_act_le
    _ = (G.R * G.C) ^ 2 := (sq _).symm

/-- Rows and columns exchanged. -/
def swap : Grid n where
  act := G.act
  co := fun v => (G.co v).swap
  R := G.C
  C := G.R
  inj := fun v w hv hw h => G.inj v w hv hw (Prod.swap_injective h)
  bdd := fun v hv => ⟨(G.bdd v hv).2, (G.bdd v hv).1⟩

lemma rook_swap {e : Finset (Fin n)} : G.swap.Rook e ↔ G.Rook e := by
  unfold Rook
  simp only [swap, Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨v, w, h1, h2, h3, h4, h5⟩; exact ⟨v, w, h1, h2, h3, h4, h5.symm⟩
  · rintro ⟨v, w, h1, h2, h3, h4, h5⟩; exact ⟨v, w, h1, h2, h3, h4, h5.symm⟩

lemma full_swap (hF : G.Full) : G.swap.Full := by
  intro a ha b hb
  obtain ⟨v, hv, hco⟩ := hF b hb a ha
  exact ⟨v, hv, by simp [swap, hco]⟩

end Grid

end RefinedAbsorption.OddGrid
