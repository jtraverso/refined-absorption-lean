module
public import RefinedAbsorption.OddGrid.Phase

/-!
# Merging an extra column

`Gb` is a grid that extends the full grid `G` (same coordinates) by some vertices in the column
`C = G.C`.  `extra_seg`: the two-stage segment `xSeg G` merges these vertices into column `0`; it is
valid on rook pairs of `Gb`, its output consists of rook pairs of `G`, and its load is at most
`25 (R_b + C_b) + 1`.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset Classical

variable {n : ℕ}

namespace Grid

/-- `Gb` extends `G` by vertices in the column `G.C`. -/
structure ExtraOK (G Gb : Grid n) : Prop where
  co : ∀ v, Gb.co v = G.co v
  sub : ∀ v, G.act v → Gb.act v
  col : ∀ v, Gb.act v → ¬ G.act v → (G.co v).2 = G.C ∧ (G.co v).1 < G.R

variable (G Gb : Grid n)

/-- The extra vertices. -/
def xEm (v : Fin n) : Prop := Gb.act v ∧ ¬ G.act v

/-- The hub of an extra vertex: column `0` of its row. -/
noncomputable def xHub (v : Fin n) : Fin n := G.cellOr ((G.co v).1, 0) v

/-- The column of the twin. -/
def zx (C b' : ℕ) : ℕ := if b' + 1 < C then b' + 1 else b' - 1

/-- The twin. -/
noncomputable def xTw (u w : Fin n) : Fin n := G.cellOr ((G.co u).1, zx G.C (G.co w).2) u

/-- The move target. -/
noncomputable def xMv (u : Fin n) : Finset (Fin n) :=
  {G.xHub u, G.cellOr (orow (G.co u).1, 0) u}

/-- The segment merging the extra column. -/
noncomputable def xSeg : List (Spec n) :=
  [mergeSpec (G.xEm Gb) G.xHub G.xTw, moveSpec (G.xEm Gb) G.xMv]

variable {G Gb}

lemma xHub_spec (hF : G.Full) (hC : 1 ≤ G.C) (hx : ExtraOK G Gb) {v : Fin n} (hv : G.xEm Gb v) :
    G.act (G.xHub v) ∧ G.co (G.xHub v) = ((G.co v).1, 0) :=
  cellOr_spec hF (hx.col v hv.1 hv.2).2 hC v

lemma gb_inj (hx : ExtraOK G Gb) {v w : Fin n} (hv : Gb.act v) (hw : Gb.act w)
    (h : G.co v = G.co w) : v = w :=
  Gb.inj v w hv hw (by rw [hx.co, hx.co, h])

theorem extra_mergeOK (hF : G.Full) (hR : 2 ≤ G.R) (hC : 3 ≤ G.C) (hx : ExtraOK G Gb) :
    MergeOK (Em := G.xEm Gb) (h := G.xHub) (tw := G.xTw) (f := G.xMv) Gb.Rook G.Rook where
  hub u hu := by
    obtain ⟨ha, hco⟩ := xHub_spec hF (by omega) hx hu
    have hcu := hx.col u hu.1 hu.2
    refine ⟨fun h => h.2 ha, fun h => ?_⟩
    have := congrArg (fun x => (G.co x).2) h
    simp only [hco] at this; omega
  ee u w huw hS hu hw := by
    obtain ⟨ha, hco⟩ := xHub_spec hF (by omega) hx hu
    obtain ⟨ha', hco'⟩ := xHub_spec hF (by omega) hx hw
    have hcu := hx.col u hu.1 hu.2
    have hcw := hx.col w hw.1 hw.2
    have hne : G.xHub u ≠ G.xHub w := by
      intro h
      have e := congrArg G.co h
      rw [hco, hco'] at e
      simp only [Prod.mk.injEq] at e
      exact huw (gb_inj hx hu.1 hw.1 (Prod.ext e.1 (by omega)))
    exact ⟨hne, rook_of hne ha ha' (Or.inr (by rw [hco, hco']))⟩
  en u w hS hu hw hwh := by
    have huw : u ≠ w := fun h => hw (h ▸ hu)
    obtain ⟨-, hwa, hr⟩ := rook_pair huw hS
    have hwG : G.act w := by by_contra h; exact hw ⟨hwa, h⟩
    have hcu := hx.col u hu.1 hu.2
    have hb' := G.bdd w hwG
    rw [hx.co, hx.co] at hr
    have hrow : (G.co u).1 = (G.co w).1 := by
      rcases hr with hr | hr
      · exact hr
      · omega
    obtain ⟨ha, hco⟩ := xHub_spec hF (by omega) hx hu
    have hne : (G.co w).2 ≠ 0 := by
      intro h; apply hwh
      exact G.inj w _ hwG ha (by rw [hco, hrow, ← h])
    have z1 : zx G.C (G.co w).2 < G.C := by unfold zx; split_ifs <;> omega
    obtain ⟨ta, tco⟩ := cellOr_spec hF hcu.2 z1 u
    change G.act (G.xTw u w) at ta
    change G.co (G.xTw u w) = _ at tco
    have t1 : G.xTw u w ≠ G.xHub u := by
      intro h; have := congrArg (fun x => (G.co x).2) h; simp only [tco, hco] at this
      unfold zx at this; split_ifs at this
      all_goals omega
    have t2 : G.xTw u w ≠ w := by
      intro h; have := congrArg (fun x => (G.co x).2) h; simp only [tco] at this
      unfold zx at this; split_ifs at this <;> omega
    refine ⟨fun h => h.2 ta, t1, t2, ?_, ?_⟩
    · exact rook_of t1.symm ha ta (Or.inl (by rw [hco, tco]))
    · exact rook_of t2 ta hwG (Or.inl (by rw [tco, hrow]))
  nn u w hS hu hw := by
    have huw : u ≠ w := by rintro rfl; have := rook_card hS; simp at this
    obtain ⟨hua, hwa, hr⟩ := rook_pair huw hS
    have huG : G.act u := by by_contra h; exact hu ⟨hua, h⟩
    have hwG : G.act w := by by_contra h; exact hw ⟨hwa, h⟩
    rw [hx.co, hx.co] at hr
    exact rook_of huw huG hwG hr
  out e he := by
    refine ⟨rook_card he, ?_⟩
    obtain ⟨v, w, -, rfl, hv, hw, -⟩ := he
    intro x hx' hEx
    simp only [mem_insert, mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · exact hEx.2 hv
    · exact hEx.2 hw
  mv u hu := by
    obtain ⟨ha, hco⟩ := xHub_spec hF (by omega) hx hu
    have hcu := hx.col u hu.1 hu.2
    have hor : orow (G.co u).1 < G.R := by unfold orow; split_ifs <;> omega
    obtain ⟨ga, gco⟩ := cellOr_spec hF hor (by omega : 0 < G.C) u
    have hne : G.xHub u ≠ G.cellOr (orow (G.co u).1, 0) u := by
      intro h; have := congrArg (fun x => (G.co x).1) h; simp only [hco, gco] at this
      unfold orow at this; split_ifs at this <;> omega
    exact rook_of hne ha ga (Or.inr (by rw [hco, gco]))

lemma xhub_fiber (hF : G.Full) (hC : 1 ≤ G.C) (hx : ExtraOK G Gb) (v : Fin n) :
    (univ.filter (fun x => G.xEm Gb x ∧ G.xHub x = v)).card ≤ 1 := by
  apply card_le_one.2
  intro x hx' y hy
  simp only [mem_filter, mem_univ, true_and] at hx' hy
  obtain ⟨-, hcx⟩ := xHub_spec hF hC hx hx'.1
  obtain ⟨-, hcy⟩ := xHub_spec hF hC hx hy.1
  have e : G.co (G.xHub x) = G.co (G.xHub y) := by rw [hx'.2, hy.2]
  rw [hcx, hcy] at e
  simp only [Prod.mk.injEq] at e
  have h1 := hx.col x hx'.1.1 hx'.1.2
  have h2 := hx.col y hy.1.1 hy.1.2
  exact gb_inj hx hx'.1.1 hy.1.1 (Prod.ext e.1 (by omega))

/-- The kept ends of pairs whose twin is `v`. -/
noncomputable def xtwSet (G : Grid n) (v : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => G.act w ∧ (G.co w).1 = (G.co v).1 ∧
    (G.co w).2 ∈ ({(G.co v).2 + 1, (G.co v).2 - 1} : Finset ℕ))

lemma xtwSet_card (v : Fin n) : (G.xtwSet v).card ≤ 2 := by
  calc _ ≤ ({(G.co v).2 + 1, (G.co v).2 - 1} : Finset ℕ).card := by
        apply card_le_card_of_injOn (fun w => (G.co w).2)
        · intro w hw
          simp only [xtwSet, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
          exact hw.2.2
        · intro w hw w' hw' h
          simp only [xtwSet, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
          exact G.inj w w' hw.1 hw'.1 (Prod.ext (hw.2.1.trans hw'.2.1.symm) h)
    _ ≤ 2 := card_le_two

lemma xtwSet_spec (hF : G.Full) (hC : 3 ≤ G.C) (hx : ExtraOK G Gb) (v : Fin n) :
    ∀ a b, Gb.Rook {a, b} → G.xEm Gb a → ¬ G.xEm Gb b → b ≠ G.xHub a → G.xTw a b = v →
      b ∈ G.xtwSet v := by
  intro u w hS hu hw hwh htv
  have huw : u ≠ w := fun h => hw (h ▸ hu)
  obtain ⟨-, hwa, hr⟩ := rook_pair huw hS
  have hwG : G.act w := by by_contra h; exact hw ⟨hwa, h⟩
  have hcu := hx.col u hu.1 hu.2
  have hb' := G.bdd w hwG
  rw [hx.co, hx.co] at hr
  have hrow : (G.co u).1 = (G.co w).1 := by
    rcases hr with hr | hr
    · exact hr
    · omega
  have z1 : zx G.C (G.co w).2 < G.C := by unfold zx; split_ifs <;> omega
  obtain ⟨-, tco⟩ := cellOr_spec hF hcu.2 z1 u
  change G.co (G.xTw u w) = _ at tco
  rw [htv] at tco
  simp only [xtwSet, mem_filter, mem_univ, true_and, tco, mem_insert, mem_singleton]
  refine ⟨hwG, hrow.symm, ?_⟩
  unfold zx; split_ifs <;> omega

lemma xmv_fiber (hF : G.Full) (hC : 1 ≤ G.C) (hx : ExtraOK G Gb) (v : Fin n) :
    (univ.filter (fun u => G.xEm Gb u ∧ v ∈ G.xMv u)).card ≤ 1 + Gb.R := by
  have hsub : univ.filter (fun u => G.xEm Gb u ∧ v ∈ G.xMv u) ⊆
      univ.filter (fun x => G.xEm Gb x ∧ G.xHub x = v) ∪
        univ.filter (fun u => G.xEm Gb u) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and, xMv, mem_insert, mem_singleton] at hu
    obtain ⟨hE, hv | hv⟩ := hu
    · exact mem_union_left _ (by simp [hE, hv])
    · exact mem_union_right _ (by simp [hE])
  have hcol : (univ.filter (fun u => G.xEm Gb u)).card ≤ Gb.R := by
    calc _ ≤ (range Gb.R).card := by
          apply card_le_card_of_injOn (fun w => (G.co w).1)
          · intro w hw
            simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
            have := (Gb.bdd w hw.1).1
            rw [hx.co] at this
            simpa using this
          · intro w hw w' hw' h
            simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
            have h1 := hx.col w hw.1 hw.2
            have h2 := hx.col w' hw'.1 hw'.2
            exact gb_inj hx hw.1 hw'.1 (Prod.ext h (h1.1.trans h2.1.symm))
      _ = Gb.R := card_range _
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 1 + Gb.R := add_le_add (xhub_fiber hF hC hx v) hcol

/-- **The segment merging the extra column.** -/
theorem extra_seg (hF : G.Full) (hR : 2 ≤ G.R) (hC : 3 ≤ G.C) (hx : ExtraOK G Gb)
    {P : Finset (Finset (Fin n))} (hP : ∀ e ∈ P, Gb.Rook e) :
    SegOK (G.xSeg Gb) P ∧ (∀ e ∈ prun (G.xSeg Gb) P (G.xSeg Gb).length, G.Rook e) ∧
      ∀ v, passSum (G.xSeg Gb) P v ≤ 25 * (Gb.R + Gb.C) + 1 := by
  have hm := extra_mergeOK hF hR hC hx
  have hP' : ∀ e ∈ P, e.card = 2 ∧ Gb.Rook e := fun e he => ⟨rook_card (hP e he), hP e he⟩
  obtain ⟨hseg, hout⟩ := merge_seg hm hP'
  refine ⟨hseg, hout, fun v => ?_⟩
  have h0 := merge_load0 (f := G.xMv) hP' (Gb.deg_le hP) v (xhub_fiber hF (by omega) hx v)
    (xtwSet_spec hF hC hx v)
  have h1 := merge_load1 hm hP' v
  have h4 := xtwSet_card (G := G) v
  have h5 := xmv_fiber hF (by omega) hx v
  unfold passSum
  simp only [xSeg, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, sum_range_succ,
    sum_range_zero]
  have : (1 + 1 + (G.xtwSet v).card) * (Gb.R + Gb.C) ≤ 6 * (Gb.R + Gb.C) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

end Grid

end RefinedAbsorption.OddGrid
