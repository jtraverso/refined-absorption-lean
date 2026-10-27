module
public import RequestProject.OddGrid.Grid

/-!
# Halving the columns of a full grid

For a full grid with `R ≥ 2` rows and `C ≥ 5` columns, the vertices of the odd columns are merged
into the even columns on their left (`b ↦ b - 1`).  `halve_seg`: the two-stage segment `hSeg G` is
valid on any set of rook pairs of `G`, its output consists of rook pairs of the halved grid
`G.colHalve` (with `⌈C / 2⌉` columns), and its load at every vertex is at most `25 (R + C) + 1`.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset Classical

variable {n : ℕ}

namespace Grid

variable (G : Grid n)

lemma rook_pair {G : Grid n} {u w : Fin n} (huw : u ≠ w) (h : G.Rook {u, w}) :
    G.act u ∧ G.act w ∧ ((G.co u).1 = (G.co w).1 ∨ (G.co u).2 = (G.co w).2) := by
  obtain ⟨v, v', -, he, hv, hv', hr⟩ := h
  have hu : u ∈ ({v, v'} : Finset (Fin n)) := he ▸ (by simp)
  have hw : w ∈ ({v, v'} : Finset (Fin n)) := he ▸ (by simp)
  simp only [mem_insert, mem_singleton] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd rfl huw
  · exact ⟨hv, hv', hr⟩
  · exact ⟨hv', hv, hr.imp Eq.symm Eq.symm⟩
  · exact absurd rfl huw

lemma rook_of {G : Grid n} {u w : Fin n} (huw : u ≠ w) (hu : G.act u) (hw : G.act w)
    (hr : (G.co u).1 = (G.co w).1 ∨ (G.co u).2 = (G.co w).2) : G.Rook {u, w} :=
  ⟨u, w, huw, rfl, hu, hw, hr⟩

/-- The grid of the even columns, renumbered. -/
def colHalve : Grid n where
  act v := G.act v ∧ (G.co v).2 % 2 = 0
  co v := ((G.co v).1, (G.co v).2 / 2)
  R := G.R
  C := (G.C + 1) / 2
  inj v w hv hw h := by
    apply G.inj v w hv.1 hw.1
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    exact Prod.ext h1 (by omega)
  bdd v hv := ⟨(G.bdd v hv.1).1, by have := (G.bdd v hv.1).2; omega⟩

lemma full_colHalve {G : Grid n} (hF : G.Full) : G.colHalve.Full := by
  intro a ha b hb
  simp only [colHalve] at ha hb
  obtain ⟨v, hv, hco⟩ := hF a ha (2 * b) (by omega)
  refine ⟨v, ⟨hv, by rw [hco]; simp⟩, ?_⟩
  simp only [colHalve, hco]
  ext <;> simp

/-- The emptied vertices: odd columns. -/
def hEm (v : Fin n) : Prop := G.act v ∧ (G.co v).2 % 2 = 1

/-- The hub: the cell on the left. -/
noncomputable def hHub (v : Fin n) : Fin n := G.cellOr ((G.co v).1, (G.co v).2 - 1) v

/-- The column of the twin. -/
def zcol (C b b' : ℕ) : ℕ :=
  if b' + 2 < C ∧ b' + 2 ≠ b - 1 then b' + 2
  else if 2 ≤ b' ∧ b' - 2 ≠ b - 1 then b' - 2
  else if b' + 4 < C then b' + 4 else b' - 4

/-- The twin of a pair `{u, w}` in a row. -/
noncomputable def hTw (u w : Fin n) : Fin n :=
  G.cellOr ((G.co u).1, zcol G.C (G.co u).2 (G.co w).2) u

/-- The other row used by moves. -/
def orow (a : ℕ) : ℕ := if a = 0 then 1 else 0

/-- The move target: a column pair at the hub. -/
noncomputable def hMv (u : Fin n) : Finset (Fin n) :=
  {G.hHub u, G.cellOr (orow (G.co u).1, (G.co u).2 - 1) u}

/-- The halving segment. -/
noncomputable def hSeg : List (Spec n) :=
  [mergeSpec G.hEm G.hHub G.hTw, moveSpec G.hEm G.hMv]

lemma zcol_spec {C b b' : ℕ} (hC : 5 ≤ C) (hb : b % 2 = 1) (hb' : b' % 2 = 0) (hbC : b < C)
    (hb'C : b' < C) :
    zcol C b b' % 2 = 0 ∧ zcol C b b' < C ∧ zcol C b b' ≠ b - 1 ∧ zcol C b b' ≠ b' ∧
      (b' = zcol C b b' + 2 ∨ b' = zcol C b b' - 2 ∨ b' = zcol C b b' + 4 ∨
        b' = zcol C b b' - 4) := by
  unfold zcol
  split_ifs <;> omega

variable {G}

lemma hHub_spec (hF : G.Full) {v : Fin n} (hv : G.hEm v) :
    G.act (G.hHub v) ∧ G.co (G.hHub v) = ((G.co v).1, (G.co v).2 - 1) := by
  have hb := G.bdd v hv.1
  exact cellOr_spec hF hb.1 (by omega) v

lemma hHub_ne (hF : G.Full) {v : Fin n} (hv : G.hEm v) : ¬ G.hEm (G.hHub v) ∧ G.hHub v ≠ v := by
  obtain ⟨-, hco⟩ := hHub_spec hF hv
  have hodd := hv.2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.2; rw [hco] at this; simp at this; omega
  · have := congrArg (fun x => (G.co x).2) h; simp only [hco] at this; omega

theorem halve_mergeOK (hF : G.Full) (hR : 2 ≤ G.R) (hC : 5 ≤ G.C) :
    MergeOK (Em := G.hEm) (h := G.hHub) (tw := G.hTw) (f := G.hMv) G.Rook G.colHalve.Rook where
  hub u hu := hHub_ne hF hu
  ee u w huw hS hu hw := by
    obtain ⟨-, -, hr⟩ := rook_pair huw hS
    obtain ⟨ha, hco⟩ := hHub_spec hF hu
    obtain ⟨ha', hco'⟩ := hHub_spec hF hw
    have h1 := hu.2; have h2 := hw.2
    have hne : G.hHub u ≠ G.hHub w := by
      intro h
      have e := congrArg G.co h
      rw [hco, hco'] at e
      simp only [Prod.mk.injEq] at e
      exact huw (G.inj u w hu.1 hw.1 (Prod.ext e.1 (by omega)))
    refine ⟨hne, rook_of hne ⟨ha, ?_⟩ ⟨ha', ?_⟩ ?_⟩
    · rw [hco]; simp only; omega
    · rw [hco']; simp only; omega
    · simp only [colHalve, hco, hco']
      rcases hr with hr | hr
      · exact Or.inl hr
      · exact Or.inr (by rw [hr])
  en u w hS hu hw hwh := by
    have huw : u ≠ w := fun h => hw (h ▸ hu)
    obtain ⟨-, hwa, hr⟩ := rook_pair huw hS
    have hb := G.bdd u hu.1
    have hb' := G.bdd w hwa
    have hu2 := hu.2
    have hw2 : (G.co w).2 % 2 = 0 := by
      by_contra h; exact hw ⟨hwa, by omega⟩
    have hrow : (G.co u).1 = (G.co w).1 := by
      rcases hr with hr | hr
      · exact hr
      · omega
    obtain ⟨ha, hco⟩ := hHub_spec hF hu
    have hne : (G.co w).2 ≠ (G.co u).2 - 1 := by
      intro h; apply hwh
      exact G.inj w _ hwa ha (by rw [hco, hrow, ← h])
    obtain ⟨z0, z1, z2, z3, -⟩ := zcol_spec hC hu2 hw2 hb.2 hb'.2
    obtain ⟨ta, tco⟩ := cellOr_spec hF hb.1 z1 u
    change G.act (G.hTw u w) at ta
    change G.co (G.hTw u w) = _ at tco
    have t1 : G.hTw u w ≠ G.hHub u := by
      intro h; have := congrArg (fun x => (G.co x).2) h; simp only [tco, hco] at this
      exact z2 this
    have t2 : G.hTw u w ≠ w := by
      intro h; have := congrArg (fun x => (G.co x).2) h; simp only [tco] at this
      exact z3 this
    refine ⟨fun h => ?_, t1, t2, ?_, ?_⟩
    · have := h.2; rw [tco] at this; simp only at this; omega
    · refine rook_of t1.symm ⟨ha, ?_⟩ ⟨ta, ?_⟩ (Or.inl ?_)
      · rw [hco]; simp only; omega
      · rw [tco]; exact z0
      · simp [colHalve, hco, tco]
    · refine rook_of t2 ⟨ta, ?_⟩ ⟨hwa, hw2⟩ (Or.inl ?_)
      · rw [tco]; exact z0
      · simp [colHalve, tco, hrow]
  nn u w hS hu hw := by
    have huw : u ≠ w := by rintro rfl; have := rook_card hS; simp at this
    obtain ⟨hua, hwa, hr⟩ := rook_pair huw hS
    have hu2 : (G.co u).2 % 2 = 0 := by by_contra h; exact hu ⟨hua, by omega⟩
    have hw2 : (G.co w).2 % 2 = 0 := by by_contra h; exact hw ⟨hwa, by omega⟩
    refine rook_of huw ⟨hua, hu2⟩ ⟨hwa, hw2⟩ ?_
    simp only [colHalve]
    rcases hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr (by rw [hr])
  out e he := by
    refine ⟨rook_card he, ?_⟩
    obtain ⟨v, w, -, rfl, hv, hw, -⟩ := he
    intro x hx hEx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · have := hv.2; have := hEx.2; omega
    · have := hw.2; have := hEx.2; omega
  mv u hu := by
    have hb := G.bdd u hu.1
    have hu2 := hu.2
    obtain ⟨ha, hco⟩ := hHub_spec hF hu
    have hor : orow (G.co u).1 < G.R := by unfold orow; split_ifs <;> omega
    obtain ⟨ga, gco⟩ := cellOr_spec hF hor (by omega : (G.co u).2 - 1 < G.C) u
    have hne : G.hHub u ≠ G.cellOr (orow (G.co u).1, (G.co u).2 - 1) u := by
      intro h; have := congrArg (fun x => (G.co x).1) h; simp only [hco, gco] at this
      unfold orow at this; split_ifs at this <;> omega
    refine rook_of hne ⟨ha, ?_⟩ ⟨ga, ?_⟩ (Or.inr ?_)
    · rw [hco]; simp only; omega
    · rw [gco]; simp only; omega
    · simp [colHalve, hco, gco]

lemma hub_fiber (hF : G.Full) (v : Fin n) :
    (univ.filter (fun x => G.hEm x ∧ G.hHub x = v)).card ≤ 1 := by
  apply card_le_one.2
  intro x hx y hy
  simp only [mem_filter, mem_univ, true_and] at hx hy
  obtain ⟨-, hcx⟩ := hHub_spec hF hx.1
  obtain ⟨-, hcy⟩ := hHub_spec hF hy.1
  have e : G.co (G.hHub x) = G.co (G.hHub y) := by rw [hx.2, hy.2]
  rw [hcx, hcy] at e
  simp only [Prod.mk.injEq] at e
  have := hx.1.2; have := hy.1.2
  exact G.inj x y hx.1.1 hy.1.1 (Prod.ext e.1 (by omega))

/-- The twins at `v` come from pairs whose kept end is one of at most four vertices. -/
noncomputable def twSet (v : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => G.act w ∧ (G.co w).1 = (G.co v).1 ∧
    (G.co w).2 ∈ ({(G.co v).2 + 2, (G.co v).2 - 2, (G.co v).2 + 4, (G.co v).2 - 4} : Finset ℕ))

lemma twSet_card (v : Fin n) : (G.twSet v).card ≤ 4 := by
  calc _ ≤ ({(G.co v).2 + 2, (G.co v).2 - 2, (G.co v).2 + 4, (G.co v).2 - 4} : Finset ℕ).card := by
        apply card_le_card_of_injOn (fun w => (G.co w).2)
        · intro w hw
          simp only [twSet, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
          exact hw.2.2
        · intro w hw w' hw' h
          simp only [twSet, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
          exact G.inj w w' hw.1 hw'.1 (Prod.ext (hw.2.1.trans hw'.2.1.symm) h)
    _ ≤ 4 := card_le_four

lemma twSet_spec (hF : G.Full) (hC : 5 ≤ G.C) (v : Fin n) :
    ∀ a b, G.Rook {a, b} → G.hEm a → ¬ G.hEm b → b ≠ G.hHub a → G.hTw a b = v →
      b ∈ G.twSet v := by
  intro u w hS hu hw hwh htv
  have huw : u ≠ w := fun h => hw (h ▸ hu)
  obtain ⟨-, hwa, hr⟩ := rook_pair huw hS
  have hb := G.bdd u hu.1
  have hb' := G.bdd w hwa
  have hu2 := hu.2
  have hw2 : (G.co w).2 % 2 = 0 := by
    by_contra h; exact hw ⟨hwa, by omega⟩
  have hrow : (G.co u).1 = (G.co w).1 := by
    rcases hr with hr | hr
    · exact hr
    · omega
  obtain ⟨ha, hco⟩ := hHub_spec hF hu
  have hne : (G.co w).2 ≠ (G.co u).2 - 1 := by
    intro h; apply hwh
    exact G.inj w _ hwa ha (by rw [hco, hrow, ← h])
  obtain ⟨-, z1, -, -, z4⟩ := zcol_spec hC hu2 hw2 hb.2 hb'.2
  obtain ⟨-, tco⟩ := cellOr_spec hF hb.1 z1 u
  change G.co (G.hTw u w) = _ at tco
  rw [htv] at tco
  simp only [twSet, mem_filter, mem_univ, true_and, tco, mem_insert, mem_singleton]
  exact ⟨hwa, hrow.symm, by omega⟩

lemma mv_fiber (hF : G.Full) (hR : 2 ≤ G.R) (v : Fin n) :
    (univ.filter (fun u => G.hEm u ∧ v ∈ G.hMv u)).card ≤ 1 + G.R := by
  have hsub : univ.filter (fun u => G.hEm u ∧ v ∈ G.hMv u) ⊆
      univ.filter (fun x => G.hEm x ∧ G.hHub x = v) ∪
        univ.filter (fun u => G.act u ∧ (G.co u).2 = (G.co v).2 + 1) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and, hMv, mem_insert, mem_singleton] at hu
    obtain ⟨hE, hv | hv⟩ := hu
    · exact mem_union_left _ (by simp [hE, hv])
    · refine mem_union_right _ ?_
      have hb := G.bdd u hE.1
      have hu2 := hE.2
      have hor : orow (G.co u).1 < G.R := by unfold orow; split_ifs <;> omega
      obtain ⟨-, gco⟩ := cellOr_spec hF hor (by omega : (G.co u).2 - 1 < G.C) u
      rw [← hv] at gco
      simp only [mem_filter, mem_univ, true_and, gco]
      exact ⟨hE.1, by omega⟩
  have hcol : (univ.filter (fun u => G.act u ∧ (G.co u).2 = (G.co v).2 + 1)).card ≤ G.R := by
    calc _ ≤ (range G.R).card := by
          apply card_le_card_of_injOn (fun w => (G.co w).1)
          · intro w hw
            simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
            simpa using (G.bdd w hw.1).1
          · intro w hw w' hw' h
            simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
            exact G.inj w w' hw.1 hw'.1 (Prod.ext h (hw.2.trans hw'.2.symm))
      _ = G.R := card_range _
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 1 + G.R := add_le_add (hub_fiber hF v) hcol

/-- **The halving segment.** -/
theorem halve_seg (hF : G.Full) (hR : 2 ≤ G.R) (hC : 5 ≤ G.C) {P : Finset (Finset (Fin n))}
    (hP : ∀ e ∈ P, G.Rook e) :
    SegOK G.hSeg P ∧ (∀ e ∈ prun G.hSeg P G.hSeg.length, G.colHalve.Rook e) ∧
      ∀ v, passSum G.hSeg P v ≤ 25 * (G.R + G.C) + 1 := by
  have hm := halve_mergeOK hF hR hC
  have hP' : ∀ e ∈ P, e.card = 2 ∧ G.Rook e := fun e he => ⟨rook_card (hP e he), hP e he⟩
  obtain ⟨hseg, hout⟩ := merge_seg hm hP'
  refine ⟨hseg, hout, fun v => ?_⟩
  have h0 := merge_load0 (f := G.hMv) hP' (G.deg_le hP) v (hub_fiber hF v) (twSet_spec hF hC v)
  have h1 := merge_load1 hm hP' v
  have h4 := twSet_card (G := G) v
  have h5 := mv_fiber hF hR v
  unfold passSum
  simp only [hSeg, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, sum_range_succ,
    sum_range_zero]
  have : (1 + 1 + (G.twSet v).card) * (G.R + G.C) ≤ 6 * (G.R + G.C) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

end Grid

end RefinedAbsorption.OddGrid
