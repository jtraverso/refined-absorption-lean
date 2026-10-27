module
public import RequestProject.OddGrid.Extra
public import RequestProject.OddGrid.Greedy

/-!
# The first stage: routing the input graph into rook pairs

Let `Gb` extend the full grid `G` by an extra column, with every vertex of `Fin n` active in `Gb`.
An input pair `{u, w}` that is not a rook pair is routed along `u, (r_u, x), (r_w, x), w`, where the
column `x = κ e < C` avoids the columns of `u` and `w`.  `xstage`: the stage is valid, its output
consists of rook pairs of `Gb`, and its load at `v` is at most `D + L`, where `D` bounds the degrees
of the input and `L` bounds how often a row sees a colour of `κ`.  `exists_kappa`: a suitable
colouring `κ` exists (greedy colouring).
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset Classical

variable {n : ℕ}

namespace Grid

variable (G : Grid n)

/-- The route of an input pair. -/
noncomputable def xroute (u w : Fin n) (x : ℕ) : Route n :=
  if (G.co u).1 = (G.co w).1 ∨ (G.co u).2 = (G.co w).2 then .walk [u, w]
  else .walk [u, G.cellOr ((G.co u).1, x) u, G.cellOr ((G.co w).1, x) u, w]

/-- The first stage. -/
noncomputable def xSpec0 (κ : Finset (Fin n) → ℕ) : Spec n := fun _ e =>
  if hne : e.Nonempty then G.xroute (e.min' hne) (e.max' hne) (κ e) else .walk []

/-- The rows touched by a pair. -/
noncomputable def rowsOf (e : Finset (Fin n)) : Finset ℕ := e.image (fun v => (G.co v).1)

/-- The columns of a pair. -/
noncomputable def colsOf (e : Finset (Fin n)) : Finset ℕ := e.image (fun v => (G.co v).2)

variable {G} {Gb : Grid n}

lemma row_lt (hx : ExtraOK G Gb) (hall : ∀ v, Gb.act v) (v : Fin n) : (G.co v).1 < G.R := by
  by_cases h : G.act v
  · exact (G.bdd v h).1
  · exact (hx.col v (hall v) h).2

lemma xroute_ok (hF : G.Full) (hx : ExtraOK G Gb) (hall : ∀ v, Gb.act v) {u w : Fin n}
    (huw : u ≠ w) {x : ℕ} (hxC : x < G.C) (hxu : x ≠ (G.co u).2) (hxw : x ≠ (G.co w).2) :
    RouteOK {u, w} (G.xroute u w x) ∧ (∀ p ∈ (G.xroute u w x).pairs, Gb.Rook p) ∧
      (G.xroute u w x).isMove = false ∧
      ∀ e v, v ∈ (G.xroute u w x).visit e →
        v = u ∨ v = w ∨ G.co v = ((G.co u).1, x) ∨ G.co v = ((G.co w).1, x) := by
  unfold xroute
  split_ifs with hr
  · refine ⟨routeOK_walk2 huw, ?_, rfl, ?_⟩
    · intro p hp
      simp only [pairs_walk2, mem_singleton] at hp
      subst hp
      exact rook_of huw (hall u) (hall w) (by rw [hx.co, hx.co]; exact hr)
    · intro e v hv
      simp only [Route.visit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, mem_insert,
        mem_singleton] at hv
      tauto
  · push_neg at hr
    obtain ⟨aa, aco⟩ := cellOr_spec hF (row_lt hx hall u) hxC u
    obtain ⟨ba, bco⟩ := cellOr_spec hF (row_lt hx hall w) hxC u
    set a := G.cellOr ((G.co u).1, x) u
    set b := G.cellOr ((G.co w).1, x) u
    have h1 : u ≠ a := by
      intro h; have := congrArg (fun y => (G.co y).2) h; simp only [aco] at this; exact hxu this.symm
    have h2 : a ≠ b := by
      intro h; have := congrArg (fun y => (G.co y).1) h; simp only [aco, bco] at this
      exact hr.1 this
    have h3 : b ≠ w := by
      intro h; have := congrArg (fun y => (G.co y).2) h; simp only [bco] at this; exact hxw this
    refine ⟨routeOK_walk4 h1 h2 h3 huw, ?_, rfl, ?_⟩
    · intro p hp
      simp only [pairs_walk4, mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact rook_of h1 (hall _) (hall _) (Or.inl (by rw [hx.co, hx.co, aco]))
      · exact rook_of h2 (hall _) (hall _) (Or.inr (by rw [hx.co, hx.co, aco, bco]))
      · exact rook_of h3 (hall _) (hall _) (Or.inl (by rw [hx.co, hx.co, bco]))
    · intro e v hv
      simp only [Route.visit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, mem_insert,
        mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl aco))
      · exact Or.inr (Or.inr (Or.inr bco))
      · exact Or.inr (Or.inl rfl)

/-- **The first stage.** -/
theorem xstage (hF : G.Full) (hx : ExtraOK G Gb) (hall : ∀ v, Gb.act v)
    {X : Finset (Finset (Fin n))} (hX2 : ∀ e ∈ X, e.card = 2) {D L : ℕ}
    (hD : ∀ v, (X.filter (v ∈ ·)).card ≤ D) {κ : Finset (Fin n) → ℕ}
    (hκ : ∀ e ∈ X, κ e < G.C ∧ κ e ∉ G.colsOf e)
    (hL : ∀ ρ x, (X.filter (fun e => ρ ∈ G.rowsOf e ∧ κ e = x)).card ≤ L) :
    SegOK [G.xSpec0 κ] X ∧ (∀ e ∈ prun [G.xSpec0 κ] X [G.xSpec0 κ].length, Gb.Rook e) ∧
      (∀ e ∈ X, (rt [G.xSpec0 κ] X 0 e).isMove = false) ∧
      ∀ v, passSum [G.xSpec0 κ] X v ≤ D + L := by
  have key : ∀ e ∈ X, ∃ u w, u ≠ w ∧ e = {u, w} ∧ G.xSpec0 κ X e = G.xroute u w (κ e) ∧
      κ e < G.C ∧ κ e ≠ (G.co u).2 ∧ κ e ≠ (G.co w).2 := by
    intro e he
    obtain ⟨hne, he', hlt⟩ := eq_pair_min_max (hX2 e he)
    obtain ⟨hC, hcol⟩ := hκ e he
    refine ⟨_, _, hlt, he', by simp only [xSpec0, dif_pos hne], hC, ?_, ?_⟩
    · intro h; apply hcol; exact mem_image.2 ⟨_, min'_mem _ _, h.symm⟩
    · intro h; apply hcol; exact mem_image.2 ⟨_, max'_mem _ _, h.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht e he
    simp only [List.length_cons, List.length_nil] at ht
    obtain rfl : t = 0 := by omega
    obtain ⟨u, w, huw, rfl, hrt, hC, h1, h2⟩ := key e he
    change RouteOK {u, w} (G.xSpec0 κ X {u, w}) ∧ ((G.xSpec0 κ X {u, w}).isMove = true → _)
    rw [hrt]
    obtain ⟨hok, -, hmv, -⟩ := xroute_ok hF hx hall huw hC h1 h2
    exact ⟨hok, fun h => by rw [hmv] at h; exact absurd h (by simp)⟩
  · intro p hp
    simp only [List.length_cons, List.length_nil, zero_add] at hp
    rw [prun_succ, mem_biUnion] at hp
    obtain ⟨e, he, hpe⟩ := hp
    obtain ⟨u, w, huw, rfl, hrt, hC, h1, h2⟩ := key e he
    change p ∈ (G.xSpec0 κ X {u, w}).pairs at hpe
    rw [hrt] at hpe
    exact (xroute_ok hF hx hall huw hC h1 h2).2.1 p hpe
  · intro e he
    obtain ⟨u, w, huw, rfl, hrt, hC, h1, h2⟩ := key e he
    change (G.xSpec0 κ X {u, w}).isMove = false
    rw [hrt]
    exact (xroute_ok hF hx hall huw hC h1 h2).2.2.1
  · intro v
    unfold passSum
    simp only [List.length_cons, List.length_nil, zero_add, sum_range_one]
    have hsub : (prun [G.xSpec0 κ] X 0).filter (fun e => v ∈ (rt [G.xSpec0 κ] X 0 e).visit e) ⊆
        X.filter (v ∈ ·) ∪ X.filter (fun e => (G.co v).1 ∈ G.rowsOf e ∧ κ e = (G.co v).2) := by
      intro e he
      obtain ⟨heX, hv⟩ := mem_filter.1 he
      change e ∈ X at heX
      obtain ⟨u, w, huw, rfl, hrt, hC, h1, h2⟩ := key e heX
      change v ∈ (G.xSpec0 κ X {u, w}).visit {u, w} at hv
      rw [hrt] at hv
      rcases (xroute_ok hF hx hall huw hC h1 h2).2.2.2 _ v hv with rfl | rfl | h | h
      · exact mem_union_left _ (mem_filter.2 ⟨heX, by simp⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨heX, by simp⟩)
      · refine mem_union_right _ (mem_filter.2 ⟨heX, ?_, by rw [h]⟩)
        exact mem_image.2 ⟨u, by simp, by rw [h]⟩
      · refine mem_union_right _ (mem_filter.2 ⟨heX, ?_, by rw [h]⟩)
        exact mem_image.2 ⟨w, by simp, by rw [h]⟩
    unfold pass
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ D + L := add_le_add (hD v) (hL _ _)

end Grid

end RefinedAbsorption.OddGrid
