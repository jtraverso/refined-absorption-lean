module
public import RefinedAbsorption.OddGrid.Concat

/-!
# Merging a set of vertices into hubs

A two-stage segment `[mergeSpec, moveSpec]` empties a set `Em` of vertices.

* Stage 1 (`mergeSpec`): every pair at an emptied vertex `u` is rerouted through the *hub* `h u`,
  so that afterwards the only pair at `u` is `{u, h u}`.  Pairs between an emptied and a kept
  vertex use a *twin* `tw u w`.
* Stage 2 (`moveSpec`): the pair `{u, h u}` is now alone at `u` and is moved to the pair `f u`.

`merge_seg` proves validity (`SegOK`), that the output pairs satisfy the target predicate `S'`,
and bounds the loads.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset

variable {n : ℕ}

lemma eq_pair_min_max {e : Finset (Fin n)} (he : e.card = 2) :
    ∃ hne : e.Nonempty, e = {e.min' hne, e.max' hne} ∧ e.min' hne ≠ e.max' hne := by
  have hne : e.Nonempty := card_pos.1 (by omega)
  refine ⟨hne, ?_, ?_⟩
  · symm
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact min'_mem _ _
      · exact max'_mem _ _
    · rw [he, card_pair (min'_lt_max'_of_card e (by omega)).ne]
  · exact (min'_lt_max'_of_card e (by omega)).ne

lemma routeOK_walk2 {a b : Fin n} (hab : a ≠ b) : RouteOK {a, b} (.walk [a, b]) :=
  ⟨a, [b], rfl, by simp [hab], by simp, by simp, by simp, by simpa using hab⟩

lemma routeOK_walk4 {a b c d : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d) :
    RouteOK {a, d} (.walk [a, b, c, d]) :=
  ⟨a, [b, c, d], rfl, by simp [hab, hbc, hcd], by simp [Nat.even_iff], by simp, by simp, by simpa using had⟩

lemma pairs_walk2 (a b : Fin n) : (Route.walk [a, b]).pairs = {{a, b}} := by
  simp [Route.pairs, wpairs]

lemma pairs_walk4 (a b c d : Fin n) :
    (Route.walk [a, b, c, d]).pairs = {{a, b}, {b, c}, {c, d}} := by
  ext x; simp [Route.pairs, wpairs]

lemma pair_sub_visit {r : Route n} {e p : Finset (Fin n)} (hp : p ∈ r.pairs) : p ⊆ r.visit e := by
  cases r with
  | walk l =>
    simp only [Route.pairs, List.mem_toFinset] at hp
    exact wpairs_subset hp
  | move f =>
    simp only [Route.pairs, mem_singleton] at hp
    subst hp; exact subset_union_right

/-- The pairs at `v` after a stage are at most three times the load of the stage, if every route
uses at most three pairs. -/
lemma card_prun_succ_le (l : List (Spec n)) (P : Finset (Finset (Fin n))) (t : ℕ) (v : Fin n)
    (hc : ∀ e ∈ prun l P t, (rt l P t e).pairs.card ≤ 3) :
    ((prun l P (t + 1)).filter (v ∈ ·)).card ≤ 3 * pass l P t v := by
  have hsub : (prun l P (t + 1)).filter (v ∈ ·) ⊆
      ((prun l P t).filter (fun e => v ∈ (rt l P t e).visit e)).biUnion
        (fun e => (rt l P t e).pairs) := by
    intro p hp
    rw [mem_filter, prun_succ, mem_biUnion] at hp
    obtain ⟨⟨e, he, hpe⟩, hv⟩ := hp
    exact mem_biUnion.2 ⟨e, mem_filter.2 ⟨he, pair_sub_visit hpe hv⟩, hpe⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ e ∈ (prun l P t).filter (fun e => v ∈ (rt l P t e).visit e), (rt l P t e).pairs.card :=
        card_biUnion_le
    _ ≤ ∑ e ∈ (prun l P t).filter (fun e => v ∈ (rt l P t e).visit e), 3 :=
        sum_le_sum fun e he => hc e (mem_filter.1 he).1
    _ = 3 * pass l P t v := by rw [sum_const, smul_eq_mul, mul_comm]; rfl

/-- Pairs meeting a set `W` of vertices number at most `|W| Δ`. -/
lemma card_filter_meet_le (P : Finset (Finset (Fin n))) (W : Finset (Fin n)) {Δ : ℕ}
    (hΔ : ∀ x, (P.filter (x ∈ ·)).card ≤ Δ) :
    (P.filter (fun e => ∃ x ∈ W, x ∈ e)).card ≤ W.card * Δ := by
  have hsub : P.filter (fun e => ∃ x ∈ W, x ∈ e) ⊆ W.biUnion (fun x => P.filter (x ∈ ·)) := by
    intro e he
    obtain ⟨he, x, hx, hxe⟩ := mem_filter.1 he
    exact mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨he, hxe⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ x ∈ W, (P.filter (x ∈ ·)).card := card_biUnion_le
    _ ≤ ∑ x ∈ W, Δ := sum_le_sum fun x _ => hΔ x
    _ = W.card * Δ := by rw [sum_const, smul_eq_mul]

section Merge

variable (Em : Fin n → Prop) [DecidablePred Em] (h : Fin n → Fin n)
  (tw : Fin n → Fin n → Fin n) (f : Fin n → Finset (Fin n))

/-- The route of the pair `{u, w}` in the merge stage. -/
def mroute (u w : Fin n) : Route n :=
  if Em u then
    if Em w then .walk [u, h u, h w, w]
    else if w = h u then .walk [u, w] else .walk [u, h u, tw u w, w]
  else if Em w then
    if u = h w then .walk [w, u] else .walk [w, h w, tw w u, u]
  else .walk [u, w]

/-- The merge stage. -/
def mergeSpec : Spec n := fun _ e =>
  if hne : e.Nonempty then mroute Em h tw (e.min' hne) (e.max' hne) else .walk []

/-- The move stage. -/
def moveSpec : Spec n := fun _ e =>
  if hne : e.Nonempty then
    if Em (e.min' hne) then .move (f (e.min' hne))
    else if Em (e.max' hne) then .move (f (e.max' hne))
    else .walk [e.min' hne, e.max' hne]
  else .walk []

/-- The pairs left by the merge stage at emptied vertices. -/
def Mg (e : Finset (Fin n)) : Prop := ∃ u, Em u ∧ e = {u, h u}

variable {Em h tw f} (S S' : Finset (Fin n) → Prop)

/-- The hypotheses of a merge. -/
structure MergeOK : Prop where
  hub : ∀ u, Em u → ¬ Em (h u) ∧ h u ≠ u
  ee : ∀ u w, u ≠ w → S {u, w} → Em u → Em w → h u ≠ h w ∧ S' {h u, h w}
  en : ∀ u w, S {u, w} → Em u → ¬ Em w → w ≠ h u →
    ¬ Em (tw u w) ∧ tw u w ≠ h u ∧ tw u w ≠ w ∧ S' {h u, tw u w} ∧ S' {tw u w, w}
  nn : ∀ u w, S {u, w} → ¬ Em u → ¬ Em w → S' {u, w}
  out : ∀ e, S' e → e.card = 2 ∧ ∀ x ∈ e, ¬ Em x
  mv : ∀ u, Em u → S' (f u)

variable {S S'}

lemma mroute_ok (hm : MergeOK (Em := Em) (h := h) (tw := tw) (f := f) S S') {u w : Fin n} (huw : u ≠ w)
    (hS : S {u, w}) :
    RouteOK {u, w} (mroute Em h tw u w) ∧
      (∀ p ∈ (mroute Em h tw u w).pairs, S' p ∨ Mg Em h p) ∧
      (mroute Em h tw u w).isMove = false := by
  have hS' : S {w, u} := by rwa [pair_comm]
  unfold mroute
  split_ifs with h1 h2 h3 h2 h3
  · obtain ⟨hne, hS2⟩ := hm.ee u w huw hS h1 h2
    refine ⟨routeOK_walk4 (hm.hub u h1).2.symm hne (hm.hub w h2).2 huw, ?_, rfl⟩
    intro p hp
    simp only [pairs_walk4, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inr ⟨u, h1, rfl⟩
    · exact Or.inl hS2
    · exact Or.inr ⟨w, h2, pair_comm _ _⟩
  · subst h3
    refine ⟨routeOK_walk2 huw, ?_, rfl⟩
    intro p hp
    simp only [pairs_walk2, mem_singleton] at hp
    exact Or.inr ⟨u, h1, hp⟩
  · obtain ⟨hE, h1', h2', hS1, hS2⟩ := hm.en u w hS h1 h2 h3
    refine ⟨routeOK_walk4 (hm.hub u h1).2.symm h1'.symm h2' huw, ?_, rfl⟩
    intro p hp
    simp only [pairs_walk4, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inr ⟨u, h1, rfl⟩
    · exact Or.inl hS1
    · exact Or.inl hS2
  · subst h3
    refine ⟨by rw [pair_comm]; exact routeOK_walk2 huw.symm, ?_, rfl⟩
    intro p hp
    simp only [pairs_walk2, mem_singleton] at hp
    exact Or.inr ⟨w, h2, hp⟩
  · obtain ⟨hE, h1', h2', hS1, hS2⟩ := hm.en w u hS' h2 h1 h3
    refine ⟨by rw [pair_comm]; exact routeOK_walk4 (hm.hub w h2).2.symm h1'.symm h2' huw.symm,
      ?_, rfl⟩
    intro p hp
    simp only [pairs_walk4, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inr ⟨w, h2, rfl⟩
    · exact Or.inl hS1
    · exact Or.inl hS2
  · refine ⟨routeOK_walk2 huw, ?_, rfl⟩
    intro p hp
    simp only [pairs_walk2, mem_singleton] at hp
    subst hp; exact Or.inl (hm.nn u w hS h1 h2)

omit [DecidablePred Em] in
lemma mergeSpec_eq {e : Finset (Fin n)} (he : e.card = 2) [DecidablePred Em] :
    ∃ u w, u ≠ w ∧ e = {u, w} ∧ ∀ Q, mergeSpec Em h tw Q e = mroute Em h tw u w := by
  obtain ⟨hne, he', hlt⟩ := eq_pair_min_max he
  exact ⟨_, _, hlt, he', fun Q => by simp only [mergeSpec, dif_pos hne]⟩

lemma moveSpec_out (hm : MergeOK (Em := Em) (h := h) (tw := tw) (f := f) S S')
    {e : Finset (Fin n)} (he : S' e) :
    ∃ u w, u ≠ w ∧ e = {u, w} ∧ ∀ Q, moveSpec Em f Q e = .walk [u, w] := by
  obtain ⟨hc, hE⟩ := hm.out e he
  obtain ⟨hne, he', hlt⟩ := eq_pair_min_max hc
  refine ⟨_, _, hlt, he', fun Q => ?_⟩
  simp only [moveSpec, dif_pos hne, if_neg (hE _ (min'_mem _ _)), if_neg (hE _ (max'_mem _ _))]

lemma moveSpec_mg (hm : MergeOK (Em := Em) (h := h) (tw := tw) (f := f) S S') {u : Fin n}
    (hu : Em u) (Q : Finset (Finset (Fin n))) :
    moveSpec Em f Q {u, h u} = .move (f u) := by
  have hc : ({u, h u} : Finset (Fin n)).card = 2 := card_pair (hm.hub u hu).2.symm
  obtain ⟨hne, he', hlt⟩ := eq_pair_min_max hc
  have hlo := min'_mem _ hne
  have hhi := max'_mem _ hne
  simp only [mem_insert, mem_singleton] at hlo hhi
  simp only [moveSpec, dif_pos hne]
  rcases hlo with hlo | hlo
  · rw [if_pos (by rw [hlo]; exact hu), hlo]
  · rw [if_neg (by rw [hlo]; exact (hm.hub u hu).1)]
    rcases hhi with hhi | hhi
    · rw [if_pos (by rw [hhi]; exact hu), hhi]
    · exact absurd (hlo.trans hhi.symm) hlt

lemma merge_prun_one (hm : MergeOK (Em := Em) (h := h) (tw := tw) (f := f) S S')
    {P : Finset (Finset (Fin n))} (hP : ∀ e ∈ P, e.card = 2 ∧ S e) :
    ∀ p ∈ prun [mergeSpec Em h tw, moveSpec Em f] P 1, S' p ∨ Mg Em h p := by
  intro p hp
  rw [prun_succ, mem_biUnion] at hp
  obtain ⟨e, he, hpe⟩ := hp
  obtain ⟨hc, hS⟩ := hP e he
  obtain ⟨u, w, huw, rfl, hrt⟩ := mergeSpec_eq (Em := Em) (h := h) (tw := tw) hc
  change p ∈ (mergeSpec Em h tw P {u, w}).pairs at hpe
  rw [hrt] at hpe
  exact (mroute_ok hm huw hS).2.1 p hpe

/-- **A merge segment is valid and lands in `S'`.** -/
theorem merge_seg (hm : MergeOK (Em := Em) (h := h) (tw := tw) (f := f) S S')
    {P : Finset (Finset (Fin n))} (hP : ∀ e ∈ P, e.card = 2 ∧ S e) :
    SegOK [mergeSpec Em h tw, moveSpec Em f] P ∧
      ∀ e ∈ prun [mergeSpec Em h tw, moveSpec Em f] P 2, S' e := by
  have h1 := merge_prun_one hm hP
  refine ⟨?_, ?_⟩
  · intro t ht e he
    simp only [List.length_cons, List.length_nil] at ht
    interval_cases t
    · obtain ⟨hc, hS⟩ := hP e he
      obtain ⟨u, w, huw, rfl, hrt⟩ := mergeSpec_eq (Em := Em) (h := h) (tw := tw) hc
      change RouteOK {u, w} (mergeSpec Em h tw P {u, w}) ∧
        ((mergeSpec Em h tw P {u, w}).isMove = true → _)
      rw [hrt]
      obtain ⟨hok, -, hmv⟩ := mroute_ok hm huw hS
      exact ⟨hok, fun h' => by rw [hmv] at h'; exact absurd h' (by simp)⟩
    · change RouteOK e (moveSpec Em f (prun [mergeSpec Em h tw, moveSpec Em f] P 1) e) ∧
        ((moveSpec Em f (prun [mergeSpec Em h tw, moveSpec Em f] P 1) e).isMove = true → _)
      rcases h1 e he with hS' | ⟨u, hu, rfl⟩
      · obtain ⟨a, b, hab, rfl, hrt⟩ := moveSpec_out hm hS'
        rw [hrt]
        exact ⟨routeOK_walk2 hab, fun h' => absurd h' (by simp [Route.isMove])⟩
      · rw [moveSpec_mg hm hu]
        refine ⟨(hm.out _ (hm.mv u hu)).1, fun _ => ⟨u, by simp, fun e' he' hue' => ?_⟩⟩
        rcases h1 e' he' with hS' | ⟨u', hu', rfl⟩
        · exact absurd hu ((hm.out e' hS').2 u hue')
        · simp only [mem_insert, mem_singleton] at hue'
          rcases hue' with rfl | h2
          · rfl
          · exact absurd (h2 ▸ hu) (hm.hub u' hu').1
  · intro p hp
    rw [prun_succ, mem_biUnion] at hp
    obtain ⟨e, he, hpe⟩ := hp
    change p ∈ (moveSpec Em f (prun [mergeSpec Em h tw, moveSpec Em f] P 1) e).pairs at hpe
    rcases h1 e he with hS' | ⟨u, hu, rfl⟩
    · obtain ⟨a, b, hab, rfl, hrt⟩ := moveSpec_out hm hS'
      rw [hrt, pairs_walk2, mem_singleton] at hpe
      rw [hpe]; exact hS'
    · rw [moveSpec_mg hm hu] at hpe
      simp only [Route.pairs, mem_singleton] at hpe
      rw [hpe]; exact hm.mv u hu

omit [DecidablePred Em] in
lemma mroute_pairs_card [DecidablePred Em] (u w : Fin n) :
    (mroute Em h tw u w).pairs.card ≤ 3 := by
  unfold mroute
  split_ifs <;> simp only [pairs_walk2, pairs_walk4] <;>
    first | exact card_le_three | simp

omit [DecidablePred Em] in
lemma mroute_visit [DecidablePred Em] {u w v : Fin n} {e : Finset (Fin n)} {W : Finset (Fin n)}
    (hS : S {u, w})
    (hW : ∀ a b, S {a, b} → Em a → ¬ Em b → b ≠ h a → tw a b = v → b ∈ W)
    (hv : v ∈ (mroute Em h tw u w).visit e) :
    v ∈ ({u, w} : Finset (Fin n)) ∨ (∃ x ∈ ({u, w} : Finset (Fin n)), Em x ∧ h x = v) ∨
      (∃ x ∈ W, x ∈ ({u, w} : Finset (Fin n))) := by
  have hS' : S {w, u} := by rwa [pair_comm]
  unfold mroute at hv
  split_ifs at hv with h1 h2 h3 h2 h3 <;>
    simp only [Route.visit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, mem_insert,
      mem_singleton] at hv
  · rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl ⟨u, by simp, h1, rfl⟩)
    · exact Or.inr (Or.inl ⟨w, by simp, h2, rfl⟩)
    · simp
  · rcases hv with rfl | rfl <;> simp
  · rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl ⟨u, by simp, h1, rfl⟩)
    · exact Or.inr (Or.inr ⟨w, hW u w hS h1 h2 h3 rfl, by simp⟩)
    · simp
  · rcases hv with rfl | rfl <;> simp
  · rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl ⟨w, by simp, h2, rfl⟩)
    · exact Or.inr (Or.inr ⟨u, hW w u hS' h2 h1 h3 rfl, by simp⟩)
    · simp
  · rcases hv with rfl | rfl <;> simp

/-- Load of the merge stage. -/
theorem merge_load0 {P : Finset (Finset (Fin n))} (hP : ∀ e ∈ P, e.card = 2 ∧ S e) {Δ : ℕ}
    (hΔ : ∀ x, (P.filter (x ∈ ·)).card ≤ Δ) (v : Fin n) {a : ℕ}
    (hHf : (univ.filter (fun x => Em x ∧ h x = v)).card ≤ a) {W : Finset (Fin n)}
    (hW : ∀ a b, S {a, b} → Em a → ¬ Em b → b ≠ h a → tw a b = v → b ∈ W) :
    pass [mergeSpec Em h tw, moveSpec Em f] P 0 v ≤ (1 + a + W.card) * Δ := by
  set Hf := univ.filter (fun x => Em x ∧ h x = v)
  have hsub : (prun [mergeSpec Em h tw, moveSpec Em f] P 0).filter
      (fun e => v ∈ (rt [mergeSpec Em h tw, moveSpec Em f] P 0 e).visit e) ⊆
      (P.filter (v ∈ ·) ∪ P.filter (fun e => ∃ x ∈ Hf, x ∈ e)) ∪
        P.filter (fun e => ∃ x ∈ W, x ∈ e) := by
    intro e he
    obtain ⟨heP, hv⟩ := mem_filter.1 he
    change e ∈ P at heP
    obtain ⟨hc, hS⟩ := hP e heP
    obtain ⟨u, w, huw, rfl, hrt⟩ := mergeSpec_eq (Em := Em) (h := h) (tw := tw) hc
    change v ∈ (mergeSpec Em h tw P {u, w}).visit {u, w} at hv
    rw [hrt] at hv
    rcases mroute_visit hS hW hv with h' | ⟨x, hx, hEx, hxv⟩ | ⟨x, hx, hxe⟩
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨heP, h'⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨heP, x,
        mem_filter.2 ⟨mem_univ _, hEx, hxv⟩, hx⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨heP, x, hx, hxe⟩)
  calc pass [mergeSpec Em h tw, moveSpec Em f] P 0 v ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ (P.filter (v ∈ ·)).card + (P.filter (fun e => ∃ x ∈ Hf, x ∈ e)).card +
        (P.filter (fun e => ∃ x ∈ W, x ∈ e)).card := by
        gcongr; exact card_union_le _ _
    _ ≤ Δ + Hf.card * Δ + W.card * Δ := by
        gcongr
        · exact hΔ v
        · exact card_filter_meet_le P Hf hΔ
        · exact card_filter_meet_le P W hΔ
    _ ≤ Δ + a * Δ + W.card * Δ := by gcongr
    _ = (1 + a + W.card) * Δ := by ring

/-- Load of the move stage. -/
theorem merge_load1 (hm : MergeOK (Em := Em) (h := h) (tw := tw) (f := f) S S')
    {P : Finset (Finset (Fin n))} (hP : ∀ e ∈ P, e.card = 2 ∧ S e) (v : Fin n) :
    pass [mergeSpec Em h tw, moveSpec Em f] P 1 v ≤
      3 * pass [mergeSpec Em h tw, moveSpec Em f] P 0 v +
        (univ.filter (fun u => Em u ∧ v ∈ f u)).card := by
  have h1 := merge_prun_one hm hP
  have hsub : (prun [mergeSpec Em h tw, moveSpec Em f] P 1).filter
      (fun e => v ∈ (rt [mergeSpec Em h tw, moveSpec Em f] P 1 e).visit e) ⊆
      (prun [mergeSpec Em h tw, moveSpec Em f] P (0 + 1)).filter (v ∈ ·) ∪
        (univ.filter (fun u => Em u ∧ v ∈ f u)).image (fun u => {u, h u}) := by
    intro e he
    obtain ⟨he, hv⟩ := mem_filter.1 he
    change v ∈ (moveSpec Em f (prun [mergeSpec Em h tw, moveSpec Em f] P 1) e).visit e at hv
    rcases h1 e he with hS' | ⟨u, hu, rfl⟩
    · obtain ⟨a, b, hab, rfl, hrt⟩ := moveSpec_out hm hS'
      rw [hrt] at hv
      refine mem_union_left _ (mem_filter.2 ⟨he, ?_⟩)
      simpa [Route.visit] using hv
    · rw [moveSpec_mg hm hu] at hv
      simp only [Route.visit, mem_union] at hv
      rcases hv with hv | hv
      · exact mem_union_left _ (mem_filter.2 ⟨he, hv⟩)
      · exact mem_union_right _ (mem_image.2 ⟨u, mem_filter.2 ⟨mem_univ _, hu, hv⟩, rfl⟩)
  calc pass [mergeSpec Em h tw, moveSpec Em f] P 1 v ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by
        gcongr
        · apply card_prun_succ_le
          intro e he
          change e ∈ P at he
          obtain ⟨hc, -⟩ := hP e he
          obtain ⟨u, w, -, rfl, hrt⟩ := mergeSpec_eq (Em := Em) (h := h) (tw := tw) hc
          change (mergeSpec Em h tw P {u, w}).pairs.card ≤ 3
          rw [hrt]; exact mroute_pairs_card u w
        · exact card_image_le

end Merge

end RefinedAbsorption.OddGrid
