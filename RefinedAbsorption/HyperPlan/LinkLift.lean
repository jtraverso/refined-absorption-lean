module
public import RefinedAbsorption.HyperPlan.Segment

/-!
# Lifting routes from the link of a vertex

To make a vertex `u` disappear, the sets containing `u` have to be merged until `u` lies in a single
set (only then can `u` be moved away).  The sets containing `u` form the *link* of `u`, a family of
`(r - 1)`-sets, and rerouting inside the link is a problem of uniformity `r - 1`.  This file shows
that the moves of uniformity `r - 1` (with parameter `q - 1`) can be lifted to moves of uniformity
`r` (with parameter `q`).

For a route `ro` of the `(r - 1)`-set `f` and two new vertices `u` (the vertex whose link is
rerouted) and `tw` (a *twin*), the lifted route of `f ∪ {u}` is

  `ro` with `u` added  −  `ro` with `tw` added  +  `f ∪ {tw}`.

* `defect_liftRoute_*`: the defect of the lifted route at `S` is the link defect at `S \ {u}` if
  `u ∈ S ∌ tw`, minus the link defect at `S \ {tw}` if `tw ∈ S ∌ u`, and `0` otherwise.
* `routeOKR_liftRoute`: a valid route of uniformity `r - 1` (parameter `q - 1`) lifts to a valid
  route of uniformity `r` (parameter `q`), for the same weights.
* `allowedR_subset_link`: the values allowed by loneliness at `f ∪ {u}` in a family `P` are allowed at
  `f` in the link of `u` in `P`, so loneliness in the link may be used.
* `visitR_liftRoute`: the lifted route visits the vertices visited in the link, plus `u` and `tw`.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ}

/-- The route of `f ∪ {u}` lifted from the route `ro` of `f` in the link of `u`, with twin `tw`. -/
def liftRoute (u tw : Fin n) (f : Finset (Fin n)) (ro : List (Finset (Fin n) × ZMod K)) :
    List (Finset (Fin n) × ZMod K) :=
  ro.map (fun p => (insert u p.1, p.2)) ++ ro.map (fun p => (insert tw p.1, -p.2)) ++
    [(insert tw f, 1)]

/-- The link of `u` in `P`. -/
def linkF (P : Finset (Finset (Fin n))) (u : Fin n) : Finset (Finset (Fin n)) :=
  (P.filter (u ∈ ·)).image (·.erase u)

lemma lfcl_append (l₁ l₂ : List (Finset (Fin n) × ZMod K)) (S : Finset (Fin n)) :
    lfcl (l₁ ++ l₂) S = lfcl l₁ S + lfcl l₂ S := by
  simp [lfcl]

lemma lfcl_map_insert (a : Fin n) (S : Finset (Fin n)) (c : ZMod K → ZMod K)
    (ro : List (Finset (Fin n) × ZMod K)) :
    lfcl (ro.map fun p => (insert a p.1, c p.2)) S =
      (ro.map fun p => if S.erase a ⊆ p.1 then c p.2 else 0).sum := by
  unfold lfcl
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp, subset_insert_iff]

lemma sum_map_ite_zero (ro : List (Finset (Fin n) × ZMod K)) (P : Finset (Fin n) → Prop)
    [DecidablePred P] (c : ZMod K → ZMod K) (h : ∀ p ∈ ro, ¬ P p.1) :
    (ro.map fun p => if P p.1 then c p.2 else 0).sum = 0 := by
  rw [List.map_congr_left (g := fun _ => (0 : ZMod K))]
  · simp
  · intro p hp; simp [h p hp]

lemma sum_map_ite_neg (ro : List (Finset (Fin n) × ZMod K)) (P : Finset (Fin n) → Prop)
    [DecidablePred P] :
    (ro.map fun p => if P p.1 then -p.2 else 0).sum =
      -(ro.map fun p => if P p.1 then p.2 else 0).sum := by
  induction ro with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    split_ifs <;> ring

variable {u tw : Fin n} {f : Finset (Fin n)} {ro : List (Finset (Fin n) × ZMod K)}

/-- Hypotheses of a lift: `u` and `tw` are distinct and new. -/
structure LiftOK (u tw : Fin n) (f : Finset (Fin n)) (ro : List (Finset (Fin n) × ZMod K)) :
    Prop where
  ne : u ≠ tw
  uf : u ∉ f
  twf : tw ∉ f
  uro : ∀ p ∈ ro, u ∉ p.1
  twro : ∀ p ∈ ro, tw ∉ p.1

lemma lfcl_liftRoute (S : Finset (Fin n)) :
    lfcl (liftRoute u tw f ro) S =
      (ro.map fun p => if S.erase u ⊆ p.1 then p.2 else 0).sum +
      (ro.map fun p => if S.erase tw ⊆ p.1 then -p.2 else 0).sum +
      (if S.erase tw ⊆ f then 1 else 0) := by
  unfold liftRoute
  rw [lfcl_append, lfcl_append, lfcl_map_insert u S (fun x => x), lfcl_map_insert tw S (fun x => -x)]
  simp [lfcl, subset_insert_iff]

lemma defect_liftRoute_u (h : LiftOK u tw f ro) {S : Finset (Fin n)} (hu : u ∈ S)
    (htw : tw ∉ S) : defect (liftRoute u tw f ro) (insert u f) S = defect ro f (S.erase u) := by
  rw [defect, lfcl_liftRoute, defect]
  have hS : S.erase tw = S := erase_eq_of_notMem htw
  rw [hS]
  have h2 : (ro.map fun p => if S ⊆ p.1 then -p.2 else 0).sum = 0 :=
    sum_map_ite_zero ro (S ⊆ ·) _ fun p hp hsub => h.uro p hp (hsub hu)
  have h3 : ¬ S ⊆ f := fun hsub => h.uf (hsub hu)
  rw [h2, if_neg h3]
  simp only [subset_insert_iff]
  unfold lfcl
  ring

lemma defect_liftRoute_tw (h : LiftOK u tw f ro) {S : Finset (Fin n)} (hu : u ∉ S)
    (htw : tw ∈ S) : defect (liftRoute u tw f ro) (insert u f) S = -defect ro f (S.erase tw) := by
  rw [defect, lfcl_liftRoute, defect]
  have hS : S.erase u = S := erase_eq_of_notMem hu
  rw [hS]
  have h1 : (ro.map fun p => if S ⊆ p.1 then p.2 else 0).sum = 0 :=
    sum_map_ite_zero ro (S ⊆ ·) (fun x => x) fun p hp hsub => h.twro p hp (hsub htw)
  have h3 : ¬ S ⊆ insert u f := fun hsub => by
    rcases mem_insert.1 (hsub htw) with h' | h'
    · exact h.ne h'.symm
    · exact h.twf h'
  rw [h1, if_neg h3]
  rw [sum_map_ite_neg]
  unfold lfcl
  ring

lemma defect_liftRoute_none {S : Finset (Fin n)} (hu : u ∉ S)
    (htw : tw ∉ S) : defect (liftRoute u tw f ro) (insert u f) S = 0 := by
  rw [defect, lfcl_liftRoute, erase_eq_of_notMem hu, erase_eq_of_notMem htw, sum_map_ite_neg]
  have : S ⊆ insert u f ↔ S ⊆ f := by
    rw [subset_insert_iff, erase_eq_of_notMem hu]
  simp only [this]
  ring

lemma defect_liftRoute_both (h : LiftOK u tw f ro) {S : Finset (Fin n)} (hu : u ∈ S)
    (htw : tw ∈ S) : defect (liftRoute u tw f ro) (insert u f) S = 0 := by
  rw [defect, lfcl_liftRoute]
  have hu' : u ∈ S.erase tw := mem_erase.2 ⟨h.ne, hu⟩
  have htw' : tw ∈ S.erase u := mem_erase.2 ⟨h.ne.symm, htw⟩
  rw [sum_map_ite_zero ro (S.erase u ⊆ ·) (fun x => x) fun p hp hsub => h.twro p hp (hsub htw'),
    sum_map_ite_zero ro (S.erase tw ⊆ ·) (fun x => -x) fun p hp hsub => h.uro p hp (hsub hu'),
    if_neg (fun hsub => h.uf (hsub hu')), if_neg (fun hsub => by
      rcases mem_insert.1 (hsub htw) with h' | h'
      · exact h.ne h'.symm
      · exact h.twf h')]
  ring

variable [NeZero K]

/-- **Lifting a valid route from the link.**  A route of the `(r - 1)`-set `f` that is valid for
the parameters `(q - 1, r - 1)` lifts to a route of `f ∪ {u}` that is valid for `(q, r)`, for the
same weights. -/
theorem routeOKR_liftRoute {q r : ℕ} (hK : ModsOK q r K) (hr : 1 ≤ r) (h : LiftOK u tw f ro)
    (hf : f.card = r - 1) {A : Finset (ZMod K)} (hro : RouteOKR (q - 1) (r - 1) f ro A) :
    RouteOKR q r (insert u f) (liftRoute u tw f ro) A := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [liftRoute, List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with (⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩) | rfl
    · rw [card_insert_of_notMem (h.uro p' hp'), hro.1 p' hp']; omega
    · rw [card_insert_of_notMem (h.twro p' hp'), hro.1 p' hp']; omega
    · rw [card_insert_of_notMem h.twf, hf]; omega
  · intro s hs S hS
    by_cases hu : u ∈ S <;> by_cases htw : tw ∈ S
    · rw [defect_liftRoute_both h hu htw, zero_mul, ZMod.val_zero]; exact dvd_zero _
    · rw [defect_liftRoute_u h hu htw]
      have hc : (S.erase u).card = S.card - 1 := card_erase_of_mem hu
      have hpos : 1 ≤ S.card := card_pos.2 ⟨u, hu⟩
      have := hro.2 s hs (S.erase u) (by omega)
      rw [hc] at this
      have e1 : q - 1 - (S.card - 1) = q - S.card := by omega
      have e2 : r - 1 - (S.card - 1) = r - S.card := by omega
      rwa [e1, e2] at this
    · rw [defect_liftRoute_tw h hu htw]
      have hc : (S.erase tw).card = S.card - 1 := card_erase_of_mem htw
      have hpos : 1 ≤ S.card := card_pos.2 ⟨tw, htw⟩
      have := hro.2 s hs (S.erase tw) (by omega)
      rw [hc] at this
      have e1 : q - 1 - (S.card - 1) = q - S.card := by omega
      have e2 : r - 1 - (S.card - 1) = r - S.card := by omega
      rw [e1, e2] at this
      rw [neg_mul, ← neg_one_mul]
      exact dvd_val_mul (hK _ hS) this
    · rw [defect_liftRoute_none hu htw, zero_mul, ZMod.val_zero]; exact dvd_zero _

/-- **Loneliness in the link.**  A value allowed at `f ∪ {u}` in `P` is allowed at `f` in the link
of `u` (for the parameters `(q - 1, r - 1)`). -/
theorem allowedR_subset_link {q r : ℕ} (P : Finset (Finset (Fin n))) (hu : u ∉ f) :
    allowedR (K := K) q r P (insert u f) ⊆ allowedR (q - 1) (r - 1) (linkF P u) f := by
  intro s hs
  simp only [allowedR, mem_filter, mem_univ, true_and, mem_powerset] at hs ⊢
  intro T hT hTc hlone
  have hTu : u ∉ T := fun h' => hu (hT h')
  have key := hs (insert u T) (insert_subset_insert u hT)
    (by rw [card_insert_of_notMem hTu]; omega) ?_
  · rw [card_insert_of_notMem hTu] at key
    have e1 : q - (T.card + 1) = q - 1 - T.card := by omega
    have e2 : r - (T.card + 1) = r - 1 - T.card := by omega
    rwa [e1, e2] at key
  · intro g hg hsub
    have hug : u ∈ g := hsub (mem_insert_self u T)
    have hmem : g.erase u ∈ linkF P u := mem_image.2 ⟨g, mem_filter.2 ⟨hg, hug⟩, rfl⟩
    have hT' : T ⊆ g.erase u := fun x hx =>
      mem_erase.2 ⟨fun hxu => hTu (hxu ▸ hx), hsub (mem_insert_of_mem hx)⟩
    have := hlone _ hmem hT'
    rw [← this, insert_erase hug]

omit [NeZero K] in
/-- The vertices visited by a lifted route. -/
lemma visitR_liftRoute : visitR (insert u f) (liftRoute u tw f ro) ⊆
    insert u (insert tw (visitR f ro)) := by
  intro x hx
  unfold visitR at hx
  rcases mem_union.1 hx with hx | hx
  · rcases mem_insert.1 hx with rfl | hx
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_of_mem (subset_visitR f ro hx))
  · obtain ⟨g, hg, hxg⟩ := mem_sup.1 hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hg)
    simp only [liftRoute, List.mem_append, List.mem_map, List.mem_singleton] at hp
    simp only [id] at hxg
    rcases hp with (⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩) | rfl
    · rcases mem_insert.1 hxg with rfl | hx'
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_of_mem (route_subset_visitR f hp' hx'))
    · rcases mem_insert.1 hxg with rfl | hx'
      · exact mem_insert_of_mem (mem_insert_self _ _)
      · exact mem_insert_of_mem (mem_insert_of_mem (route_subset_visitR f hp' hx'))
    · rcases mem_insert.1 hxg with rfl | hx'
      · exact mem_insert_of_mem (mem_insert_self _ _)
      · exact mem_insert_of_mem (mem_insert_of_mem (subset_visitR f ro hx'))

omit [NeZero K] in
lemma length_liftRoute : (liftRoute u tw f ro).length = 2 * ro.length + 1 := by
  simp [liftRoute]; ring

end RefinedAbsorption.HyperPlan
