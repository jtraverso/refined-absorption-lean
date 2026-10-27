module
public import RequestProject.HyperPlan.LinkLift

/-!
# Emptying a vertex by collapsing its link

A vertex `u` disappears from a plan only by a move of a set in which `u` is *lonely* (it lies in no
other current set).  To get there, the link of `u` (the `(r - 1)`-sets `e \ {u}`, `u ∈ e`) has to be
collapsed to a single set.  This file reduces this to a segment of uniformity `r - 1` (parameter
`q - 1`) on the link.

Given a segment `l'` on the link `linkF P u` and twins `tw t f` (one for every stage `t` and every
link set `f`), the *lifted segment* `liftSeg u tw l'` keeps every set not containing `u` and sends
`e ∋ u` along the lifted route (`HyperPlan.LinkLift`) of the route of `e \ {u}` in `l'`.

* `linkF_prunR_liftSeg`: at every stage the link of `u` in the lifted segment is the family of `l'`.
* `segOKR_liftSeg`: if `l'` is a valid segment for `(q - 1, r - 1)`, the lifted segment is valid for
  `(q, r)`.  Loneliness in the link is used freely.
* `passR_liftSeg_le`: the loads of the lifted segment are bounded by the sets not containing `u` and
  the link sets whose (lifted) route visits `S`.
* `card_filter_mem_prunR_liftSeg`: the number of sets containing `u` is the size of the family of
  `l'`; in particular `u` is lonely at the end if `l'` collapses the link to a single set.
* `segOKR_move`, `notMem_prunR_move`, `prunR_move`: once `u` is lonely, one stage moves it to a new
  vertex `u'`, and afterwards no set contains `u`.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ} [NeZero K]

omit [NeZero K] in
lemma routeOKR_mono {q r : ℕ} {e : Finset (Fin n)} {ro : List (Finset (Fin n) × ZMod K)}
    {A A' : Finset (ZMod K)} (h : RouteOKR q r e ro A') (hA : A ⊆ A') : RouteOKR q r e ro A :=
  ⟨h.1, fun s hs => h.2 s (hA hs)⟩

variable (u : Fin n) (tw : ℕ → Finset (Fin n) → Fin n) (l' : List (SpecR n K))

/-- Stage `t` of the lifted segment. -/
def liftSpec (t : ℕ) : SpecR n K := fun Q e =>
  if u ∈ e then
    liftRoute u (tw t (e.erase u)) (e.erase u) ((l'.getD t idSpecR) (linkF Q u) (e.erase u))
  else [(e, 1)]

/-- The lifted segment. -/
def liftSeg : List (SpecR n K) := (List.range l'.length).map (liftSpec u tw l')

omit [NeZero K] in
lemma length_liftSeg : (liftSeg u tw l').length = l'.length := by simp [liftSeg]

omit [NeZero K] in
lemma getD_liftSeg {t : ℕ} (ht : t < l'.length) :
    (liftSeg u tw l').getD t idSpecR = liftSpec u tw l' t := by
  unfold liftSeg
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  simp

/-- The hypotheses of a lift along a segment: `u` and the twins avoid the link sets and their
routes, and differ. -/
def LiftHyp (L0 : Finset (Finset (Fin n))) : Prop :=
  ∀ t < l'.length, ∀ f ∈ prunR l' L0 t, LiftOK u (tw t f) f (rtR l' L0 t f)

variable {u tw l'} {P : Finset (Finset (Fin n))}

omit [NeZero K] in
lemma rtR_liftSeg_of_mem {t : ℕ} (ht : t < l'.length) {e : Finset (Fin n)} (hu : u ∈ e) :
    rtR (liftSeg u tw l') P t e =
      liftRoute u (tw t (e.erase u)) (e.erase u)
        ((l'.getD t idSpecR) (linkF (prunR (liftSeg u tw l') P t) u) (e.erase u)) := by
  unfold rtR
  rw [getD_liftSeg u tw l' ht]
  simp [liftSpec, hu]

omit [NeZero K] in
lemma rtR_liftSeg_of_notMem {t : ℕ} (ht : t < l'.length) {e : Finset (Fin n)} (hu : u ∉ e) :
    rtR (liftSeg u tw l') P t e = [(e, 1)] := by
  unfold rtR
  rw [getD_liftSeg u tw l' ht]
  simp [liftSpec, hu]

lemma mem_linkF {Q : Finset (Finset (Fin n))} {f : Finset (Fin n)} :
    f ∈ linkF Q u ↔ u ∉ f ∧ insert u f ∈ Q := by
  unfold linkF
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hu⟩, rfl⟩
    exact ⟨notMem_erase u e, by rwa [insert_erase hu]⟩
  · rintro ⟨hu, hf⟩
    exact ⟨insert u f, ⟨hf, mem_insert_self u f⟩, erase_insert hu⟩

/-- **The link of `u` along the lifted segment is the family of `l'`.** -/
theorem linkF_prunR_liftSeg (hL : LiftHyp u tw l' (linkF P u)) :
    ∀ t ≤ l'.length, linkF (prunR (liftSeg u tw l') P t) u = prunR l' (linkF P u) t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    ext g
    rw [mem_linkF, prunR_succ, prunR_succ]
    simp only [mem_biUnion, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨hug, e, he, p, hp, hpe⟩
      by_cases hue : u ∈ e
      · rw [rtR_liftSeg_of_mem (by omega) hue] at hp
        have hf : e.erase u ∈ prunR l' (linkF P u) t := by
          rw [← ih', mem_linkF, insert_erase hue]; exact ⟨notMem_erase u e, he⟩
        have hok := hL t (by omega) _ hf
        rw [ih'] at hp
        simp only [liftRoute, List.mem_append, List.mem_map, List.mem_singleton] at hp
        rcases hp with (⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩) | rfl
        · refine ⟨e.erase u, hf, p', hp', ?_⟩
          have : insert u p'.1 = insert u g := hpe
          have h1 := congrArg (·.erase u) this
          simp only at h1
          rw [erase_insert (hok.uro p' hp'), erase_insert hug] at h1
          exact h1
        · exfalso
          have : insert (tw t (e.erase u)) p'.1 = insert u g := hpe
          have hm : u ∈ insert (tw t (e.erase u)) p'.1 := this ▸ mem_insert_self u g
          rcases mem_insert.1 hm with h' | h'
          · exact hok.ne h'
          · exact hok.uro p' hp' h'
        · exfalso
          have : insert (tw t (e.erase u)) (e.erase u) = insert u g := hpe
          have hm : u ∈ insert (tw t (e.erase u)) (e.erase u) := this ▸ mem_insert_self u g
          rcases mem_insert.1 hm with h' | h'
          · exact hok.ne h'
          · exact notMem_erase u e h'
      · rw [rtR_liftSeg_of_notMem (by omega) hue] at hp
        simp only [List.mem_singleton] at hp
        subst hp
        have : e = insert u g := hpe
        exact absurd (this ▸ mem_insert_self u g) hue
    · rintro ⟨f, hf, p, hp, rfl⟩
      have hok := hL t (by omega) f hf
      have hfm : f ∈ linkF (prunR (liftSeg u tw l') P t) u := by rw [ih']; exact hf
      obtain ⟨huf, hef⟩ := mem_linkF.1 hfm
      refine ⟨hok.uro p hp, insert u f, hef, (insert u p.1, p.2), ?_, rfl⟩
      rw [rtR_liftSeg_of_mem (by omega) (mem_insert_self u f), erase_insert huf, ih']
      simp only [liftRoute, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨p, hp, rfl⟩)

/-- The route of a set containing `u` in the lifted segment. -/
lemma rtR_liftSeg_link (hL : LiftHyp u tw l' (linkF P u)) {t : ℕ} (ht : t < l'.length)
    {e : Finset (Fin n)} (hu : u ∈ e) :
    rtR (liftSeg u tw l') P t e =
      liftRoute u (tw t (e.erase u)) (e.erase u) (rtR l' (linkF P u) t (e.erase u)) := by
  rw [rtR_liftSeg_of_mem ht hu, linkF_prunR_liftSeg hL t ht.le]
  rfl

variable {q r L : ℕ}

/-- **Lifting a valid segment from the link.** -/
theorem segOKR_liftSeg (hK : ModsOK q r K) (hr : 1 ≤ r) (hP : ∀ e ∈ P, e.card = r)
    (hL : LiftHyp u tw l' (linkF P u)) (hseg : SegOKR (q - 1) (r - 1) L l' (linkF P u)) :
    SegOKR q r (2 * L + 1) (liftSeg u tw l') P := by
  have hcard : ∀ t ≤ l'.length, ∀ e ∈ prunR (liftSeg u tw l') P t, e.card = r := by
    intro t
    induction t with
    | zero => intro _; exact hP
    | succ t ih =>
      intro ht g hg
      rw [prunR_succ] at hg
      obtain ⟨e, he, hge⟩ := mem_biUnion.1 hg
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hge)
      by_cases hue : u ∈ e
      · rw [rtR_liftSeg_link hL (by omega) hue] at hp
        have hf : e.erase u ∈ prunR l' (linkF P u) t := by
          rw [← linkF_prunR_liftSeg hL t (by omega), mem_linkF, insert_erase hue]
          exact ⟨notMem_erase u e, he⟩
        have hec := ih (by omega) e he
        have hfc : (e.erase u).card = r - 1 := by rw [card_erase_of_mem hue, hec]
        have hro := hseg.route t (by omega) _ hf
        have := (routeOKR_liftRoute (A := ∅) hK hr (hL t (by omega) _ hf) hfc
          ⟨hro.1, fun s hs => by simp at hs⟩).1 p
        exact this hp
      · rw [rtR_liftSeg_of_notMem (by omega) hue] at hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ih (by omega) e he
  refine ⟨hP, ?_, ?_⟩
  · intro t ht e he
    rw [length_liftSeg] at ht
    by_cases hue : u ∈ e
    · rw [rtR_liftSeg_link hL ht hue]
      have hf : e.erase u ∈ prunR l' (linkF P u) t := by
        rw [← linkF_prunR_liftSeg hL t ht.le, mem_linkF, insert_erase hue]
        exact ⟨notMem_erase u e, he⟩
      have hfc : (e.erase u).card = r - 1 := by
        rw [card_erase_of_mem hue, hcard t ht.le e he]
      have hro := hseg.route t ht _ hf
      have hsub : allowedR (K := K) q r (prunR (liftSeg u tw l') P t) e ⊆
          allowedR (q - 1) (r - 1) (prunR l' (linkF P u) t) (e.erase u) := by
        have := allowedR_subset_link (K := K) (q := q) (r := r)
          (prunR (liftSeg u tw l') P t) (notMem_erase u e)
        rwa [insert_erase hue, linkF_prunR_liftSeg hL t ht.le] at this
      have := routeOKR_liftRoute hK hr (hL t ht _ hf) hfc (routeOKR_mono hro hsub)
      rwa [insert_erase hue] at this
    · rw [rtR_liftSeg_of_notMem ht hue]
      exact routeOKR_stay (hcard t ht.le e he) _
  · intro t ht e he
    rw [length_liftSeg] at ht
    by_cases hue : u ∈ e
    · rw [rtR_liftSeg_link hL ht hue, length_liftRoute]
      have hf : e.erase u ∈ prunR l' (linkF P u) t := by
        rw [← linkF_prunR_liftSeg hL t ht.le, mem_linkF, insert_erase hue]
        exact ⟨notMem_erase u e, he⟩
      have := hseg.len t ht _ hf
      omega
    · rw [rtR_liftSeg_of_notMem ht hue]; simp

/-- **Loads of the lifted segment.** -/
theorem passR_liftSeg_le (hL : LiftHyp u tw l' (linkF P u)) {t : ℕ} (ht : t < l'.length)
    (S : Finset (Fin n)) :
    passR (liftSeg u tw l') P t S ≤
      ((prunR (liftSeg u tw l') P t).filter (fun e => u ∉ e ∧ S ⊆ e)).card +
      ((prunR l' (linkF P u) t).filter (fun f =>
        S ⊆ insert u (insert (tw t f) (visitR f (rtR l' (linkF P u) t f))))).card := by
  unfold passR
  set Q := prunR (liftSeg u tw l') P t
  have hsplit : Q.filter (fun e => S ⊆ visitR e (rtR (liftSeg u tw l') P t e)) ⊆
      Q.filter (fun e => u ∉ e ∧ S ⊆ e) ∪
      (Q.filter (fun e => u ∈ e ∧ S ⊆ visitR e (rtR (liftSeg u tw l') P t e))) := by
    intro e he
    obtain ⟨he, hS⟩ := mem_filter.1 he
    by_cases hue : u ∈ e
    · exact mem_union_right _ (mem_filter.2 ⟨he, hue, hS⟩)
    · refine mem_union_left _ (mem_filter.2 ⟨he, hue, ?_⟩)
      rw [rtR_liftSeg_of_notMem ht hue, visitR_stay] at hS
      exact hS
  refine (card_le_card hsplit).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  have himg : Q.filter (fun e => u ∈ e ∧ S ⊆ visitR e (rtR (liftSeg u tw l') P t e)) ⊆
      ((prunR l' (linkF P u) t).filter (fun f =>
        S ⊆ insert u (insert (tw t f) (visitR f (rtR l' (linkF P u) t f))))).image (insert u) := by
    intro e he
    obtain ⟨he, hue, hS⟩ := mem_filter.1 he
    have hf : e.erase u ∈ prunR l' (linkF P u) t := by
      rw [← linkF_prunR_liftSeg hL t ht.le, mem_linkF, insert_erase hue]
      exact ⟨notMem_erase u e, he⟩
    refine mem_image.2 ⟨e.erase u, mem_filter.2 ⟨hf, ?_⟩, insert_erase hue⟩
    rw [rtR_liftSeg_link hL ht hue] at hS
    have := visitR_liftRoute (u := u) (tw := tw t (e.erase u)) (f := e.erase u)
      (ro := rtR l' (linkF P u) t (e.erase u))
    rw [insert_erase hue] at this
    exact hS.trans this
  exact (card_le_card himg).trans card_image_le

omit [NeZero K] in
lemma linkF_image_insert (Q : Finset (Finset (Fin n))) :
    (linkF Q u).image (insert u) = Q.filter (u ∈ ·) := by
  ext e
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(mem_linkF.1 hf).2, mem_insert_self u f⟩
  · rintro ⟨he, hu⟩
    exact ⟨e.erase u, mem_linkF.2 ⟨notMem_erase u e, by rwa [insert_erase hu]⟩, insert_erase hu⟩

omit [NeZero K] in
lemma card_linkF (Q : Finset (Finset (Fin n))) : (linkF Q u).card = (Q.filter (u ∈ ·)).card := by
  rw [← linkF_image_insert, card_image_of_injOn]
  intro f hf g hg hfg
  have h1 := congrArg (·.erase u) hfg
  simp only at h1
  rwa [erase_insert (mem_linkF.1 hf).1, erase_insert (mem_linkF.1 hg).1] at h1

/-- **The sets containing `u` at the end of the lifted segment** correspond to the final family of
`l'`. -/
theorem card_filter_mem_prunR_liftSeg (hL : LiftHyp u tw l' (linkF P u)) :
    ((prunR (liftSeg u tw l') P l'.length).filter (u ∈ ·)).card =
      (prunR l' (linkF P u) l'.length).card := by
  rw [← card_linkF, linkF_prunR_liftSeg hL _ le_rfl]

/-! ### Moving a lonely vertex -/

variable (u) in
/-- The stage moving the vertex `u` to `u'` in the sets containing it. -/
noncomputable def moveSpec (u' : Fin n) : SpecR n K := fun _ e =>
  if u ∈ e then boxRoute e (e.erase u) (fun _ => u') else [(e, 1)]

omit [NeZero K] in
lemma sdiff_erase_self {e : Finset (Fin n)} (hu : u ∈ e) : e \ e.erase u = {u} := by
  ext x
  simp only [mem_sdiff, mem_erase, mem_singleton]
  constructor
  · rintro ⟨hx, h⟩; by_contra hxu; exact h ⟨hxu, hx⟩
  · rintro rfl; exact ⟨hu, fun h => h.1 rfl⟩

omit [NeZero K] in
lemma boxOK_move {e : Finset (Fin n)} {u' : Fin n} (hu : u ∈ e) (hu' : u' ∉ e) :
    BoxOK e (e.erase u) (fun _ => u') where
  sub := erase_subset u e
  inj x hx y hy _ := by
    have h1 : x = u := by simp at hx; exact hx.2
    have h2 : y = u := by simp at hy; exact hy.2
    rw [h1, h2]
  out x _ := hu'

omit [NeZero K] in
/-- The sets of the route of a move. -/
lemma mem_boxRoute_move {e : Finset (Fin n)} {u' : Fin n} {p : Finset (Fin n) × ZMod K}
    (hu : u ∈ e) (hp : p ∈ boxRoute (K := K) e (e.erase u) (fun _ => u')) :
    p.1 = insert u' (e.erase u) := by
  obtain ⟨J, hJ, hJe, hpJ⟩ := mem_boxRoute hp
  have hJsub : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
  have hFJ : e.erase u ⊆ J := (mem_filter.1 hJ).2
  have hJ' : J = e.erase u := by
    apply subset_antisymm _ hFJ
    intro x hx
    refine mem_erase.2 ⟨?_, hJsub hx⟩
    rintro rfl
    apply hJe
    apply subset_antisymm hJsub
    intro y hy
    by_cases hyx : y = x
    · rw [hyx]; exact hx
    · exact hFJ (mem_erase.2 ⟨hyx, hy⟩)
  subst hJ'
  rw [hpJ, bt, sdiff_erase_self hu, image_singleton, union_comm]
  rfl

variable {q r : ℕ}

/-- **Moving a lonely vertex is a valid one-stage segment.**  If at most one set of `Q` contains
`u`, and `u' ∉ e` for that set, the stage `moveSpec u u'` is valid; afterwards no set contains
`u`. -/
theorem segOKR_move (hK : ModsOK q r K) {Q : Finset (Finset (Fin n))} {u' : Fin n}
    (hQ : ∀ e ∈ Q, e.card = r) (hlone : (Q.filter (u ∈ ·)).card ≤ 1)
    (hu' : ∀ e ∈ Q, u ∈ e → u' ∉ e) :
    SegOKR q r (2 ^ r) [moveSpec (K := K) u u'] Q := by
  refine ⟨hQ, ?_, ?_⟩
  · intro t ht e he
    simp only [List.length_singleton, Nat.lt_one_iff] at ht
    subst ht
    have hrt : rtR [moveSpec (K := K) u u'] Q 0 e = moveSpec u u' Q e := rfl
    rw [hrt, moveSpec]
    split_ifs with hue
    · refine routeOKR_loneBox hK (hQ e he) (boxOK_move hue (hu' e he hue)) ?_
      rw [sdiff_erase_self hue]
      intro f hf hsub
      have huf : u ∈ f := hsub (mem_singleton_self u)
      exact card_le_one.1 hlone f (mem_filter.2 ⟨hf, huf⟩) e (mem_filter.2 ⟨he, hue⟩)
    · exact routeOKR_stay (hQ e he) _
  · intro t ht e he
    simp only [List.length_singleton, Nat.lt_one_iff] at ht
    subst ht
    have hrt : rtR [moveSpec (K := K) u u'] Q 0 e = moveSpec u u' Q e := rfl
    rw [hrt, moveSpec]
    split_ifs with hue
    · exact (length_boxRoute _ _ _).trans (by rw [hQ e he])
    · simp only [List.length_singleton]; exact Nat.one_le_two_pow

/-- After the move, no set contains `u`. -/
theorem notMem_prunR_move {Q : Finset (Finset (Fin n))} {u' : Fin n} (huu : u' ≠ u) :
    ∀ g ∈ prunR [moveSpec (K := K) u u'] Q 1, u ∉ g := by
  intro g hg
  rw [prunR_succ] at hg
  obtain ⟨e, he, hge⟩ := mem_biUnion.1 hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hge)
  have hrt : rtR [moveSpec (K := K) u u'] Q 0 e = moveSpec u u' Q e := rfl
  rw [hrt, moveSpec] at hp
  split_ifs at hp with hue
  · rw [mem_boxRoute_move hue hp]
    simp only [mem_insert, mem_erase, not_or]
    exact ⟨huu.symm, fun h => h.1 rfl⟩
  · simp only [List.mem_singleton] at hp
    rw [hp]; exact hue

/-- The family after the move. -/
theorem prunR_move {Q : Finset (Finset (Fin n))} {u' : Fin n} :
    prunR [moveSpec (K := K) u u'] Q 1 =
      Q.filter (u ∉ ·) ∪ (Q.filter (u ∈ ·)).image (fun e => insert u' (e.erase u)) := by
  rw [prunR_succ]
  ext g
  simp only [mem_biUnion, List.mem_toFinset, List.mem_map, mem_union, mem_filter, mem_image]
  have hrt : ∀ e, rtR [moveSpec (K := K) u u'] Q 0 e = moveSpec u u' Q e := fun _ => rfl
  constructor
  · rintro ⟨e, he, p, hp, rfl⟩
    rw [hrt, moveSpec] at hp
    split_ifs at hp with hue
    · exact Or.inr ⟨e, ⟨he, hue⟩, (mem_boxRoute_move hue hp).symm⟩
    · simp only [List.mem_singleton] at hp
      rw [hp]; exact Or.inl ⟨he, hue⟩
  · rintro (⟨hg, hug⟩ | ⟨e, ⟨he, hue⟩, rfl⟩)
    · refine ⟨g, hg, (g, 1), ?_, rfl⟩
      rw [hrt, moveSpec, if_neg hug]; simp
    · have hJ : e.erase u ∈ (bJs e (e.erase u)).erase e := by
        refine mem_erase.2 ⟨fun h => notMem_erase u e (h.symm ▸ hue), ?_⟩
        exact mem_filter.2 ⟨mem_powerset.2 (erase_subset u e), subset_rfl⟩
      refine ⟨e, he, (bt e (fun _ => u') (e.erase u), -(-1 : ZMod K) ^ (e \ e.erase u).card), ?_, ?_⟩
      · rw [hrt, moveSpec, if_pos hue]
        unfold boxRoute
        exact List.mem_map.2 ⟨e.erase u, mem_toList.2 hJ, rfl⟩
      · show bt e (fun _ => u') (e.erase u) = insert u' (e.erase u)
        rw [bt, sdiff_erase_self hue, image_singleton, union_comm]
        rfl

end RefinedAbsorption.HyperPlan
