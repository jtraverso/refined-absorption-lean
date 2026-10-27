module
public import RequestProject.HyperPlan.Empty

/-!
# Emptying many vertices at once

Every stage of a plan loads all the current sets (a set that stays where it is still counts in
`passR`), so the vertices have to be emptied *in parallel*: a plan with `O(log n)` stages is needed.
This file runs the construction of `HyperPlan.Empty` simultaneously for all the vertices of a set
`U`, provided no current set contains two vertices of `U`.

Every `u ∈ U` comes with its own link segment `l' u` (all of length `T`) and its own twins
`tw u t f`.  A set meeting `U` in the vertex `u` is sent along the lifted route of the route of
`e \ {u}` in `l' u`; the other sets stay.

* `liftSegU_inv`: at every stage, every set meets `U` in at most one vertex, and the link of every
  `u ∈ U` is the family of `l' u`.
* `segOKR_liftSegU`: if every `l' u` is a valid segment for `(q - 1, r - 1)`, the lifted segment is
  valid for `(q, r)`.
* `passR_liftSegU_le`: loads.
* `card_filter_mem_prunR_liftSegU`: at the end, the number of sets containing `u` is the size of the
  final family of `l' u`.
* `segOKR_moveU`, `prunR_moveU_disjoint`: once every vertex of `U` is lonely, one stage moves every
  `u ∈ U` to `μ u`; afterwards no set meets `U`.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ} [NeZero K]

/-- `e` meets `U` in at most one vertex. -/
def MeetsOne (U e : Finset (Fin n)) : Prop := e ∩ U = ∅ ∨ ∃ u, e ∩ U = {u}

/-- The vertex of `U` in `e`, if any. -/
noncomputable def selU (U e : Finset (Fin n)) : Option (Fin n) :=
  if h : (e ∩ U).Nonempty then some ((e ∩ U).min' h) else none

lemma selU_of_eq_singleton {U e : Finset (Fin n)} {u : Fin n} (h : e ∩ U = {u}) :
    selU U e = some u := by
  have hne : (e ∩ U).Nonempty := by rw [h]; exact singleton_nonempty u
  unfold selU
  rw [dif_pos hne]
  congr 1
  have hx : ∀ x ∈ e ∩ U, x = u := fun x hx => by rw [h] at hx; exact mem_singleton.1 hx
  exact hx _ (min'_mem _ _)

lemma selU_of_eq_empty {U e : Finset (Fin n)} (h : e ∩ U = ∅) : selU U e = none := by
  unfold selU
  rw [dif_neg (by rw [h]; exact not_nonempty_empty)]

lemma inter_eq_singleton_of {U e : Finset (Fin n)} {u : Fin n} (he : MeetsOne U e) (hu : u ∈ U)
    (hue : u ∈ e) : e ∩ U = {u} := by
  rcases he with h | ⟨v, hv⟩
  · exact absurd (h ▸ mem_inter.2 ⟨hue, hu⟩) (notMem_empty u)
  · have : u ∈ e ∩ U := mem_inter.2 ⟨hue, hu⟩
    rw [hv, mem_singleton] at this
    rw [hv, this]

lemma insert_inter_singleton {U s : Finset (Fin n)} {u : Fin n} (hu : u ∈ U) (hs : Disjoint s U) :
    insert u s ∩ U = {u} := by
  rw [insert_inter_of_mem hu, disjoint_iff_inter_eq_empty.1 hs, insert_empty]

lemma insert_inter_empty {U s : Finset (Fin n)} {a : Fin n} (ha : a ∉ U) (hs : Disjoint s U) :
    insert a s ∩ U = ∅ := by
  rw [insert_inter_of_notMem ha, disjoint_iff_inter_eq_empty.1 hs]

lemma erase_disjoint {U e : Finset (Fin n)} {u : Fin n} (h : e ∩ U = {u}) :
    Disjoint (e.erase u) U := by
  rw [disjoint_left]
  intro x hx hxU
  have : x ∈ e ∩ U := mem_inter.2 ⟨(mem_erase.1 hx).2, hxU⟩
  rw [h, mem_singleton] at this
  exact (mem_erase.1 hx).1 this

variable (U : Finset (Fin n)) (tw : Fin n → ℕ → Finset (Fin n) → Fin n)
  (l' : Fin n → List (SpecR n K)) (T : ℕ)

/-- Stage `t` of the parallel lifted segment. -/
noncomputable def liftSpecU (t : ℕ) : SpecR n K := fun Q e =>
  match selU U e with
  | some u => liftRoute u (tw u t (e.erase u)) (e.erase u)
      (((l' u).getD t idSpecR) (linkF Q u) (e.erase u))
  | none => [(e, 1)]

/-- The parallel lifted segment. -/
noncomputable def liftSegU : List (SpecR n K) := (List.range T).map (liftSpecU U tw l')

omit [NeZero K] in
lemma length_liftSegU : (liftSegU U tw l' T).length = T := by simp [liftSegU]

omit [NeZero K] in
lemma getD_liftSegU {t : ℕ} (ht : t < T) :
    (liftSegU U tw l' T).getD t idSpecR = liftSpecU U tw l' t := by
  unfold liftSegU
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  simp

/-- The hypotheses of a parallel lift. -/
structure LiftHypU (P : Finset (Finset (Fin n))) : Prop where
  one : ∀ e ∈ P, MeetsOne U e
  len : ∀ u ∈ U, (l' u).length = T
  ok : ∀ u ∈ U, ∀ t < T, ∀ f ∈ prunR (l' u) (linkF P u) t,
    LiftOK u (tw u t f) f (rtR (l' u) (linkF P u) t f)
  twU : ∀ u ∈ U, ∀ t < T, ∀ f ∈ prunR (l' u) (linkF P u) t, tw u t f ∉ U
  roU : ∀ u ∈ U, ∀ t < T, ∀ f ∈ prunR (l' u) (linkF P u) t,
    ∀ p ∈ rtR (l' u) (linkF P u) t f, Disjoint p.1 U

variable {U tw l' T} {P : Finset (Finset (Fin n))}

omit [NeZero K] in
lemma rtR_liftSegU_of_eq {t : ℕ} (ht : t < T) {e : Finset (Fin n)} {u : Fin n}
    (h : e ∩ U = {u}) :
    rtR (liftSegU U tw l' T) P t e =
      liftRoute u (tw u t (e.erase u)) (e.erase u)
        (((l' u).getD t idSpecR) (linkF (prunR (liftSegU U tw l' T) P t) u) (e.erase u)) := by
  unfold rtR
  rw [getD_liftSegU U tw l' T ht]
  simp only [liftSpecU, selU_of_eq_singleton h]

omit [NeZero K] in
lemma rtR_liftSegU_of_empty {t : ℕ} (ht : t < T) {e : Finset (Fin n)} (h : e ∩ U = ∅) :
    rtR (liftSegU U tw l' T) P t e = [(e, 1)] := by
  unfold rtR
  rw [getD_liftSegU U tw l' T ht]
  simp only [liftSpecU, selU_of_eq_empty h]

/-- The link families of `l' u` consist of sets disjoint from `U`. -/
lemma link_disjoint (hL : LiftHypU U tw l' T P) {u : Fin n} (hu : u ∈ U) :
    ∀ t ≤ T, ∀ f ∈ prunR (l' u) (linkF P u) t, Disjoint f U := by
  intro t
  induction t with
  | zero =>
    intro _ f hf
    obtain ⟨huf, hfP⟩ := mem_linkF.1 hf
    have := inter_eq_singleton_of (hL.one _ hfP) hu (mem_insert_self u f)
    have h2 := erase_disjoint this
    rwa [erase_insert huf] at h2
  | succ t ih =>
    intro ht g hg
    rw [prunR_succ] at hg
    obtain ⟨f, hf, hgf⟩ := mem_biUnion.1 hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hgf)
    exact hL.roU u hu t (by omega) f hf p hp

/-- **The invariant of the parallel lift.** -/
theorem liftSegU_inv (hL : LiftHypU U tw l' T P) :
    ∀ t ≤ T, (∀ e ∈ prunR (liftSegU U tw l' T) P t, MeetsOne U e) ∧
      ∀ u ∈ U, linkF (prunR (liftSegU U tw l' T) P t) u = prunR (l' u) (linkF P u) t := by
  intro t
  induction t with
  | zero => intro _; exact ⟨hL.one, fun _ _ => rfl⟩
  | succ t ih =>
    intro ht
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    -- the link set of `e` and its route
    have hlink : ∀ e ∈ prunR (liftSegU U tw l' T) P t, ∀ u, e ∩ U = {u} →
        u ∈ U ∧ e.erase u ∈ prunR (l' u) (linkF P u) t ∧
        rtR (liftSegU U tw l' T) P t e = liftRoute u (tw u t (e.erase u)) (e.erase u)
          (rtR (l' u) (linkF P u) t (e.erase u)) := by
      intro e he u hu
      have huU : u ∈ U := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
      have hue : u ∈ e := (mem_inter.1 (hu ▸ mem_singleton_self u)).1
      refine ⟨huU, ?_, ?_⟩
      · rw [← ih2 u huU, mem_linkF, insert_erase hue]; exact ⟨notMem_erase u e, he⟩
      · rw [rtR_liftSegU_of_eq (by omega) hu, ih2 u huU]; rfl
    -- the sets of stage `t + 1`
    have hsets : ∀ g ∈ prunR (liftSegU U tw l' T) P (t + 1),
        (∃ e ∈ prunR (liftSegU U tw l' T) P t, e ∩ U = ∅ ∧ g = e) ∨
        (∃ e ∈ prunR (liftSegU U tw l' T) P t, ∃ u, e ∩ U = {u} ∧
          ∃ p ∈ rtR (l' u) (linkF P u) t (e.erase u), g = insert u p.1) ∨
        g ∩ U = ∅ := by
      intro g hg
      rw [prunR_succ] at hg
      obtain ⟨e, he, hge⟩ := mem_biUnion.1 hg
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hge)
      rcases ih1 e he with h0 | ⟨u, hu⟩
      · rw [rtR_liftSegU_of_empty (by omega) h0] at hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact Or.inl ⟨e, he, h0, rfl⟩
      · obtain ⟨huU, hf, hrt⟩ := hlink e he u hu
        rw [hrt] at hp
        simp only [liftRoute, List.mem_append, List.mem_map, List.mem_singleton] at hp
        rcases hp with (⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩) | rfl
        · exact Or.inr (Or.inl ⟨e, he, u, hu, p', hp', rfl⟩)
        · exact Or.inr (Or.inr (insert_inter_empty (hL.twU u huU t (by omega) _ hf)
            (hL.roU u huU t (by omega) _ hf p' hp')))
        · exact Or.inr (Or.inr (insert_inter_empty (hL.twU u huU t (by omega) _ hf)
            (erase_disjoint hu)))
    refine ⟨?_, ?_⟩
    · intro g hg
      rcases hsets g hg with ⟨e, he, h0, rfl⟩ | ⟨e, he, u, hu, p, hp, rfl⟩ | h0
      · exact Or.inl h0
      · obtain ⟨huU, hf, -⟩ := hlink e he u hu
        exact Or.inr ⟨u, insert_inter_singleton huU (hL.roU u huU t (by omega) _ hf p hp)⟩
      · exact Or.inl h0
    · intro u huU
      ext g
      rw [mem_linkF]
      constructor
      · rintro ⟨hug, hg⟩
        rcases hsets _ hg with ⟨e, he, h0, rfl⟩ | ⟨e, he, v, hv, p, hp, hgp⟩ | h0
        · exact absurd (h0 ▸ mem_inter.2 ⟨mem_insert_self u g, huU⟩) (notMem_empty u)
        · obtain ⟨hvU, hf, -⟩ := hlink e he v hv
          have hpU := hL.roU v hvU t (by omega) _ hf p hp
          have huv : u = v := by
            have : u ∈ insert v p.1 := hgp ▸ mem_insert_self u g
            rcases mem_insert.1 this with h | h
            · exact h
            · exact absurd huU (disjoint_left.1 hpU h)
          subst huv
          have hgp' : g = p.1 := by
            have h1 := congrArg (·.erase u) hgp
            simp only at h1
            rwa [erase_insert hug, erase_insert (fun h => disjoint_left.1 hpU h huU)] at h1
          rw [prunR_succ, hgp']
          exact mem_biUnion.2 ⟨_, hf, List.mem_toFinset.2 (List.mem_map_of_mem hp)⟩
        · exact absurd (h0 ▸ mem_inter.2 ⟨mem_insert_self u g, huU⟩) (notMem_empty u)
      · intro hg
        rw [prunR_succ] at hg
        obtain ⟨f, hf, hgf⟩ := mem_biUnion.1 hg
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hgf)
        have hok := hL.ok u huU t (by omega) f hf
        have hfm : f ∈ linkF (prunR (liftSegU U tw l' T) P t) u := by rw [ih2 u huU]; exact hf
        obtain ⟨huf, hef⟩ := mem_linkF.1 hfm
        have hfd := link_disjoint hL huU t (by omega) f hf
        have hint : insert u f ∩ U = {u} := insert_inter_singleton huU hfd
        refine ⟨hok.uro p hp, ?_⟩
        rw [prunR_succ]
        refine mem_biUnion.2 ⟨insert u f, hef, List.mem_toFinset.2 (List.mem_map.2
          ⟨(insert u p.1, p.2), ?_, rfl⟩)⟩
        rw [(hlink _ hef u hint).2.2, erase_insert huf]
        simp only [liftRoute, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨p, hp, rfl⟩)

variable {q r L : ℕ}

/-- **The parallel lift of valid link segments is a valid segment.** -/
theorem segOKR_liftSegU (hK : ModsOK q r K) (hr : 1 ≤ r) (hP : ∀ e ∈ P, e.card = r)
    (hL : LiftHypU U tw l' T P)
    (hseg : ∀ u ∈ U, SegOKR (q - 1) (r - 1) L (l' u) (linkF P u)) :
    SegOKR q r (2 * L + 1) (liftSegU U tw l' T) P := by
  have key : ∀ t < T, ∀ e ∈ prunR (liftSegU U tw l' T) P t, (e.card = r →
      RouteOKR q r e (rtR (liftSegU U tw l' T) P t e)
        (allowedR q r (prunR (liftSegU U tw l' T) P t) e) ∧
      (rtR (liftSegU U tw l' T) P t e).length ≤ 2 * L + 1) := by
    intro t ht e he hec
    obtain ⟨hone, hlk⟩ := liftSegU_inv hL t ht.le
    rcases hone e he with h0 | ⟨u, hu⟩
    · rw [rtR_liftSegU_of_empty ht h0]
      exact ⟨routeOKR_stay hec _, by simp⟩
    · have huU : u ∈ U := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
      have hue : u ∈ e := (mem_inter.1 (hu ▸ mem_singleton_self u)).1
      have hf : e.erase u ∈ prunR (l' u) (linkF P u) t := by
        rw [← hlk u huU, mem_linkF, insert_erase hue]; exact ⟨notMem_erase u e, he⟩
      have hlen := hL.len u huU
      have hrt : rtR (liftSegU U tw l' T) P t e = liftRoute u (tw u t (e.erase u)) (e.erase u)
          (rtR (l' u) (linkF P u) t (e.erase u)) := by
        rw [rtR_liftSegU_of_eq ht hu, hlk u huU]; rfl
      rw [hrt]
      have hfc : (e.erase u).card = r - 1 := by rw [card_erase_of_mem hue, hec]
      have hro := (hseg u huU).route t (by omega) _ hf
      have hsub : allowedR (K := K) q r (prunR (liftSegU U tw l' T) P t) e ⊆
          allowedR (q - 1) (r - 1) (prunR (l' u) (linkF P u) t) (e.erase u) := by
        have := allowedR_subset_link (K := K) (q := q) (r := r)
          (prunR (liftSegU U tw l' T) P t) (notMem_erase u e)
        rwa [insert_erase hue, hlk u huU] at this
      have h1 := routeOKR_liftRoute hK hr (hL.ok u huU t ht _ hf) hfc (routeOKR_mono hro hsub)
      rw [insert_erase hue] at h1
      refine ⟨h1, ?_⟩
      rw [length_liftRoute]
      have := (hseg u huU).len t (by omega) _ hf
      omega
  have hcard : ∀ t ≤ T, ∀ e ∈ prunR (liftSegU U tw l' T) P t, e.card = r := by
    intro t
    induction t with
    | zero => intro _; exact hP
    | succ t ih =>
      intro ht g hg
      rw [prunR_succ] at hg
      obtain ⟨e, he, hge⟩ := mem_biUnion.1 hg
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hge)
      exact (key t (by omega) e he (ih (by omega) e he)).1.1 p hp
  refine ⟨hP, fun t ht e he => ?_, fun t ht e he => ?_⟩
  · rw [length_liftSegU] at ht
    exact (key t ht e he (hcard t ht.le e he)).1
  · rw [length_liftSegU] at ht
    exact (key t ht e he (hcard t ht.le e he)).2

/-- **Loads of the parallel lift.** -/
theorem passR_liftSegU_le (hL : LiftHypU U tw l' T P) {t : ℕ} (ht : t < T) (S : Finset (Fin n)) :
    passR (liftSegU U tw l' T) P t S ≤
      ((prunR (liftSegU U tw l' T) P t).filter (fun e => e ∩ U = ∅ ∧ S ⊆ e)).card +
      ∑ u ∈ U, ((prunR (l' u) (linkF P u) t).filter (fun f =>
        S ⊆ insert u (insert (tw u t f) (visitR f (rtR (l' u) (linkF P u) t f))))).card := by
  obtain ⟨hone, hlk⟩ := liftSegU_inv hL t ht.le
  unfold passR
  set Q := prunR (liftSegU U tw l' T) P t
  have hsplit : Q.filter (fun e => S ⊆ visitR e (rtR (liftSegU U tw l' T) P t e)) ⊆
      Q.filter (fun e => e ∩ U = ∅ ∧ S ⊆ e) ∪ U.biUnion (fun u =>
        Q.filter (fun e => e ∩ U = {u} ∧ S ⊆ visitR e (rtR (liftSegU U tw l' T) P t e))) := by
    intro e he
    obtain ⟨he, hS⟩ := mem_filter.1 he
    rcases hone e he with h0 | ⟨u, hu⟩
    · refine mem_union_left _ (mem_filter.2 ⟨he, h0, ?_⟩)
      rw [rtR_liftSegU_of_empty ht h0, visitR_stay] at hS
      exact hS
    · have huU : u ∈ U := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
      exact mem_union_right _ (mem_biUnion.2 ⟨u, huU, mem_filter.2 ⟨he, hu, hS⟩⟩)
  refine (card_le_card hsplit).trans ((card_union_le _ _).trans (Nat.add_le_add_left
    (card_biUnion_le.trans (sum_le_sum fun u huU => ?_)) _))
  have himg : Q.filter (fun e => e ∩ U = {u} ∧ S ⊆ visitR e (rtR (liftSegU U tw l' T) P t e)) ⊆
      ((prunR (l' u) (linkF P u) t).filter (fun f =>
        S ⊆ insert u (insert (tw u t f) (visitR f (rtR (l' u) (linkF P u) t f))))).image
        (insert u) := by
    intro e he
    obtain ⟨he, hu, hS⟩ := mem_filter.1 he
    have hue : u ∈ e := (mem_inter.1 (hu ▸ mem_singleton_self u)).1
    have hf : e.erase u ∈ prunR (l' u) (linkF P u) t := by
      rw [← hlk u huU, mem_linkF, insert_erase hue]; exact ⟨notMem_erase u e, he⟩
    refine mem_image.2 ⟨e.erase u, mem_filter.2 ⟨hf, ?_⟩, insert_erase hue⟩
    rw [rtR_liftSegU_of_eq ht hu, hlk u huU] at hS
    have := visitR_liftRoute (u := u) (tw := tw u t (e.erase u)) (f := e.erase u)
      (ro := rtR (l' u) (linkF P u) t (e.erase u))
    rw [insert_erase hue] at this
    exact hS.trans this
  exact (card_le_card himg).trans card_image_le

/-- **At the end of the parallel lift**, the sets containing `u ∈ U` correspond to the final family
of `l' u`. -/
theorem card_filter_mem_prunR_liftSegU (hL : LiftHypU U tw l' T P) {u : Fin n} (hu : u ∈ U) :
    ((prunR (liftSegU U tw l' T) P T).filter (u ∈ ·)).card = (prunR (l' u) (linkF P u) T).card := by
  rw [← card_linkF, (liftSegU_inv hL T le_rfl).2 u hu]

lemma meetsOne_prunR_liftSegU (hL : LiftHypU U tw l' T P) :
    ∀ e ∈ prunR (liftSegU U tw l' T) P T, MeetsOne U e :=
  (liftSegU_inv hL T le_rfl).1

/-! ### Moving many lonely vertices -/

variable (U) in
/-- The stage moving every `u ∈ U` to `μ u` in the set containing it. -/
noncomputable def moveSpecU (μ : Fin n → Fin n) : SpecR n K := fun _ e =>
  match selU U e with
  | some u => boxRoute e (e.erase u) (fun _ => μ u)
  | none => [(e, 1)]

/-- **Moving many lonely vertices is a valid one-stage segment.** -/
theorem segOKR_moveU (hK : ModsOK q r K) {Q : Finset (Finset (Fin n))} {μ : Fin n → Fin n}
    (hQ : ∀ e ∈ Q, e.card = r) (hone : ∀ e ∈ Q, MeetsOne U e)
    (hlone : ∀ u ∈ U, (Q.filter (u ∈ ·)).card ≤ 1)
    (hμ : ∀ u ∈ U, ∀ e ∈ Q, u ∈ e → μ u ∉ e) :
    SegOKR q r (2 ^ r) [moveSpecU (K := K) U μ] Q := by
  have hrt : ∀ e, rtR [moveSpecU (K := K) U μ] Q 0 e = moveSpecU U μ Q e := fun _ => rfl
  refine ⟨hQ, ?_, ?_⟩
  · intro t ht e he
    simp only [List.length_singleton, Nat.lt_one_iff] at ht
    subst ht
    rw [hrt, moveSpecU]
    rcases hone e he with h0 | ⟨u, hu⟩
    · rw [selU_of_eq_empty h0]; exact routeOKR_stay (hQ e he) _
    · rw [selU_of_eq_singleton hu]
      have huU : u ∈ U := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
      have hue : u ∈ e := (mem_inter.1 (hu ▸ mem_singleton_self u)).1
      refine routeOKR_loneBox hK (hQ e he) (boxOK_move hue (hμ u huU e he hue)) ?_
      rw [sdiff_erase_self hue]
      intro f hf hsub
      have huf : u ∈ f := hsub (mem_singleton_self u)
      exact card_le_one.1 (hlone u huU) f (mem_filter.2 ⟨hf, huf⟩) e (mem_filter.2 ⟨he, hue⟩)
  · intro t ht e he
    simp only [List.length_singleton, Nat.lt_one_iff] at ht
    subst ht
    rw [hrt, moveSpecU]
    rcases hone e he with h0 | ⟨u, hu⟩
    · rw [selU_of_eq_empty h0]; simp only [List.length_singleton]; exact Nat.one_le_two_pow
    · rw [selU_of_eq_singleton hu]
      exact (length_boxRoute _ _ _).trans (by rw [hQ e he])

/-- **After moving the lonely vertices of `U` outside `U`, no set meets `U`.** -/
theorem prunR_moveU_disjoint {Q : Finset (Finset (Fin n))} {μ : Fin n → Fin n}
    (hone : ∀ e ∈ Q, MeetsOne U e) (hμU : ∀ u ∈ U, μ u ∉ U) :
    ∀ g ∈ prunR [moveSpecU (K := K) U μ] Q 1, Disjoint g U := by
  have hrt : ∀ e, rtR [moveSpecU (K := K) U μ] Q 0 e = moveSpecU U μ Q e := fun _ => rfl
  intro g hg
  rw [prunR_succ] at hg
  obtain ⟨e, he, hge⟩ := mem_biUnion.1 hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hge)
  rw [hrt, moveSpecU] at hp
  rcases hone e he with h0 | ⟨u, hu⟩
  · rw [selU_of_eq_empty h0] at hp
    simp only [List.mem_singleton] at hp
    rw [hp]
    exact disjoint_iff_inter_eq_empty.2 h0
  · rw [selU_of_eq_singleton hu] at hp
    have huU : u ∈ U := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
    have hue : u ∈ e := (mem_inter.1 (hu ▸ mem_singleton_self u)).1
    rw [mem_boxRoute_move hue hp]
    exact disjoint_iff_inter_eq_empty.2 (insert_inter_empty (hμU u huU) (erase_disjoint hu))

/-- The family after moving the lonely vertices of `U`. -/
theorem prunR_moveU {Q : Finset (Finset (Fin n))} {μ : Fin n → Fin n}
    (hone : ∀ e ∈ Q, MeetsOne U e) :
    prunR [moveSpecU (K := K) U μ] Q 1 =
      Q.filter (fun e => e ∩ U = ∅) ∪
        U.biUnion (fun u => (Q.filter (u ∈ ·)).image (fun e => insert (μ u) (e.erase u))) := by
  have hrt : ∀ e, rtR [moveSpecU (K := K) U μ] Q 0 e = moveSpecU U μ Q e := fun _ => rfl
  rw [prunR_succ]
  ext g
  simp only [mem_biUnion, List.mem_toFinset, List.mem_map, mem_union, mem_filter, mem_image]
  constructor
  · rintro ⟨e, he, p, hp, rfl⟩
    rw [hrt, moveSpecU] at hp
    rcases hone e he with h0 | ⟨u, hu⟩
    · rw [selU_of_eq_empty h0] at hp
      simp only [List.mem_singleton] at hp
      rw [hp]; exact Or.inl ⟨he, h0⟩
    · rw [selU_of_eq_singleton hu] at hp
      have huU : u ∈ U := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
      have hue : u ∈ e := (mem_inter.1 (hu ▸ mem_singleton_self u)).1
      exact Or.inr ⟨u, huU, e, ⟨he, hue⟩, (mem_boxRoute_move hue hp).symm⟩
  · rintro (⟨hg, h0⟩ | ⟨u, huU, e, ⟨he, hue⟩, rfl⟩)
    · refine ⟨g, hg, (g, 1), ?_, rfl⟩
      rw [hrt, moveSpecU, selU_of_eq_empty h0]; simp
    · have hu := inter_eq_singleton_of (hone e he) huU hue
      have hJ : e.erase u ∈ (bJs e (e.erase u)).erase e := by
        refine mem_erase.2 ⟨fun h => notMem_erase u e (h.symm ▸ hue), ?_⟩
        exact mem_filter.2 ⟨mem_powerset.2 (erase_subset u e), subset_rfl⟩
      refine ⟨e, he, (bt e (fun _ => μ u) (e.erase u),
        -(-1 : ZMod K) ^ (e \ e.erase u).card), ?_, ?_⟩
      · rw [hrt, moveSpecU, selU_of_eq_singleton hu]
        unfold boxRoute
        exact List.mem_map.2 ⟨e.erase u, mem_toList.2 hJ, rfl⟩
      · show bt e (fun _ => μ u) (e.erase u) = insert (μ u) (e.erase u)
        rw [bt, sdiff_erase_self hue, image_singleton, union_comm]
        rfl

end RefinedAbsorption.HyperPlan
