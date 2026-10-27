module
public import RequestProject.OddGrid.Plan

/-!
# Valid plans are label-level decompositions

`PlanOK sp X`: the input graph is a `2`-graph, every route of a present pair is valid
(`RouteOK`: a signed walk with `1` or `3` steps between the ends of the pair, or a move to a
`2`-set), and moved pairs occur only after the first stage and are `Lonely` (the only present pair
at one of their vertices).

* `plan_stage_ldecomp`: every stage of a valid plan is an `LDecomp` whose residue lies in the
  inputs of the next stage.
* `plan_ldecomp`: the whole plan, followed by the *base* pieces (all divisible sets of final
  carries), is an `LDecomp` with empty residue.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner

variable {n K : ℕ}

/-- `e` is the only pair of `P` at one of its vertices. -/
def Lonely (P : Finset (Finset (Fin n))) (e : Finset (Fin n)) : Prop :=
  ∃ u ∈ e, ∀ e' ∈ P, u ∈ e' → e' = e

/-- Validity of the route of the pair `e`. -/
def RouteOK (e : Finset (Fin n)) : Route n → Prop
  | .walk l => ∃ p tl, l = p :: tl ∧ (p :: tl).IsChain (· ≠ ·) ∧ ¬ Even tl.length ∧
      tl.length ≤ 3 ∧ e = {p, (p :: tl).getLast (List.cons_ne_nil _ _)} ∧
      p ≠ (p :: tl).getLast (List.cons_ne_nil _ _)
  | .move f => f.card = 2

/-- Validity of a plan. -/
structure PlanOK (sp : List (Spec n)) (X : Finset (Finset (Fin n))) : Prop where
  rg : ∀ e ∈ X, e.card = 2
  route : ∀ t < sp.length, ∀ e ∈ prun sp X t, RouteOK e (rt sp X t e)
  move : ∀ t < sp.length, ∀ e ∈ prun sp X t, (rt sp X t e).isMove = true →
    1 ≤ t ∧ Lonely (prun sp X t) e

variable [NeZero K] {q : ℕ} (hd : q - 1 ∣ K) (hN : q.choose 2 ∣ K)
  {sp : List (Spec n)} {X : Finset (Finset (Fin n))}

include hd in
lemma castHom_eq_zero_iff (s : ZMod K) :
    ZMod.castHom hd (ZMod (q - 1)) s = 0 ↔ (q - 1) ∣ s.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

include hd hN in
/-- The switch piece `P0` of an input of a valid plan is divisible. -/
lemma plan_P0 (hok : PlanOK sp X) {t : ℕ} (ht : t < sp.length) {ℓ : Lab n K}
    (hℓ : ℓ ∈ inp sp X (K := K) q t) : LDiv q (pwP (K := K) sp X) (P0 t (restFP sp X t) ℓ) := by
  obtain ⟨he, hpw⟩ := inp_pair hℓ
  have hok' := hok.route t ht _ he
  have hmv := hok.move t ht _ he
  cases hr : rt sp X t (plab ℓ).1 with
  | walk l =>
    rw [hr] at hok'
    obtain ⟨p, tl, rfl, hch, hodd, -, hpr, hne⟩ := hok'
    exact ldiv_P0_walk hd hN (stagePW sp X t) (by rw [restFP, hr, Route.rest, hpw]) hch hodd
      (by rw [hpw]; exact hpr) hne
  | move f =>
    rw [hr] at hmv
    obtain ⟨h1, -⟩ := hmv rfl
    apply ldiv_P0_count hd hN (stagePW sp X t) (f := f) (by rw [restFP, hr, Route.rest, hpw])
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨e, -, s, hs, rfl⟩ := mem_inp_succ.1 hℓ
    rw [castHom_eq_zero_iff hd]
    simp only [plab] at hr
    simp only [allowed, hr, Route.isMove, if_true, mem_filter] at hs
    exact hs.2

include hd hN in
/-- The residue of a stage of a valid plan lies in the inputs of the next stage. -/
lemma plan_stRes (hok : PlanOK sp X) {t : ℕ} (ht : t < sp.length) (Ls : Finset (Lab n K))
    (hLs : Ls ⊆ inp sp X (K := K) q t) (hdiv : LDiv q (pwP (K := K) sp X) Ls) :
    stRes t (inp sp X q t) (restFP sp X t) Ls ⊆ inp sp X q (t + 1) := by
  intro x hx
  simp only [stRes, mem_image] at hx
  obtain ⟨e, he, rfl⟩ := hx
  have he' : e ∈ prun sp X (t + 1) := by rw [← outs_inp (K := K) q t]; exact he
  refine mem_inp_succ.2 ⟨e, he', _, ?_, rfl⟩
  unfold allowed
  split_ifs with hmv
  · have ht1 : t + 1 < sp.length := by
      by_contra h
      rw [rt_of_ge sp X (by omega)] at hmv
      exact absurd hmv (by simp [Route.isMove])
    obtain ⟨-, u, hu, hlon⟩ := hok.move (t + 1) ht1 e he' hmv
    have hI : ∀ ℓ ∈ inp sp X (K := K) q t, NotStage t ℓ := fun _ h => notStage_inp h
    have hP0 : ∀ ℓ ∈ inp sp X (K := K) q t, LDiv q (pwP (K := K) sp X)
        (P0 t (restFP sp X t) ℓ) := fun _ h => plan_P0 hd hN hok ht h
    obtain ⟨hsub, hpd, hdj, heq⟩ := stage_decomp (restF := restFP sp X t) hI Ls hLs
    have hRes : LDiv q (pwP sp X) (stRes t (inp sp X q t) (restFP sp X t) Ls) :=
      ldiv_of_partition (ldiv_union (disjoint_stR hI hLs)
        (ldiv_stR hd hN (stagePW sp X t) hI hP0) hdiv) hpd
        (fun P hP => ldiv_stW hd hN (stagePW sp X t) hP0 (hsub hP)) hdj heq
    have hc := cls_cast_of_ldiv hd hRes u
    have hcls : cls (pwP sp X) (stRes t (inp sp X q t) (restFP sp X t) Ls) u =
        sig t (inp sp X q t) (restFP sp X t) e Ls := by
      rw [cls, stRes, sum_image (by intro a _ b _ h; simp only [Lab.cp.injEq] at h; exact h.2.1)]
      rw [sum_eq_single e]
      · simp [pwP, hu]
      · intro e' he'' hne
        simp only [pwP]
        by_cases hu' : u ∈ e'
        · exact False.elim (hne (hlon e' (by rw [← outs_inp (K := K) q t]; exact he'') hu'))
        · simp [hu']
      · intro h; exact absurd he h
    rw [hcls, castHom_eq_zero_iff hd] at hc
    simp [hc]
  · exact mem_univ _

include hd hN in
/-- **Every stage of a valid plan is a label-level decomposition.** -/
theorem plan_stage_ldecomp (hok : PlanOK sp X) {t : ℕ} (ht : t < sp.length) :
    LDecomp (LDiv q (pwP (K := K) sp X)) (inp sp X q t) (stR t (inp sp X q t) (restFP sp X t))
      (inp sp X q (t + 1)) (stW t (inp sp X q t) (restFP sp X t)) :=
  stage_ldecomp hd hN (stagePW sp X t) (fun _ h => notStage_inp h)
    (fun _ h => plan_P0 hd hN hok ht h) _ (plan_stRes hd hN hok ht)

/-! ### Composition of the stages -/

/-- The stage of a label (`none` for the input labels). -/
def stIdx : Lab n K → Option ℕ
  | .x _ => none
  | .anti t _ => some t
  | .rest t _ _ => some t
  | .cp t _ _ _ => some t
  | .cn t _ _ _ => some t

omit [NeZero K] in
lemma stIdx_of_stR {t : ℕ} {I : Finset (Lab n K)} {restF : RestF n K} [NeZero K] {x : Lab n K}
    (hx : x ∈ stR t I restF) : stIdx x = some t := by
  rcases stR_stage hx with ⟨ℓ, rfl⟩ | ⟨ℓ, k, rfl⟩ | ⟨e, k, s, rfl⟩ | ⟨e, k, s, rfl⟩ <;> rfl

lemma stIdx_inp_zero {x : Lab n K} (hx : x ∈ inp sp X (K := K) q 0) : stIdx x = none := by
  obtain ⟨e, -, rfl⟩ := mem_inp_zero.1 hx; rfl

/-- Positivity of chain lengths on output pairs. -/
lemma slen_pos {t : ℕ} {I : Finset (Lab n K)} {restF : RestF n K} {e : Finset (Fin n)}
    (he : e ∈ outs t I restF) : 0 < slen t I restF e := by
  obtain ⟨r, hr, rfl⟩ := mem_image.1 he
  exact card_pos.2 ⟨r, mem_onPair.2 ⟨hr, rfl⟩⟩

/-- The inputs of stage `t + 1` are labels of stage `t`. -/
lemma inp_succ_subset_stR (t : ℕ) :
    inp sp X q (t + 1) ⊆ stR t (inp sp X (K := K) q t) (restFP sp X t) := by
  intro x hx
  obtain ⟨e, he, s, -, rfl⟩ := mem_inp_succ.1 hx
  rw [← outs_inp (K := K) q t] at he
  refine mem_union_right _ (mem_biUnion.2 ⟨e, he, ?_⟩)
  simp only [chR, mem_union, mem_image, mem_product, mem_Icc, mem_univ, and_true]
  exact Or.inl (Or.inr ⟨(_, _), ⟨slen_pos he, le_rfl⟩, rfl⟩)

/-- The labels of the first `T` stages. -/
def Rall (sp : List (Spec n)) (X : Finset (Finset (Fin n))) (q T : ℕ) : Finset (Lab n K) :=
  (range T).biUnion fun i => stR i (inp sp X q i) (restFP sp X i)

/-- The pieces of the first `T` stages. -/
noncomputable def Wall (sp : List (Spec n)) (X : Finset (Finset (Fin n))) (q T : ℕ) :
    Finset (Finset (Lab n K)) :=
  (range T).biUnion fun i => stW i (inp sp X q i) (restFP sp X i)

lemma stIdx_Rall {T : ℕ} {x : Lab n K} (hx : x ∈ Rall (K := K) sp X q T) : ∃ i < T, stIdx x = some i := by
  obtain ⟨i, hi, hx⟩ := mem_biUnion.1 hx
  exact ⟨i, mem_range.1 hi, stIdx_of_stR hx⟩

lemma inp_subset_Rall {i T : ℕ} (hi : i ≤ T) :
    inp sp X (K := K) q i ⊆ inp sp X q 0 ∪ Rall sp X q T := by
  cases i with
  | zero => exact subset_union_left
  | succ j =>
    intro x hx
    exact mem_union_right _ (mem_biUnion.2 ⟨j, mem_range.2 (by omega), inp_succ_subset_stR j hx⟩)

lemma Wall_subset {T : ℕ} {W : Finset (Lab n K)} (hW : W ∈ Wall (K := K) sp X q T) :
    W ⊆ inp sp X q 0 ∪ Rall sp X q T := by
  obtain ⟨i, hi, hW⟩ := mem_biUnion.1 hW
  intro x hx
  rcases mem_union.1 (stW_subset hW hx) with h | h
  · exact inp_subset_Rall (i := i) (by have := mem_range.1 hi; omega) h
  · exact mem_union_right _ (mem_biUnion.2 ⟨i, hi, h⟩)

include hd hN in
/-- **Composition of the first `T` stages.** -/
theorem plan_ldecomp_upto (hok : PlanOK sp X) {T : ℕ} (hT : T ≤ sp.length) :
    LDecomp (LDiv q (pwP (K := K) sp X)) (inp sp X q 0) (Rall sp X q T) (inp sp X q T)
      (Wall sp X q T) := by
  induction T with
  | zero => simpa [Rall, Wall] using LDecomp.refl (LDiv q (pwP (K := K) sp X)) (inp sp X q 0)
  | succ T ih =>
    have h := (ih (by omega)).trans (plan_stage_ldecomp hd hN hok (t := T) (by omega))
      (fun W hW => Wall_subset hW) ?_
    · have hR : Rall (K := K) sp X q (T + 1) =
          Rall sp X q T ∪ stR T (inp sp X q T) (restFP sp X T) := by
        simp [Rall, range_add_one, biUnion_insert, union_comm]
      have hW : Wall (K := K) sp X q (T + 1) =
          Wall sp X q T ∪ stW T (inp sp X q T) (restFP sp X T) := by
        simp [Wall, range_add_one, biUnion_insert, union_comm]
      rw [hR, hW]; exact h
    · rw [disjoint_left]
      intro x hx hx'
      have h1 := stIdx_of_stR hx
      rcases mem_union.1 hx' with h | h
      · rw [stIdx_inp_zero h] at h1; exact absurd h1 (by simp)
      · obtain ⟨i, hi, h2⟩ := stIdx_Rall h
        rw [h1] at h2; simp only [Option.some.injEq] at h2; omega

open Classical in
/-- The base pieces: all divisible sets of final carries. -/
noncomputable def Wbase (sp : List (Spec n)) (X : Finset (Finset (Fin n))) (q : ℕ) :
    Finset (Finset (Lab n K)) :=
  (inp sp X q sp.length).powerset.filter (fun S => LDiv q (pwP sp X) S)

include hd hN in
/-- **A valid plan with its base pieces is a decomposition with empty residue.** -/
theorem plan_ldecomp (hok : PlanOK sp X) :
    LDecomp (LDiv q (pwP (K := K) sp X)) (inp sp X q 0) (Rall sp X q sp.length) ∅
      (Wall sp X q sp.length ∪ Wbase sp X q) := by
  have hb : LDecomp (LDiv q (pwP (K := K) sp X)) (inp sp X q sp.length) ∅ ∅ (Wbase sp X q) := by
    intro L hL hdiv
    refine ⟨{L}, ?_, ∅, subset_refl _, ldiv_empty, ?_, ?_, ?_⟩
    · simp [Wbase, hL, hdiv]
    · simp
    · simp
    · simp
  have h := (plan_ldecomp_upto hd hN hok le_rfl).trans hb (fun W hW => Wall_subset hW)
    (disjoint_empty_left _)
  rwa [union_empty] at h

end RefinedAbsorption.OddGrid
