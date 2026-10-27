module
public import RequestProject.HyperPlan.Stage
public import RequestProject.OddGrid.PlanDecomp

/-!
# Multi-stage plans, uniformity `r`

A *plan* is a list of stage specifications `sp : List (SpecR n K)`.  At stage `t` the current
family of `r`-sets is `prunR sp X t` (starting from the input `X`), and every current set `e` is
sent along a *signed route* `rtR sp X t e`: a list of `r`-sets with coefficients in `ZMod K`.  A
label of weight `w` on `e` is replaced by the same sets with the coefficients multiplied by `w`.

The inputs of stage `t + 1` are the carries left by stage `t`, restricted to the values allowed by
*loneliness* (`allowedR`): if `S ⊆ e` (`|S| < r`) lies in no other current set, a divisible
residue has a value on `e` divisible by `binom(q - |S|, r - |S|)`.

A route is valid (`RouteOKR`) if its sets are `r`-sets and its defect (`defect`) times every
allowed value is divisible at every face.  For the input stage the only weight is `1`.

* `plan_stage_ldecompR`: every stage of a valid plan is a label-level decomposition whose residue
  lies in the inputs of the next stage.
* `plan_ldecompR`: the whole plan, followed by the *base* pieces (all divisible sets of final
  carries), is a decomposition with empty residue.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ} [NeZero K]

/-- A stage specification: the signed route of every set, given the current family. -/
abbrev SpecR (n K : ℕ) :=
  Finset (Finset (Fin n)) → Finset (Fin n) → List (Finset (Fin n) × ZMod K)

/-- The default specification (beyond the end of a plan): every set stays where it is. -/
def idSpecR : SpecR n K := fun _ e => [(e, 1)]

variable (sp : List (SpecR n K)) (X : Finset (Finset (Fin n)))

/-- The family of sets present at stage `t`. -/
def prunR : ℕ → Finset (Finset (Fin n))
  | 0 => X
  | t + 1 => (prunR t).biUnion fun e => (((sp.getD t idSpecR) (prunR t) e).map Prod.fst).toFinset

/-- The signed route of the set `e` at stage `t`. -/
def rtR (t : ℕ) (e : Finset (Fin n)) : List (Finset (Fin n) × ZMod K) :=
  (sp.getD t idSpecR) (prunR sp X t) e

lemma prunR_succ (t : ℕ) :
    prunR sp X (t + 1) = (prunR sp X t).biUnion fun e => ((rtR sp X t e).map Prod.fst).toFinset :=
  rfl

/-- The rerouting rule of stage `t`. -/
def restFR (t : ℕ) : RestF n K := fun ℓ => wroute (rtR sp X t (plab ℓ).1) (plab ℓ).2

/-- The weights of all labels of the plan. -/
def pwR : Lab n K → Finset (Fin n) × ZMod K
  | .x e => (e, 1)
  | .anti _ ℓ => ((pwR ℓ).1, -(pwR ℓ).2)
  | .rest t ℓ k => (restFR sp X t ℓ).getD k (∅, 0)
  | .cp _ e _ s => (e, s)
  | .cn _ e _ s => (e, -s)

lemma stagePWR (t : ℕ) : StagePW t (restFR sp X t) (pwR (K := K) sp X) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- `S` lies in no set of `P` other than `e`. -/
def LoneIn (P : Finset (Finset (Fin n))) (e S : Finset (Fin n)) : Prop := ∀ f ∈ P, S ⊆ f → f = e

instance (P : Finset (Finset (Fin n))) (e S : Finset (Fin n)) : Decidable (LoneIn P e S) := by
  unfold LoneIn; infer_instance

/-- The values allowed for the carry on `e` by loneliness in the family `P`. -/
def allowedR (q r : ℕ) (P : Finset (Finset (Fin n))) (e : Finset (Fin n)) : Finset (ZMod K) :=
  univ.filter fun s => ∀ S ∈ e.powerset, S.card < r → LoneIn P e S →
    (q - S.card).choose (r - S.card) ∣ s.val

lemma zero_mem_allowedR (q r : ℕ) (P : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    (0 : ZMod K) ∈ allowedR q r P e := by
  simp [allowedR]

/-- The inputs of stage `t`. -/
def inpR (q r : ℕ) : ℕ → Finset (Lab n K)
  | 0 => X.image Lab.x
  | t + 1 => (prunR sp X (t + 1)).biUnion fun e =>
      (allowedR q r (prunR sp X (t + 1)) e).image
        (Lab.cp t e (slen t (inpR q r t) (restFR sp X t) e))

variable {sp X}

lemma mem_inpR_zero {q r : ℕ} {ℓ : Lab n K} : ℓ ∈ inpR sp X q r 0 ↔ ∃ e ∈ X, ℓ = .x e := by
  simp [inpR, eq_comm]

lemma mem_inpR_succ {q r t : ℕ} {ℓ : Lab n K} :
    ℓ ∈ inpR sp X q r (t + 1) ↔ ∃ e ∈ prunR sp X (t + 1),
      ∃ s ∈ (allowedR q r (prunR sp X (t + 1)) e : Finset (ZMod K)),
      ℓ = .cp t e (slen t (inpR sp X (K := K) q r t) (restFR sp X t) e) s := by
  simp only [inpR, mem_biUnion, mem_image]
  constructor
  · rintro ⟨e, he, s, hs, rfl⟩; exact ⟨e, he, s, hs, rfl⟩
  · rintro ⟨e, he, s, hs, rfl⟩; exact ⟨e, he, s, hs, rfl⟩

lemma notStage_inpR {q r t : ℕ} {ℓ : Lab n K} (h : ℓ ∈ inpR sp X q r t) : NotStage t ℓ := by
  cases t with
  | zero => obtain ⟨e, -, rfl⟩ := mem_inpR_zero.1 h; trivial
  | succ t =>
    obtain ⟨e, -, s, -, rfl⟩ := mem_inpR_succ.1 h
    show t ≠ t + 1; omega

lemma inpR_pair {q r t : ℕ} {ℓ : Lab n K} (h : ℓ ∈ inpR sp X q r t) :
    (plab ℓ).1 ∈ prunR sp X t ∧ pwR sp X ℓ = plab ℓ := by
  cases t with
  | zero => obtain ⟨e, he, rfl⟩ := mem_inpR_zero.1 h; exact ⟨he, rfl⟩
  | succ t => obtain ⟨e, he, s, -, rfl⟩ := mem_inpR_succ.1 h; exact ⟨he, rfl⟩

lemma exists_inpR {q r t : ℕ} {e : Finset (Fin n)} (he : e ∈ prunR sp X t) :
    ∃ ℓ ∈ inpR sp X (K := K) q r t, (plab ℓ).1 = e := by
  cases t with
  | zero => exact ⟨.x e, mem_inpR_zero.2 ⟨e, he, rfl⟩, rfl⟩
  | succ t => exact ⟨_, mem_inpR_succ.2 ⟨e, he, 0, zero_mem_allowedR _ _ _ _, rfl⟩, rfl⟩

lemma rests_image_restPairR (t : ℕ) (restF : RestF n K) (ℓ : Lab n K) :
    (rests t restF ℓ).image (restPair restF) = ((restF ℓ).map Prod.fst).toFinset :=
  OddGrid.rests_image_restPair t restF ℓ

lemma map_fst_wroute (ro : List (Finset (Fin n) × ZMod K)) (w : ZMod K) :
    (wroute ro w).map Prod.fst = ro.map Prod.fst := by
  simp [wroute, List.map_map, Function.comp_def]

/-- **The output sets of stage `t` are the sets of stage `t + 1`.** -/
lemma outs_inpR (q r t : ℕ) :
    outs t (inpR sp X (K := K) q r t) (restFR sp X t) = prunR sp X (t + 1) := by
  ext f
  have key : ∀ ℓ : Lab n K, f ∈ (rests t (restFR sp X t) ℓ).image (restPair (restFR sp X t)) ↔
      f ∈ ((rtR sp X t (plab ℓ).1).map Prod.fst).toFinset := by
    intro ℓ; rw [rests_image_restPairR, restFR, map_fst_wroute]
  rw [prunR_succ, outs, restSet]
  simp only [mem_biUnion]
  have h2 : f ∈ image (restPair (restFR sp X t))
      ((inpR sp X (K := K) q r t).biUnion (rests t (restFR sp X t)))
      ↔ ∃ ℓ ∈ inpR sp X (K := K) q r t, f ∈ ((rtR sp X t (plab ℓ).1).map Prod.fst).toFinset := by
    simp only [← key, mem_image, mem_biUnion]
    constructor
    · rintro ⟨r, ⟨ℓ, hℓ, hr⟩, rfl⟩; exact ⟨ℓ, hℓ, r, hr, rfl⟩
    · rintro ⟨ℓ, hℓ, r, hr, rfl⟩; exact ⟨r, ⟨ℓ, hℓ, hr⟩, rfl⟩
  rw [h2]
  constructor
  · rintro ⟨ℓ, hℓ, hf⟩
    exact ⟨_, (inpR_pair hℓ).1, hf⟩
  · rintro ⟨e, he, hf⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := exists_inpR (K := K) (q := q) (r := r) he
    exact ⟨ℓ, hℓ, hf⟩

/-! ### Validity -/

/-- Validity of a signed route of `e` for the weights in `A`. -/
def RouteOKR (q r : ℕ) (e : Finset (Fin n)) (ro : List (Finset (Fin n) × ZMod K))
    (A : Finset (ZMod K)) : Prop :=
  (∀ p ∈ ro, p.1.card = r) ∧ ∀ s ∈ A, ∀ S : Finset (Fin n), S.card < r →
    (q - S.card).choose (r - S.card) ∣ (defect ro e S * s).val

/-- The weights that can occur at stage `t` on the set `e`. -/
def wts (q r : ℕ) (sp : List (SpecR n K)) (X : Finset (Finset (Fin n))) (t : ℕ)
    (e : Finset (Fin n)) : Finset (ZMod K) :=
  if t = 0 then {1} else allowedR q r (prunR sp X t) e

/-- Validity of a plan (with routes of length at most `L`). -/
structure PlanOKR (q r L : ℕ) (sp : List (SpecR n K)) (X : Finset (Finset (Fin n))) : Prop where
  rg : ∀ e ∈ X, e.card = r
  route : ∀ t < sp.length, ∀ e ∈ prunR sp X t, RouteOKR q r e (rtR sp X t e) (wts q r sp X t e)
  len : ∀ t < sp.length, ∀ e ∈ prunR sp X t, (rtR sp X t e).length ≤ L

variable {q r L : ℕ} (hK : ModsOK q r K)

lemma wt_mem_wts {t : ℕ} {ℓ : Lab n K} (hℓ : ℓ ∈ inpR sp X (K := K) q r t) :
    (plab ℓ).2 ∈ wts q r sp X t (plab ℓ).1 := by
  cases t with
  | zero =>
    obtain ⟨e, -, rfl⟩ := mem_inpR_zero.1 hℓ
    simp [wts, plab]
  | succ t =>
    obtain ⟨e, -, s, hs, rfl⟩ := mem_inpR_succ.1 hℓ
    simpa [wts, plab] using hs

include hK in
/-- The switch piece `P0` of an input of a valid plan is divisible. -/
lemma plan_P0R (hok : PlanOKR q r L sp X) {t : ℕ} (ht : t < sp.length) {ℓ : Lab n K}
    (hℓ : ℓ ∈ inpR sp X (K := K) q r t) :
    LDivR q r (pwR (K := K) sp X) (P0 t (restFR sp X t) ℓ) := by
  obtain ⟨he, hpw⟩ := inpR_pair hℓ
  have hok' := (hok.route t ht _ he).2 _ (wt_mem_wts hℓ)
  refine ldivR_P0 hK (stagePWR sp X t) (ro := rtR sp X t (plab ℓ).1) ?_ ?_
  · rw [hpw]; rfl
  · rw [hpw]; exact hok'

include hK in
/-- The residue of a stage of a valid plan lies in the inputs of the next stage. -/
lemma plan_stResR (hok : PlanOKR q r L sp X) {t : ℕ} (ht : t < sp.length)
    (Ls : Finset (Lab n K)) (hLs : Ls ⊆ inpR sp X (K := K) q r t)
    (hdiv : LDivR q r (pwR (K := K) sp X) Ls) :
    stRes t (inpR sp X q r t) (restFR sp X t) Ls ⊆ inpR sp X q r (t + 1) := by
  intro x hx
  have hI : ∀ ℓ ∈ inpR sp X (K := K) q r t, NotStage t ℓ := fun _ h => notStage_inpR h
  have hP0 : ∀ ℓ ∈ inpR sp X (K := K) q r t, LDivR q r (pwR (K := K) sp X)
      (P0 t (restFR sp X t) ℓ) := fun _ h => plan_P0R hK hok ht h
  have hRes := ldivR_stRes hK (stagePWR sp X t) hI hP0 hLs hdiv
  simp only [stRes, mem_image] at hx
  obtain ⟨e, he, rfl⟩ := hx
  have he' : e ∈ prunR sp X (t + 1) := by rw [← outs_inpR (K := K) q r t]; exact he
  refine mem_inpR_succ.2 ⟨e, he', _, ?_, rfl⟩
  simp only [allowedR, mem_filter, mem_univ, true_and, mem_powerset]
  intro S hSe hS hlone
  have h1 := (ldivR_iff hK _).1 hRes S hS
  have hcl : fcl (pwR sp X) (stRes t (inpR sp X q r t) (restFR sp X t) Ls) S =
      sig t (inpR sp X q r t) (restFR sp X t) e Ls := by
    rw [fcl, stRes, sum_image (by intro a _ b _ h; simp only [Lab.cp.injEq] at h; exact h.2.1)]
    rw [sum_eq_single e]
    · simp [pwR, hSe]
    · intro e' he'' hne
      simp only [pwR]
      by_cases hS' : S ⊆ e'
      · exact False.elim (hne (hlone e' (by rw [← outs_inpR (K := K) q r t]; exact he'') hS'))
      · simp [hS']
    · intro h; exact absurd he h
  rwa [hcl] at h1

include hK in
/-- **Every stage of a valid plan is a label-level decomposition.** -/
theorem plan_stage_ldecompR (hok : PlanOKR q r L sp X) {t : ℕ} (ht : t < sp.length) :
    LDecomp (LDivR q r (pwR (K := K) sp X)) (inpR sp X q r t)
      (stR t (inpR sp X q r t) (restFR sp X t)) (inpR sp X q r (t + 1))
      (stW t (inpR sp X q r t) (restFR sp X t)) :=
  stage_ldecompR hK (stagePWR sp X t) (fun _ h => notStage_inpR h)
    (fun _ h => plan_P0R hK hok ht h) _ (plan_stResR hK hok ht)

/-! ### Composition of the stages -/

lemma stIdx_inpR_zero {x : Lab n K} (hx : x ∈ inpR sp X (K := K) q r 0) : stIdx x = none := by
  obtain ⟨e, -, rfl⟩ := mem_inpR_zero.1 hx; rfl

/-- The inputs of stage `t + 1` are labels of stage `t`. -/
lemma inpR_succ_subset_stR (t : ℕ) :
    inpR sp X q r (t + 1) ⊆ stR t (inpR sp X (K := K) q r t) (restFR sp X t) := by
  intro x hx
  obtain ⟨e, he, s, -, rfl⟩ := mem_inpR_succ.1 hx
  rw [← outs_inpR (K := K) q r t] at he
  refine mem_union_right _ (mem_biUnion.2 ⟨e, he, ?_⟩)
  simp only [OddGrid.chR, mem_union, mem_image, mem_product, mem_Icc, mem_univ, and_true]
  exact Or.inl (Or.inr ⟨(_, _), ⟨slen_pos he, le_rfl⟩, rfl⟩)

variable (sp X) in
/-- The labels of the first `T` stages. -/
def RallR (q r T : ℕ) : Finset (Lab n K) :=
  (range T).biUnion fun i => stR i (inpR sp X q r i) (restFR sp X i)

variable (sp X) in
/-- The pieces of the first `T` stages. -/
noncomputable def WallR (q r T : ℕ) : Finset (Finset (Lab n K)) :=
  (range T).biUnion fun i => stW i (inpR sp X q r i) (restFR sp X i)

lemma stIdx_RallR {T : ℕ} {x : Lab n K} (hx : x ∈ RallR (K := K) sp X q r T) :
    ∃ i < T, stIdx x = some i := by
  obtain ⟨i, hi, hx⟩ := mem_biUnion.1 hx
  exact ⟨i, mem_range.1 hi, stIdx_of_stR hx⟩

lemma inpR_subset_RallR {i T : ℕ} (hi : i ≤ T) :
    inpR sp X (K := K) q r i ⊆ inpR sp X q r 0 ∪ RallR sp X q r T := by
  cases i with
  | zero => exact subset_union_left
  | succ j =>
    intro x hx
    exact mem_union_right _ (mem_biUnion.2 ⟨j, mem_range.2 (by omega), inpR_succ_subset_stR j hx⟩)

lemma WallR_subset {T : ℕ} {W : Finset (Lab n K)} (hW : W ∈ WallR (K := K) sp X q r T) :
    W ⊆ inpR sp X q r 0 ∪ RallR sp X q r T := by
  obtain ⟨i, hi, hW⟩ := mem_biUnion.1 hW
  intro x hx
  rcases mem_union.1 (stW_subset hW hx) with h | h
  · exact inpR_subset_RallR (i := i) (by have := mem_range.1 hi; omega) h
  · exact mem_union_right _ (mem_biUnion.2 ⟨i, hi, h⟩)

include hK in
/-- **Composition of the first `T` stages.** -/
theorem plan_ldecomp_uptoR (hok : PlanOKR q r L sp X) {T : ℕ} (hT : T ≤ sp.length) :
    LDecomp (LDivR q r (pwR (K := K) sp X)) (inpR sp X q r 0) (RallR sp X q r T)
      (inpR sp X q r T) (WallR sp X q r T) := by
  induction T with
  | zero =>
    simpa [RallR, WallR] using LDecomp.refl (LDivR q r (pwR (K := K) sp X)) (inpR sp X q r 0)
  | succ T ih =>
    have h := (ih (by omega)).trans (plan_stage_ldecompR hK hok (t := T) (by omega))
      (fun W hW => WallR_subset hW) ?_
    · have hR : RallR (K := K) sp X q r (T + 1) =
          RallR sp X q r T ∪ stR T (inpR sp X q r T) (restFR sp X T) := by
        simp [RallR, range_add_one, biUnion_insert, union_comm]
      have hW : WallR (K := K) sp X q r (T + 1) =
          WallR sp X q r T ∪ stW T (inpR sp X q r T) (restFR sp X T) := by
        simp [WallR, range_add_one, biUnion_insert, union_comm]
      rw [hR, hW]; exact h
    · rw [disjoint_left]
      intro x hx hx'
      have h1 := stIdx_of_stR hx
      rcases mem_union.1 hx' with h | h
      · rw [stIdx_inpR_zero h] at h1; exact absurd h1 (by simp)
      · obtain ⟨i, hi, h2⟩ := stIdx_RallR h
        rw [h1] at h2; simp only [Option.some.injEq] at h2; omega

variable (sp X) in
open Classical in
/-- The base pieces: all divisible sets of final carries. -/
noncomputable def WbaseR (q r : ℕ) : Finset (Finset (Lab n K)) :=
  (inpR sp X q r sp.length).powerset.filter (fun S => LDivR q r (pwR sp X) S)

include hK in
/-- **A valid plan with its base pieces is a decomposition with empty residue.** -/
theorem plan_ldecompR (hok : PlanOKR q r L sp X) :
    LDecomp (LDivR q r (pwR (K := K) sp X)) (inpR sp X q r 0) (RallR sp X q r sp.length) ∅
      (WallR sp X q r sp.length ∪ WbaseR sp X q r) := by
  have hb : LDecomp (LDivR q r (pwR (K := K) sp X)) (inpR sp X q r sp.length) ∅ ∅
      (WbaseR sp X q r) := by
    intro L hL hdiv
    refine ⟨{L}, ?_, ∅, subset_refl _, ldivR_empty, ?_, ?_, ?_⟩
    · simp [WbaseR, hL, hdiv]
    · simp
    · simp
    · simp
  have h := (plan_ldecomp_uptoR hK hok le_rfl).trans hb (fun W hW => WallR_subset hW)
    (disjoint_empty_left _)
  rwa [union_empty] at h

end RefinedAbsorption.HyperPlan
