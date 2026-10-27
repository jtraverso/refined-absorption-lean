module
public import RefinedAbsorption.OddGrid.Compose

/-!
# Multi-stage plans of the grid refiner

A *plan* is a list of stage specifications `sp : List (Spec n)`.  At stage `t` the current set of
pairs is `prun sp X t` (starting from the input graph `X`), and every pair `e` is sent along a
*route* `rt sp X t e`: either a signed walk (`Route.walk`) between the ends of `e` with an odd
number of steps, or a *move* (`Route.move`) of a bundle whose weight is `≡ 0 (mod q - 1)` to
another pair.  The inputs of stage `t + 1` are the carries left by stage `t` (`inp`), restricted to
values `≡ 0 (mod q - 1)` on pairs that are moved.

* `outs_inp`: the output pairs of stage `t` are exactly `prun sp X (t + 1)`.
* `plan_stage_ldecomp`: under the validity conditions `PlanOK` every stage is a label-level
  decomposition whose residue lies in the inputs of the next stage.  For moved pairs this uses that
  the pair is the only one at one of its vertices (`Lonely`): the residue is divisible, so the carry
  on such a pair has value `≡ 0 (mod q - 1)`.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

variable {n K : ℕ}

/-- A route of a pair: a signed walk, or a move of a bundle to another pair. -/
inductive Route (n : ℕ) : Type
  | walk (l : List (Fin n))
  | move (f : Finset (Fin n))

/-- The pairs of consecutive vertices of a walk. -/
def wpairs : List (Fin n) → List (Finset (Fin n))
  | p :: q :: rest => {p, q} :: wpairs (q :: rest)
  | _ => []

lemma map_fst_walkL (l : List (Fin n)) (w : ZMod K) : (walkL l w).map Prod.fst = wpairs l := by
  induction l generalizing w with
  | nil => rfl
  | cons p tl ih =>
    cases tl with
    | nil => rfl
    | cons q rest =>
      rw [walkL_cons_cons, List.map_cons, ih, wpairs]

namespace Route

/-- The weighted pairs replacing a label of weight `w`. -/
def rest : Route n → ZMod K → List (Finset (Fin n) × ZMod K)
  | walk l, w => walkL l w
  | move f, w => [(f, w)]

/-- The pairs used by a route. -/
def pairs : Route n → Finset (Finset (Fin n))
  | walk l => (wpairs l).toFinset
  | move f => {f}

/-- The vertices touched by the route of `e`. -/
def visit (e : Finset (Fin n)) : Route n → Finset (Fin n)
  | walk l => l.toFinset
  | move f => e ∪ f

/-- Whether a route is a move. -/
def isMove : Route n → Bool
  | walk _ => false
  | move _ => true

lemma rest_pairs (r : Route n) (w : ZMod K) : ((r.rest w).map Prod.fst).toFinset = r.pairs := by
  cases r with
  | walk l => simp only [rest, pairs, map_fst_walkL]
  | move f => simp [rest, pairs]

end Route

/-- A stage specification: the route of every pair, given the current set of pairs. -/
abbrev Spec (n : ℕ) := Finset (Finset (Fin n)) → Finset (Fin n) → Route n

/-- The default specification (beyond the end of a plan): no rerouting at all. -/
def idSpec : Spec n := fun _ _ => .walk []

variable (sp : List (Spec n)) (X : Finset (Finset (Fin n)))

/-- The pairs present at stage `t`. -/
def prun : ℕ → Finset (Finset (Fin n))
  | 0 => X
  | t + 1 => (prun t).biUnion fun e => ((sp.getD t idSpec) (prun t) e).pairs

/-- The route of the pair `e` at stage `t`. -/
def rt (t : ℕ) (e : Finset (Fin n)) : Route n := (sp.getD t idSpec) (prun sp X t) e

lemma prun_succ (t : ℕ) :
    prun sp X (t + 1) = (prun sp X t).biUnion fun e => (rt sp X t e).pairs := rfl

lemma rt_of_ge {t : ℕ} (ht : sp.length ≤ t) (e : Finset (Fin n)) : rt sp X t e = .walk [] := by
  unfold rt; rw [List.getD_eq_default _ _ ht]; rfl

/-- Pair and weight of an input label. -/
def plab : Lab n K → Finset (Fin n) × ZMod K
  | .x e => (e, 1)
  | .cp _ e _ s => (e, s)
  | _ => (∅, 0)

/-- The rerouting rule of stage `t`. -/
def restFP (t : ℕ) : RestF n K := fun ℓ => (rt sp X t (plab ℓ).1).rest (plab ℓ).2

/-- The weights of all labels of the plan. -/
def pwP : Lab n K → Finset (Fin n) × ZMod K
  | .x e => (e, 1)
  | .anti _ ℓ => ((pwP ℓ).1, -(pwP ℓ).2)
  | .rest t ℓ k => (restFP sp X t ℓ).getD k (∅, 0)
  | .cp _ e _ s => (e, s)
  | .cn _ e _ s => (e, -s)

lemma stagePW (t : ℕ) : StagePW t (restFP sp X t) (pwP (K := K) sp X) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

variable [NeZero K]

/-- The values allowed for the carries on a pair with route `r`. -/
def allowed (q : ℕ) (r : Route n) : Finset (ZMod K) :=
  if r.isMove then univ.filter (fun s => (q - 1) ∣ s.val) else univ

lemma zero_mem_allowed (q : ℕ) (r : Route n) : (0 : ZMod K) ∈ allowed q r := by
  unfold allowed; split_ifs <;> simp

/-- The inputs of stage `t`. -/
def inp (q : ℕ) : ℕ → Finset (Lab n K)
  | 0 => X.image Lab.x
  | t + 1 => (prun sp X (t + 1)).biUnion fun e =>
      (allowed q (rt sp X (t + 1) e)).image
        (Lab.cp t e (slen t (inp q t) (restFP sp X t) e))

variable {sp X}

lemma mem_inp_zero {q : ℕ} {ℓ : Lab n K} : ℓ ∈ inp sp X q 0 ↔ ∃ e ∈ X, ℓ = .x e := by
  simp [inp, eq_comm]

lemma mem_inp_succ {q t : ℕ} {ℓ : Lab n K} :
    ℓ ∈ inp sp X q (t + 1) ↔ ∃ e ∈ prun sp X (t + 1),
      ∃ s ∈ (allowed q (rt sp X (t + 1) e) : Finset (ZMod K)),
      ℓ = .cp t e (slen t (inp sp X (K := K) q t) (restFP sp X t) e) s := by
  simp only [inp, mem_biUnion, mem_image]
  constructor
  · rintro ⟨e, he, s, hs, rfl⟩; exact ⟨e, he, s, hs, rfl⟩
  · rintro ⟨e, he, s, hs, rfl⟩; exact ⟨e, he, s, hs, rfl⟩

/-- Inputs are not labels of their stage. -/
lemma notStage_inp {q t : ℕ} {ℓ : Lab n K} (h : ℓ ∈ inp sp X q t) : NotStage t ℓ := by
  cases t with
  | zero => obtain ⟨e, -, rfl⟩ := mem_inp_zero.1 h; trivial
  | succ t =>
    obtain ⟨e, -, s, -, rfl⟩ := mem_inp_succ.1 h
    show t ≠ t + 1; omega

/-- The pair of an input is a current pair, and its weight is given by `plab`. -/
lemma inp_pair {q t : ℕ} {ℓ : Lab n K} (h : ℓ ∈ inp sp X q t) :
    (plab ℓ).1 ∈ prun sp X t ∧ pwP sp X ℓ = plab ℓ := by
  cases t with
  | zero => obtain ⟨e, he, rfl⟩ := mem_inp_zero.1 h; exact ⟨he, rfl⟩
  | succ t => obtain ⟨e, he, s, -, rfl⟩ := mem_inp_succ.1 h; exact ⟨he, rfl⟩

/-- Every current pair carries an input. -/
lemma exists_inp {q t : ℕ} {e : Finset (Fin n)} (he : e ∈ prun sp X t) :
    ∃ ℓ ∈ inp sp X (K := K) q t, (plab ℓ).1 = e := by
  cases t with
  | zero => exact ⟨.x e, mem_inp_zero.2 ⟨e, he, rfl⟩, rfl⟩
  | succ t => exact ⟨_, mem_inp_succ.2 ⟨e, he, 0, zero_mem_allowed _ _, rfl⟩, rfl⟩

omit [NeZero K] in
lemma rests_image_restPair (t : ℕ) (restF : RestF n K) (ℓ : Lab n K) :
    (rests t restF ℓ).image (restPair restF) = ((restF ℓ).map Prod.fst).toFinset := by
  ext f
  simp only [rests, mem_image, mem_range, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨(restF ℓ).getD k (∅, 0), ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    refine ⟨_, ⟨k, hk, rfl⟩, ?_⟩
    simp only [restPair, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-- **The output pairs of stage `t` are the pairs of stage `t + 1`.** -/
lemma outs_inp (q t : ℕ) :
    outs t (inp sp X (K := K) q t) (restFP sp X t) = prun sp X (t + 1) := by
  ext f
  have key : ∀ ℓ : Lab n K, f ∈ (rests t (restFP sp X t) ℓ).image (restPair (restFP sp X t)) ↔
      f ∈ (rt sp X t (plab ℓ).1).pairs := by
    intro ℓ; rw [rests_image_restPair, restFP, Route.rest_pairs]
  rw [prun_succ, outs, restSet]
  simp only [mem_biUnion]
  have h2 : f ∈ image (restPair (restFP sp X t))
      ((inp sp X (K := K) q t).biUnion (rests t (restFP sp X t)))
      ↔ ∃ ℓ ∈ inp sp X (K := K) q t, f ∈ (rt sp X t (plab ℓ).1).pairs := by
    simp only [← key, mem_image, mem_biUnion]
    constructor
    · rintro ⟨r, ⟨ℓ, hℓ, hr⟩, rfl⟩; exact ⟨ℓ, hℓ, r, hr, rfl⟩
    · rintro ⟨ℓ, hℓ, r, hr, rfl⟩; exact ⟨r, ⟨ℓ, hℓ, hr⟩, rfl⟩
  rw [h2]
  constructor
  · rintro ⟨ℓ, hℓ, hf⟩
    exact ⟨_, (inp_pair hℓ).1, hf⟩
  · rintro ⟨e, he, hf⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := exists_inp (K := K) (q := q) he
    exact ⟨ℓ, hℓ, hf⟩

end RefinedAbsorption.OddGrid
