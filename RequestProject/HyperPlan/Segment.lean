module
public import RequestProject.HyperPlan.Moves

/-!
# Segments of `r`-uniform plans

A plan is usually built from several *segments* run one after the other.  A segment is a list of
stages run from an arbitrary family `P`; its validity (`SegOKR`) asks every route to be valid for
the values allowed by loneliness (`allowedR`) at every stage, including the first one.

* `prunR_append_le`, `prunR_append_add`, `rtR_append_lt`, `rtR_append_add`: running `l₁ ++ l₂` is
  running `l₁`, then `l₂` on the result.
* `SegOKR.append`: valid segments concatenate.
* `planOKR_of_segOKR`: a valid segment preceded by one stage that keeps everything is a valid plan
  (`PlanOKR`).
* `passSumR_append`, `passSumR_cons_id`: the loads of concatenated segments add up.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ} [NeZero K]

lemma prunR_append_le (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n))) :
    ∀ t ≤ l₁.length, prunR (l₁ ++ l₂) P t = prunR l₁ P t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [prunR_succ, prunR_succ]
    simp only [rtR, ih (by omega), List.getD_append _ _ _ _ (by omega : t < l₁.length)]

lemma rtR_append_lt (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n))) {t : ℕ}
    (ht : t < l₁.length) (e : Finset (Fin n)) : rtR (l₁ ++ l₂) P t e = rtR l₁ P t e := by
  simp only [rtR, prunR_append_le l₁ l₂ P t ht.le]
  rw [List.getD_append _ _ _ _ ht]

lemma prunR_append_add (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n))) :
    ∀ t, prunR (l₁ ++ l₂) P (l₁.length + t) = prunR l₂ (prunR l₁ P l₁.length) t := by
  intro t
  induction t with
  | zero => simpa using prunR_append_le l₁ l₂ P l₁.length le_rfl
  | succ t ih =>
    rw [← Nat.add_assoc, prunR_succ, prunR_succ]
    simp only [rtR, ih, List.getD_append_right _ _ _ _ (by omega : l₁.length ≤ l₁.length + t),
      Nat.add_sub_cancel_left]

lemma rtR_append_add (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n))) (t : ℕ)
    (e : Finset (Fin n)) :
    rtR (l₁ ++ l₂) P (l₁.length + t) e = rtR l₂ (prunR l₁ P l₁.length) t e := by
  simp only [rtR, prunR_append_add]
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

lemma prunR_append_length (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n))) :
    prunR (l₁ ++ l₂) P (l₁ ++ l₂).length = prunR l₂ (prunR l₁ P l₁.length) l₂.length := by
  rw [List.length_append, prunR_append_add]

/-- Validity of a segment: routes of length at most `L`, valid for the allowed values. -/
structure SegOKR (q r L : ℕ) (l : List (SpecR n K)) (P : Finset (Finset (Fin n))) : Prop where
  rg : ∀ e ∈ P, e.card = r
  route : ∀ t < l.length, ∀ e ∈ prunR l P t,
    RouteOKR q r e (rtR l P t e) (allowedR q r (prunR l P t) e)
  len : ∀ t < l.length, ∀ e ∈ prunR l P t, (rtR l P t e).length ≤ L

variable {q r L : ℕ}

/-- The sets of a valid segment are `r`-sets at every stage. -/
lemma SegOKR.card_prunR {l : List (SpecR n K)} {P : Finset (Finset (Fin n))} (h : SegOKR q r L l P) :
    ∀ t ≤ l.length, ∀ e ∈ prunR l P t, e.card = r := by
  intro t
  induction t with
  | zero => intro _; exact h.rg
  | succ t ih =>
    intro ht f hf
    rw [prunR_succ] at hf
    obtain ⟨e, he, hfe⟩ := mem_biUnion.1 hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hfe)
    exact (h.route t (by omega) e he).1 p hp

lemma SegOKR.nil (P : Finset (Finset (Fin n))) (hP : ∀ e ∈ P, e.card = r) :
    SegOKR (K := K) q r L [] P :=
  ⟨hP, fun t ht => by simp at ht, fun t ht => by simp at ht⟩

lemma SegOKR.append {l₁ l₂ : List (SpecR n K)} {P : Finset (Finset (Fin n))}
    (h₁ : SegOKR q r L l₁ P) (h₂ : SegOKR q r L l₂ (prunR l₁ P l₁.length)) :
    SegOKR q r L (l₁ ++ l₂) P := by
  refine ⟨h₁.rg, ?_, ?_⟩
  · intro t ht e he
    by_cases h : t < l₁.length
    · rw [prunR_append_le l₁ l₂ P t h.le] at he ⊢
      rw [rtR_append_lt l₁ l₂ P h]
      exact h₁.route t h e he
    · obtain ⟨s, rfl⟩ : ∃ s, t = l₁.length + s := ⟨t - l₁.length, by omega⟩
      rw [prunR_append_add] at he ⊢
      rw [rtR_append_add]
      rw [List.length_append] at ht
      exact h₂.route s (by omega) e he
  · intro t ht e he
    by_cases h : t < l₁.length
    · rw [prunR_append_le l₁ l₂ P t h.le] at he
      rw [rtR_append_lt l₁ l₂ P h]
      exact h₁.len t h e he
    · obtain ⟨s, rfl⟩ : ∃ s, t = l₁.length + s := ⟨t - l₁.length, by omega⟩
      rw [prunR_append_add] at he
      rw [rtR_append_add]
      rw [List.length_append] at ht
      exact h₂.len s (by omega) e he

/-- The plan `[keep everything] ++ l`. -/
def withStay (l : List (SpecR n K)) : List (SpecR n K) := idSpecR :: l

lemma prunR_withStay_one (l : List (SpecR n K)) (X : Finset (Finset (Fin n))) :
    prunR (withStay l) X 1 = X := by
  rw [prunR_succ]
  ext f
  simp only [mem_biUnion, rtR, withStay, List.getD_cons_zero, idSpecR, List.map_cons,
    List.map_nil, List.toFinset_cons, List.toFinset_nil, insert_empty, mem_singleton]
  constructor
  · rintro ⟨e, he, rfl⟩; exact he
  · intro hf; exact ⟨f, hf, rfl⟩

lemma withStay_eq_append (l : List (SpecR n K)) : withStay l = [idSpecR] ++ l := rfl

lemma prunR_withStay_succ (l : List (SpecR n K)) (X : Finset (Finset (Fin n))) (t : ℕ) :
    prunR (withStay l) X (t + 1) = prunR l X t := by
  have := prunR_append_add [idSpecR] l X t
  rw [← withStay_eq_append] at this
  simp only [List.length_singleton] at this
  rw [Nat.add_comm, this]
  congr 1
  have h1 := prunR_withStay_one l X
  rw [withStay_eq_append, prunR_append_le _ _ X 1 (by simp)] at h1
  exact h1

lemma rtR_withStay_succ (l : List (SpecR n K)) (X : Finset (Finset (Fin n))) (t : ℕ)
    (e : Finset (Fin n)) : rtR (withStay l) X (t + 1) e = rtR l X t e := by
  have := rtR_append_add [idSpecR] l X t e
  rw [← withStay_eq_append] at this
  simp only [List.length_singleton] at this
  rw [Nat.add_comm, this]
  have h1 := prunR_withStay_one l X
  rw [withStay_eq_append, prunR_append_le _ _ X 1 (by simp)] at h1
  rw [h1]

lemma rtR_withStay_zero (l : List (SpecR n K)) (X : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    rtR (withStay l) X 0 e = [(e, 1)] := rfl

/-- **A valid segment preceded by a stage keeping everything is a valid plan.** -/
theorem planOKR_of_segOKR {l : List (SpecR n K)} {X : Finset (Finset (Fin n))}
    (h : SegOKR q r L l X) (hL : 1 ≤ L) : PlanOKR q r L (withStay l) X := by
  refine ⟨h.rg, ?_, ?_⟩
  · intro t ht e he
    cases t with
    | zero =>
      rw [rtR_withStay_zero]
      exact routeOKR_stay (h.rg e he) _
    | succ t =>
      rw [prunR_withStay_succ] at he
      rw [rtR_withStay_succ]
      unfold wts
      rw [if_neg (by omega), prunR_withStay_succ]
      exact h.route t (by simpa [withStay] using ht) e he
  · intro t ht e he
    cases t with
    | zero => rw [rtR_withStay_zero]; simpa using hL
    | succ t =>
      rw [prunR_withStay_succ] at he
      rw [rtR_withStay_succ]
      exact h.len t (by simpa [withStay] using ht) e he

lemma length_withStay (l : List (SpecR n K)) : (withStay l).length = l.length + 1 := rfl

lemma prunR_withStay_length (l : List (SpecR n K)) (X : Finset (Finset (Fin n))) :
    prunR (withStay l) X (withStay l).length = prunR l X l.length := by
  rw [length_withStay, prunR_withStay_succ]

/-! ### Loads -/

/-- The total load of a segment at `S`. -/
def passSumR (l : List (SpecR n K)) (P : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  ∑ t ∈ range l.length, passR l P t S

lemma passR_append_lt (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n))) {t : ℕ}
    (ht : t < l₁.length) (S : Finset (Fin n)) : passR (l₁ ++ l₂) P t S = passR l₁ P t S := by
  unfold passR
  rw [prunR_append_le l₁ l₂ P t ht.le]
  congr 1
  apply filter_congr
  intro e _
  rw [rtR_append_lt l₁ l₂ P ht]

lemma passR_append_add (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n))) (t : ℕ)
    (S : Finset (Fin n)) :
    passR (l₁ ++ l₂) P (l₁.length + t) S = passR l₂ (prunR l₁ P l₁.length) t S := by
  unfold passR
  rw [prunR_append_add]
  congr 1
  apply filter_congr
  intro e _
  rw [rtR_append_add]

lemma passSumR_append (l₁ l₂ : List (SpecR n K)) (P : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) :
    passSumR (l₁ ++ l₂) P S = passSumR l₁ P S + passSumR l₂ (prunR l₁ P l₁.length) S := by
  unfold passSumR
  rw [List.length_append, sum_range_add]
  congr 1
  · exact sum_congr rfl fun t ht => passR_append_lt l₁ l₂ P (mem_range.1 ht) S
  · exact sum_congr rfl fun t _ => passR_append_add l₁ l₂ P t S

omit [NeZero K] in
lemma visitR_stay (e : Finset (Fin n)) : visitR e [((e, 1) : Finset (Fin n) × ZMod K)] = e := by
  unfold visitR
  simp

/-- The loads of `withStay l`: the first stage only loads the sets containing `S`. -/
lemma passSumR_withStay (l : List (SpecR n K)) (X : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    passSumR (withStay l) X S = (X.filter (S ⊆ ·)).card + passSumR l X S := by
  rw [withStay_eq_append, passSumR_append]
  congr 1
  · unfold passSumR passR
    simp only [List.length_singleton, range_one, sum_singleton]
    congr 1
    apply filter_congr
    intro e _
    show S ⊆ visitR e [(e, 1)] ↔ S ⊆ e
    rw [visitR_stay]
  · congr 1
    have h1 := prunR_withStay_one l X
    rw [withStay_eq_append, prunR_append_le _ _ X 1 (by simp)] at h1
    simpa using h1

end RefinedAbsorption.HyperPlan
