module
public import RequestProject.OddGrid.PlanLoad

/-!
# Concatenation of plans

* `prun_append_le`, `prun_append_add`, `rt_append_*`: running `l₁ ++ l₂` is running `l₁`, then
  `l₂` on the result.
* `SegOK`: validity of a segment of a plan (no condition on the first stage);
  `SegOK.append`, `planOK_of_segOK`.
* `passSum_append`: the loads add up.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset

variable {n : ℕ}

lemma prun_append_le (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) :
    ∀ t ≤ l₁.length, prun (l₁ ++ l₂) P t = prun l₁ P t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [prun_succ, prun_succ]
    simp only [rt, ih (by omega), List.getD_append _ _ _ _ (by omega : t < l₁.length)]

lemma rt_append_lt (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) {t : ℕ}
    (ht : t < l₁.length) (e : Finset (Fin n)) : rt (l₁ ++ l₂) P t e = rt l₁ P t e := by
  simp only [rt, prun_append_le l₁ l₂ P t ht.le]
  rw [List.getD_append _ _ _ _ ht]

lemma prun_append_add (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) :
    ∀ t, prun (l₁ ++ l₂) P (l₁.length + t) = prun l₂ (prun l₁ P l₁.length) t := by
  intro t
  induction t with
  | zero => simpa using prun_append_le l₁ l₂ P l₁.length le_rfl
  | succ t ih =>
    rw [← Nat.add_assoc, prun_succ, prun_succ]
    simp only [rt, ih, List.getD_append_right _ _ _ _ (by omega : l₁.length ≤ l₁.length + t),
      Nat.add_sub_cancel_left]

lemma rt_append_add (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) (t : ℕ)
    (e : Finset (Fin n)) :
    rt (l₁ ++ l₂) P (l₁.length + t) e = rt l₂ (prun l₁ P l₁.length) t e := by
  simp only [rt, prun_append_add]
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- Validity of a segment of a plan. -/
def SegOK (l : List (Spec n)) (P : Finset (Finset (Fin n))) : Prop :=
  ∀ t < l.length, ∀ e ∈ prun l P t, RouteOK e (rt l P t e) ∧
    ((rt l P t e).isMove = true → Lonely (prun l P t) e)

lemma SegOK.append {l₁ l₂ : List (Spec n)} {P : Finset (Finset (Fin n))} (h₁ : SegOK l₁ P)
    (h₂ : SegOK l₂ (prun l₁ P l₁.length)) : SegOK (l₁ ++ l₂) P := by
  intro t ht e he
  by_cases h : t < l₁.length
  · rw [prun_append_le l₁ l₂ P t h.le] at he ⊢
    rw [rt_append_lt l₁ l₂ P h]
    exact h₁ t h e he
  · obtain ⟨s, rfl⟩ : ∃ s, t = l₁.length + s := ⟨t - l₁.length, by omega⟩
    rw [prun_append_add] at he ⊢
    rw [rt_append_add]
    rw [List.length_append] at ht
    exact h₂ s (by omega) e he

lemma SegOK.nil (P : Finset (Finset (Fin n))) : SegOK [] P := by
  intro t ht; simp at ht

/-- A plan whose first stage has no moves and whose segment is valid is valid. -/
lemma planOK_of_segOK {sp : List (Spec n)} {X : Finset (Finset (Fin n))}
    (hrg : ∀ e ∈ X, e.card = 2) (hseg : SegOK sp X)
    (h0 : ∀ e ∈ X, (rt sp X 0 e).isMove = false) : PlanOK sp X := by
  refine ⟨hrg, fun t ht e he => (hseg t ht e he).1, fun t ht e he hmv => ?_⟩
  refine ⟨?_, (hseg t ht e he).2 hmv⟩
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [h0 e he] at hmv; exact absurd hmv (by simp)
  · exact hpos

/-- The total load of a segment at `v`. -/
def passSum (l : List (Spec n)) (P : Finset (Finset (Fin n))) (v : Fin n) : ℕ :=
  ∑ t ∈ range l.length, pass l P t v

lemma pass_append_lt (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) {t : ℕ}
    (ht : t < l₁.length) (v : Fin n) : pass (l₁ ++ l₂) P t v = pass l₁ P t v := by
  unfold pass
  rw [prun_append_le l₁ l₂ P t ht.le]
  congr 1
  apply filter_congr
  intro e _
  rw [rt_append_lt l₁ l₂ P ht]

lemma pass_append_add (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) (t : ℕ)
    (v : Fin n) : pass (l₁ ++ l₂) P (l₁.length + t) v = pass l₂ (prun l₁ P l₁.length) t v := by
  unfold pass
  rw [prun_append_add]
  congr 1
  apply filter_congr
  intro e _
  rw [rt_append_add]

lemma passSum_append (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) (v : Fin n) :
    passSum (l₁ ++ l₂) P v = passSum l₁ P v + passSum l₂ (prun l₁ P l₁.length) v := by
  unfold passSum
  rw [List.length_append, sum_range_add]
  congr 1
  · exact sum_congr rfl fun t ht => pass_append_lt l₁ l₂ P (mem_range.1 ht) v
  · exact sum_congr rfl fun t _ => pass_append_add l₁ l₂ P t v

lemma prun_append_length (l₁ l₂ : List (Spec n)) (P : Finset (Finset (Fin n))) :
    prun (l₁ ++ l₂) P (l₁ ++ l₂).length = prun l₂ (prun l₁ P l₁.length) l₂.length := by
  rw [List.length_append, prun_append_add]

end RefinedAbsorption.OddGrid
