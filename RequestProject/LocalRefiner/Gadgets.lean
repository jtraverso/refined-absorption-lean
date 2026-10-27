module
public import RequestProject.LocalRefiner.Segments

/-!
# The gadgets of the local refiner (`r = 2`, `q = 2k + 4` even)

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Write `q = 2k + 4`, `d = q - 1 = 2k + 3` and `N = binom(q, 2) = (k + 2)(2k + 3)`.  The labels are:

* `xe e`: the edge `e` of `X` (one copy);
* `ae e`: `N - 1` parallel copies of `e` (so `xe e` and `ae e` form `N` copies of `e`);
* `tk e u`, `vb u i j`: a *token at `u`*, the multigraph on `u, u+1, u+2` with
  `k+2` copies of `{u, u+1}`, `k+2` copies of `{u, u+2}` and `(2k+4)(k+1)` copies of
  `{u+1, u+2}`.  Its degrees are `≡ 1` at `u` and `≡ 0` elsewhere modulo `d`; this is where
  `q` even (i.e. `d` odd) is used;
* `ke e`, `gb i j`: `d(k+1)` parallel copies of a pair (degrees `≡ 0` modulo `d`).

`wdeg_cls` computes all degrees modulo `d`, and `wdeg_empty` the sizes.
-/

@[expose] public section

namespace RefinedAbsorption.LocalRefiner

open Finset RefinedAbsorption.MultiRefiner

/-- The labels of the local refiner on `Fin n`. -/
inductive Lb (n : ℕ) where
  | xe (e : Finset (Fin n))
  | ae (e : Finset (Fin n))
  | tk (e : Finset (Fin n)) (u : Fin n)
  | ke (e : Finset (Fin n))
  | vb (u : Fin n) (i j : ℕ)
  | gb (i j : ℕ)
  deriving DecidableEq

variable {n : ℕ} [NeZero n]

/-- The segments of a token at `u`. -/
def tokSegs (k : ℕ) (u : Fin n) : List (Finset (Fin n) × ℕ) :=
  [({u, u + 1}, k + 2), ({u, u + 2}, k + 2), ({u + 1, u + 2}, (2 * k + 4) * (k + 1))]

/-- The segments of the labels; `gE i` is the pair carrying the global block `i`. -/
def segs (k : ℕ) (gE : ℕ → Finset (Fin n)) : Lb n → List (Finset (Fin n) × ℕ)
  | .xe e => [(e, 1)]
  | .ae e => [(e, (k + 1) * (2 * k + 5))]
  | .tk _ u => tokSegs k u
  | .ke e => [(e, (2 * k + 3) * (k + 1))]
  | .vb u _ _ => tokSegs k u
  | .gb i _ => [(gE i, (2 * k + 3) * (k + 1))]

/-- The degree classes modulo `d = 2k + 3`. -/
def cls (k : ℕ) (x : Fin n) : Lb n → ZMod (2 * k + 3)
  | .xe e => if x ∈ e then 1 else 0
  | .ae e => if x ∈ e then -1 else 0
  | .tk _ u => if x = u then 1 else 0
  | .ke _ => 0
  | .vb u _ _ => if x = u then 1 else 0
  | .gb _ _ => 0

/-- The sizes. -/
def csz (k : ℕ) : Lb n → ℕ
  | .xe _ => 1
  | .ae _ => (k + 1) * (2 * k + 5)
  | .tk _ _ => (2 * k + 4) * (k + 2)
  | .ke _ => (2 * k + 3) * (k + 1)
  | .vb _ _ _ => (2 * k + 4) * (k + 2)
  | .gb _ _ => (2 * k + 3) * (k + 1)

section Shift

lemma tok_ne_all (hn : 3 ≤ n) (u : Fin n) : u ≠ u + 1 ∧ u ≠ u + 2 ∧ u + 1 ≠ u + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : (1 : Fin (m+3)) = 0 := by simpa using (congrArg (· - u) h).symm
    simp at this
  · intro h
    have : (2 : Fin (m+3)) = 0 := by simpa using (congrArg (· - u) h).symm
    simp [Fin.ext_iff] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  · intro h
    have : (1 : Fin (m+3)) = 2 := by simpa using (congrArg (· - u) h)
    simp [Fin.ext_iff] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this; omega

lemma tok_ne₁ (hn : 3 ≤ n) (u : Fin n) : u ≠ u + 1 := (tok_ne_all hn u).1

lemma tok_ne₂ (hn : 3 ≤ n) (u : Fin n) : u ≠ u + 2 := (tok_ne_all hn u).2.1

lemma tok_ne₁₂ (hn : 3 ≤ n) (u : Fin n) : u + 1 ≠ u + 2 := (tok_ne_all hn u).2.2

end Shift

theorem wdeg_tok (k : ℕ) (u : Fin n) (gE : ℕ → Finset (Fin n)) (ℓ : Lb n)
    (hℓ : segs k gE ℓ = tokSegs k u) (S : Finset (Fin n)) :
    wdeg (segs k gE) ℓ S =
      (if S ⊆ {u, u + 1} then k + 2 else 0) + (if S ⊆ {u, u + 2} then k + 2 else 0) +
        (if S ⊆ {u + 1, u + 2} then (2 * k + 4) * (k + 1) else 0) := by
  simp [wdeg, hℓ, tokSegs, segAt, sum_range_succ]

/-- **Degrees modulo `d`.** -/
theorem wdeg_cls (k : ℕ) (hn : 3 ≤ n) (gE : ℕ → Finset (Fin n)) (ℓ : Lb n) (x : Fin n) :
    ((wdeg (segs k gE) ℓ {x} : ℕ) : ZMod (2 * k + 3)) = cls k x ℓ := by
  have h0 : ((2 * k + 3 : ℕ) : ZMod (2 * k + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0
  have htok : ∀ u : Fin n, ∀ ℓ : Lb n, segs k gE ℓ = tokSegs k u →
      ((wdeg (segs k gE) ℓ {x} : ℕ) : ZMod (2 * k + 3)) = if x = u then 1 else 0 := by
    intro u ℓ hℓ
    rw [wdeg_tok k u gE ℓ hℓ]
    simp only [singleton_subset_iff, mem_insert, mem_singleton]
    have h1 := tok_ne₁ hn u
    have h2 := tok_ne₂ hn u
    have h12 := tok_ne₁₂ hn u
    by_cases hxu : x = u
    · subst hxu
      simp only [true_or, if_true, h1, h2, false_or, if_false, add_zero]
      push_cast; linear_combination h0
    · by_cases hx1 : x = u + 1
      · subst hx1
        simp only [hxu, h12, true_or, or_true, false_or, if_true, if_false]
        push_cast; linear_combination (k + 2 : ZMod (2 * k + 3)) * h0
      · by_cases hx2 : x = u + 2
        · subst hx2
          simp only [Ne.symm h2, Ne.symm h12, or_true, false_or, if_true, if_false, zero_add]
          push_cast; linear_combination (k + 2 : ZMod (2 * k + 3)) * h0
        · simp [hxu, hx1, hx2]
  cases ℓ with
  | xe e => simp [wdeg, segs, segAt, cls, singleton_subset_iff]
  | ae e =>
    simp only [wdeg, segs, segAt, cls, singleton_subset_iff, List.length_singleton,
      sum_range_one, List.getD_cons_zero]
    split_ifs
    · push_cast; linear_combination (k + 2 : ZMod (2 * k + 3)) * h0
    · simp
  | tk e u => rw [htok u _ rfl]; rfl
  | ke e =>
    simp only [wdeg, segs, segAt, cls, singleton_subset_iff, List.length_singleton,
      sum_range_one, List.getD_cons_zero]
    split_ifs
    · push_cast; linear_combination (k + 1 : ZMod (2 * k + 3)) * h0
    · simp
  | vb u i j => rw [htok u _ rfl]; rfl
  | gb i j =>
    simp only [wdeg, segs, segAt, cls, singleton_subset_iff, List.length_singleton,
      sum_range_one, List.getD_cons_zero]
    split_ifs
    · push_cast; linear_combination (k + 1 : ZMod (2 * k + 3)) * h0
    · simp

/-- **Sizes.** -/
theorem wdeg_empty (k : ℕ) (gE : ℕ → Finset (Fin n)) (ℓ : Lb n) :
    wdeg (segs k gE) ℓ ∅ = csz k ℓ := by
  cases ℓ <;> simp [wdeg, segs, segAt, csz, tokSegs, sum_range_succ] <;> ring

end RefinedAbsorption.LocalRefiner
