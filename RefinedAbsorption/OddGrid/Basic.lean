module
public import RefinedAbsorption.GridRefiner.Labels

/-!
# Weighted labels for the grid refiner (odd `q`, `r = 2`)

Every label `ℓ` of the grid refiner stands for `w.val` parallel copies of a pair `p`, where
`pw ℓ = (p, w)` with `w : ZMod K` (in the application `K = q (q - 1)`).  A finite set of labels
`Q` lifts (`liftS`) to a multigraph; its *class* is the function `v ↦ Σ_{ℓ ∈ Q, v ∈ p_ℓ} w_ℓ` together
with the total weight `Σ_{ℓ ∈ Q} w_ℓ`.

* `ldiv_of_cls`: if the class vanishes modulo `q - 1` at every vertex and the total weight vanishes
  modulo `binom(q, 2)`, the lift is `K_q^2`-divisible.
* `cls_cast_of_ldiv`: conversely, a divisible lift has class `≡ 0 (mod q - 1)` at every vertex.
* `walkL`: a *signed walk*: the pairs of consecutive vertices of a walk, with alternating weights
  `w, -w, w, …`.  For a walk with an odd number of steps and distinct consecutive vertices its
  class equals the class of `w` copies of the pair of its end vertices (`lcls_walkL_odd`,
  `ltot_walkL`).
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner

/-- The labels of the grid refiner.  `x e` is the edge `e` of the input graph; the other labels
belong to a stage `t`: `anti t ℓ` (the anti-label of the input `ℓ`), `rest t ℓ k` (the `k`-th
piece of the rerouting of `ℓ`) and `cp t e k s`, `cn t e k s` (the carries of the chain on the
pair `e` at position `k` with value `s`). -/
inductive Lab (n K : ℕ) : Type
  | x (e : Finset (Fin n))
  | anti (t : ℕ) (ℓ : Lab n K)
  | rest (t : ℕ) (ℓ : Lab n K) (k : ℕ)
  | cp (t : ℕ) (e : Finset (Fin n)) (k : ℕ) (s : ZMod K)
  | cn (t : ℕ) (e : Finset (Fin n)) (k : ℕ) (s : ZMod K)
  deriving DecidableEq

section Weighted

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V] {K : ℕ}

/-- The segments of a weighted label: `w.val` copies of the pair `p`. -/
def wsg (pw : Λ → Finset V × ZMod K) (ℓ : Λ) : List (Finset V × ℕ) :=
  [((pw ℓ).1, (pw ℓ).2.val)]

/-- The class of a set of labels at a vertex. -/
def cls (pw : Λ → Finset V × ZMod K) (Q : Finset Λ) (v : V) : ZMod K :=
  ∑ ℓ ∈ Q, if v ∈ (pw ℓ).1 then (pw ℓ).2 else 0

/-- The total weight of a set of labels. -/
def tot (pw : Λ → Finset V × ZMod K) (Q : Finset Λ) : ZMod K :=
  ∑ ℓ ∈ Q, (pw ℓ).2

/-- Divisibility of the lift of a set of labels. -/
abbrev LDiv (q : ℕ) (pw : Λ → Finset V × ZMod K) (Q : Finset Λ) : Prop :=
  MIsDivisible q 2 (cpEnds (wsg pw)) (liftS (wsg pw) Q)

lemma wdeg_wsg (pw : Λ → Finset V × ZMod K) (ℓ : Λ) (S : Finset V) :
    wdeg (wsg pw) ℓ S = if S ⊆ (pw ℓ).1 then (pw ℓ).2.val else 0 := by
  rw [wdeg_list]; simp [wsg]

lemma cls_union (pw : Λ → Finset V × ZMod K) {P Q : Finset Λ} (h : Disjoint P Q) (v : V) :
    cls pw (P ∪ Q) v = cls pw P v + cls pw Q v := by
  unfold cls; rw [sum_union h]

omit [DecidableEq V] in
lemma tot_union (pw : Λ → Finset V × ZMod K) {P Q : Finset Λ} (h : Disjoint P Q) :
    tot pw (P ∪ Q) = tot pw P + tot pw Q := by
  unfold tot; rw [sum_union h]

variable [NeZero K]

/-- **Divisibility criterion** for weighted labels. -/
lemma ldiv_of_cls {q : ℕ} (hd : q - 1 ∣ K) (hN : q.choose 2 ∣ K) {pw : Λ → Finset V × ZMod K}
    {Q : Finset Λ} (h1 : ∀ v, ZMod.castHom hd (ZMod (q - 1)) (cls pw Q v) = 0)
    (h0 : ZMod.castHom hN (ZMod (q.choose 2)) (tot pw Q) = 0) : LDiv q pw Q := by
  apply divisible_of_zmod
  · rw [← h0, tot, map_sum]
    push_cast
    refine sum_congr rfl fun ℓ _ => ?_
    rw [wdeg_wsg, if_pos (empty_subset _), ZMod.castHom_apply, ZMod.natCast_val]
  · intro v
    rw [← h1 v, cls, map_sum]
    push_cast
    refine sum_congr rfl fun ℓ _ => ?_
    rw [wdeg_wsg]
    by_cases hv : v ∈ (pw ℓ).1 <;> simp [hv, ZMod.castHom_apply, ZMod.natCast_val]

/-- A divisible lift has class `≡ 0 (mod q - 1)` at every vertex. -/
lemma cls_cast_of_ldiv {q : ℕ} (hd : q - 1 ∣ K) {pw : Λ → Finset V × ZMod K} {Q : Finset Λ}
    (h : LDiv q pw Q) (v : V) : ZMod.castHom hd (ZMod (q - 1)) (cls pw Q v) = 0 := by
  have h1 := h {v} (by simp)
  simp only [card_singleton, show 2 - 1 = 1 from rfl, Nat.choose_one_right] at h1
  rw [mdeg_liftS] at h1
  rw [← (ZMod.natCast_eq_zero_iff _ _).2 h1, cls, map_sum]
  push_cast
  refine sum_congr rfl fun ℓ _ => ?_
  rw [wdeg_wsg]
  by_cases hv : v ∈ (pw ℓ).1 <;> simp [hv, ZMod.castHom_apply, ZMod.natCast_val]

end Weighted

/-! ### Signed walks -/

section Walk

variable {V : Type} [DecidableEq V] {K : ℕ}

/-- The class of a list of weighted pairs at a vertex. -/
def lcls (l : List (Finset V × ZMod K)) (v : V) : ZMod K :=
  (l.map fun s => if v ∈ s.1 then s.2 else 0).sum

/-- The total weight of a list of weighted pairs. -/
def ltot (l : List (Finset V × ZMod K)) : ZMod K := (l.map Prod.snd).sum

/-- The signed walk along a list of vertices: consecutive pairs with alternating weights. -/
def walkL : List V → ZMod K → List (Finset V × ZMod K)
  | p :: q :: rest, w => ({p, q}, w) :: walkL (q :: rest) (-w)
  | _, _ => []

lemma walkL_cons_cons (p q : V) (rest : List V) (w : ZMod K) :
    walkL (p :: q :: rest) w = ({p, q}, w) :: walkL (q :: rest) (-w) := rfl

lemma length_walkL (l : List V) (w : ZMod K) : (walkL l w).length = l.length - 1 := by
  induction l generalizing w with
  | nil => rfl
  | cons p tl ih =>
    cases tl with
    | nil => rfl
    | cons q rest => rw [walkL_cons_cons, List.length_cons, ih]; simp

/-- Class of a signed walk: telescoping. -/
lemma lcls_walkL (p : V) (tl : List V) (h : (p :: tl).IsChain (· ≠ ·)) (w : ZMod K) (v : V) :
    lcls (walkL (p :: tl) w) v =
      (if v = p then w else 0) + (-1) ^ (tl.length + 1) *
        (if v = (p :: tl).getLast (List.cons_ne_nil _ _) then w else 0) := by
  induction tl generalizing p w with
  | nil => simp only [walkL, lcls, List.getLast_singleton]; split_ifs with hv <;> simp [hv]
  | cons q rest ih =>
    have hpq : p ≠ q := (List.isChain_cons_cons.1 h).1
    have h' := (List.isChain_cons_cons.1 h).2
    rw [walkL_cons_cons]
    simp only [lcls, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih q h' (-w), List.getLast_cons_cons, List.length_cons]
    simp only [mem_insert, mem_singleton]
    by_cases hvp : v = p
    · subst hvp
      simp [hpq, pow_succ]
    · by_cases hvq : v = q
      · subst hvq; simp [hvp, pow_succ]
      · simp [hvp, hvq, pow_succ]

/-- Total weight of a signed walk. -/
lemma ltot_walkL (p : V) (tl : List V) (w : ZMod K) :
    ltot (walkL (p :: tl) w) = if Even tl.length then 0 else w := by
  induction tl generalizing p w with
  | nil => simp [walkL, ltot]
  | cons q rest ih =>
    rw [walkL_cons_cons]
    simp only [ltot, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih q (-w), List.length_cons]
    simp only [Nat.even_add_one]
    split_ifs <;> simp

/-- A walk with an odd number of steps: its class is that of `w` copies of its end pair. -/
lemma lcls_walkL_odd (p : V) (tl : List V) (h : (p :: tl).IsChain (· ≠ ·))
    (hodd : ¬ Even tl.length) (w : ZMod K) (v : V) :
    lcls (walkL (p :: tl) w) v =
      (if v = p then w else 0) +
        (if v = (p :: tl).getLast (List.cons_ne_nil _ _) then w else 0) := by
  rw [lcls_walkL p tl h, Nat.not_even_iff_odd] at *
  rw [show (-1 : ZMod K) ^ (tl.length + 1) = 1 from (hodd.add_one).neg_one_pow, one_mul]

end Walk

end RefinedAbsorption.OddGrid
