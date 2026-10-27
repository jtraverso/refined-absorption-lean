module
public import RequestProject.GridRefiner.Lift
public import RequestProject.LocalRefiner.OwnedChains

/-!
# Labels of the grid refiner

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The grid refiner is a sequence of *stages*.  All stages use one type of labels `GLab n`; a label
stands for a small multigraph on `Fin n` (a list of segments, `sg`).  The stage data (vertex maps,
token helpers, output shapes) are collected in a `Plan`.

* `x e`: the edge `e` of `X` (one copy);
* `anti t ℓ`: `q(q-1) - 1` parallel copies of the pair of the single-copy label `ℓ`;
* `path t ℓ j`: the `j`-th copy of the output shape of `ℓ` in the switch stage `t`;
* `tok t ℓ v`, `vz t v k j`: a *token* of the switch stage `t` at the moving vertex `v`, a
  multigraph on `v`, its helper `hw t v` and its target `pi t v` whose degrees are
  `≡ 1` at `v`, `≡ -1` at `pi t v` and `≡ 0` elsewhere modulo `q - 1`;
* `out t p i`, `pz t p k j`: single copies of the pair `p` (compression stage `t`).

`wdeg_list` computes degrees of labels from their segments; `divisible_of_zmod` is the
divisibility criterion used for all pieces.
-/

@[expose] public section

namespace RefinedAbsorption.GridRefiner

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

/-- The labels of the grid refiner. -/
inductive GLab (n : ℕ) : Type
  | x (e : Finset (Fin n))
  | anti (t : ℕ) (ℓ : GLab n)
  | path (t : ℕ) (ℓ : GLab n) (j : ℕ)
  | tok (t : ℕ) (ℓ : GLab n) (v : Fin n)
  | vz (t : ℕ) (v : Fin n) (k j : ℕ)
  | out (t : ℕ) (p : Finset (Fin n)) (i : ℕ)
  | pz (t : ℕ) (p : Finset (Fin n)) (k j : ℕ)
  deriving DecidableEq

/-- The data of the switch stages: the vertex map `pi t`, the token helpers `hw t` and the output
shapes `shape t p` (the list of pairs replacing a copy of the pair `p`). -/
structure Plan (n : ℕ) where
  pi : ℕ → Fin n → Fin n
  hw : ℕ → Fin n → Fin n
  shape : ℕ → Finset (Fin n) → List (Finset (Fin n))

variable {n : ℕ} (P : Plan n)

/-- The pair of a single-copy label. -/
def pe : GLab n → Finset (Fin n)
  | .x e => e
  | .path t ℓ j => (P.shape t (pe ℓ)).getD j ∅
  | .out _ p _ => p
  | .pz _ p _ _ => p
  | _ => ∅

/-- The segments of a token at `v` in the switch stage `t`. -/
def tokSg (q t : ℕ) (v : Fin n) : List (Finset (Fin n) × ℕ) :=
  [({v, P.hw t v}, 1 + (q - 1) * (q - 1)), ({P.hw t v, P.pi t v}, q - 2)]

/-- The segments of the labels. -/
def sg (q : ℕ) : GLab n → List (Finset (Fin n) × ℕ)
  | .x e => [(e, 1)]
  | .anti _ ℓ => [(pe P ℓ, q * (q - 1) - 1)]
  | .path t ℓ j => [((P.shape t (pe P ℓ)).getD j ∅, 1)]
  | .tok t _ v => tokSg P q t v
  | .vz t v _ _ => tokSg P q t v
  | .out _ p _ => [(p, 1)]
  | .pz _ p _ _ => [(p, 1)]

/-- The ends of the copies. -/
abbrev endsG (q : ℕ) : GLab n × ℕ × ℕ → Finset (Fin n) := cpEnds (sg P q)

lemma sg_x (q : ℕ) (e : Finset (Fin n)) : sg P q (.x e) = [(pe P (.x e), 1)] := rfl
lemma sg_path (q t : ℕ) (ℓ : GLab n) (j : ℕ) :
    sg P q (.path t ℓ j) = [(pe P (.path t ℓ j), 1)] := rfl
lemma sg_out (q t : ℕ) (p : Finset (Fin n)) (i : ℕ) :
    sg P q (.out t p i) = [(pe P (.out t p i), 1)] := rfl
lemma sg_pz (q t : ℕ) (p : Finset (Fin n)) (k j : ℕ) :
    sg P q (.pz t p k j) = [(pe P (.pz t p k j), 1)] := rfl

/-! ### Degrees of labels -/

lemma sum_range_getD {α M : Type*} [AddCommMonoid M] (l : List α) (d : α) (f : α → M) :
    ∑ s ∈ range l.length, f (l.getD s d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [ih, add_comm]

lemma wdeg_list {Λ V : Type} [DecidableEq V] (sg' : Λ → List (Finset V × ℕ)) (ℓ : Λ)
    (S : Finset V) :
    wdeg sg' ℓ S = ((sg' ℓ).map fun s => if S ⊆ s.1 then s.2 else 0).sum := by
  unfold wdeg segAt
  exact sum_range_getD (sg' ℓ) (∅, 0) (fun s => if S ⊆ s.1 then s.2 else 0)

lemma two_mul_choose_two (q : ℕ) : 2 * q.choose 2 = q * (q - 1) := by
  rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self q).two_dvd

/-- **Divisibility criterion** for lifts of label sets (`r = 2`). -/
lemma divisible_of_zmod {Λ V : Type} [DecidableEq Λ] [DecidableEq V] {q : ℕ}
    {sg' : Λ → List (Finset V × ℕ)} {Q : Finset Λ}
    (h0 : ((∑ ℓ ∈ Q, wdeg sg' ℓ ∅ : ℕ) : ZMod (q.choose 2)) = 0)
    (h1 : ∀ v, ((∑ ℓ ∈ Q, wdeg sg' ℓ {v} : ℕ) : ZMod (q - 1)) = 0) :
    MIsDivisible q 2 (cpEnds sg') (liftS sg' Q) := by
  intro S hS
  rw [mdeg_liftS]
  rcases Nat.lt_succ_iff.1 hS |>.lt_or_eq with h | h
  · rw [Nat.lt_one_iff, card_eq_zero] at h
    subst h
    simp only [card_empty, Nat.sub_zero]
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  · obtain ⟨v, rfl⟩ := card_eq_one.1 h
    simp only [card_singleton, show 2 - 1 = 1 from rfl, Nat.choose_one_right]
    exact (ZMod.natCast_eq_zero_iff _ _).1 (h1 v)

end RefinedAbsorption.GridRefiner
