module
public import RequestProject.Basic

/-!
# Placing bounded rooted gadgets in `K_n^r`: definitions

This file sets up the data for the Partial Clique Embedding Lemma (Lemma 5.2 of
M. Delcourt and L. Postle, *Proof of the Existence Conjecture via Refined Absorption*,
arXiv:2402.17855).

A *gadget* on `Fin n` with `h` auxiliary vertices consists of
* a set of roots `R : Finset (Fin n)` (already placed vertices of the host), and
* a template `T : Finset (Finset (Fin n ⊕ Fin h))` of `r`-sets, each of which uses only roots on
  the left and at least one auxiliary vertex on the right.

A *placement* of the gadget is a map `φ : Fin h → Fin n` which is injective and avoids the roots.
The *new edges* are the images of the template edges under `Sum.elim id φ`.

Different gadgets may share vertices; only their new edges have to be disjoint.

The *mixed load* `load R Φ s J U` counts the already placed gadgets `i ∈ s` whose roots contain
`J` and whose auxiliary image contains `U`.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ}

/-- Well-formedness of a gadget with at most `k` roots, at least `r - 1` roots, and template
edges of size `r` built from roots and auxiliary vertices, each using an auxiliary vertex. -/
structure GadgetWF (r k : ℕ) (R : Finset (Fin n)) (T : Finset (Finset (Fin n ⊕ Fin h))) :
    Prop where
  roots_le : R.card ≤ k
  roots_ge : r - 1 ≤ R.card
  edge_card : ∀ t ∈ T, t.card = r
  edge_roots : ∀ t ∈ T, ∀ a, Sum.inl a ∈ t → a ∈ R
  edge_aux : ∀ t ∈ T, ∃ p, Sum.inr p ∈ t

/-- The vertex map of a placement: roots stay where they are, auxiliary vertices go along `φ`. -/
def emb (φ : Fin h → Fin n) : Fin n ⊕ Fin h → Fin n := Sum.elim (fun a => a) φ

/-- The image of one template edge. -/
def placeEdge (φ : Fin h → Fin n) (t : Finset (Fin n ⊕ Fin h)) : Finset (Fin n) :=
  t.image (emb φ)

/-- The new edges of a gadget placed along `φ`. -/
def newEdges (T : Finset (Finset (Fin n ⊕ Fin h))) (φ : Fin h → Fin n) :
    Finset (Finset (Fin n)) :=
  T.image (placeEdge φ)

/-- The auxiliary image of a placement. -/
def auxImage (φ : Fin h → Fin n) : Finset (Fin n) := univ.image φ

/-- A valid placement of a gadget with roots `R`: injective and avoiding the roots. -/
def ValidPlacement (R : Finset (Fin n)) (φ : Fin h → Fin n) : Prop :=
  Function.Injective φ ∧ ∀ p, φ p ∉ R

/-- **Mixed load** `d(J,U)`: the number of placed gadgets `i ∈ s` whose roots contain `J` and
whose auxiliary images contain `U`. -/
def load {ι : Type*} (R : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n) (s : Finset ι)
    (J U : Finset (Fin n)) : ℕ :=
  (s.filter fun i => J ⊆ R i ∧ U ⊆ auxImage (Φ i)).card

/-- The cap on the load `d(J,U)` with `|U| = u`: `λ^u · D · n^(r-1-|J|-u)`.  At the top level
`|J| + |U| = r - 1` it is `λ^|U| · D`. -/
def cap (r lam D : ℕ) (n : ℕ) (J : Finset (Fin n)) (u : ℕ) : ℕ :=
  lam ^ u * D * n ^ (r - 1 - J.card - u)

end RefinedAbsorption.Placement
