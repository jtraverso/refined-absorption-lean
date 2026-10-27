module
public import RequestProject.Basic

/-!
# Lemma 3.8 of the survey (General Embedding): definitions and statement

Conventions.

* The host is `K_n^r` on `Fin n`; `G` is an `r`-graph on `Fin n`.
* The multi-`r`-graph `J` is given by labelled edge copies `ends : ι → Finset (Fin n)`
  (parallel copies allowed); its `(r-1)`-degrees count multiplicity.
* A subgraph `H` of `J` is a set of edge copies `H : Finset ι`; its vertex set is
  `V(H) = ⋃_{x ∈ H} ends x`.
* For `H ∈ ℋ` the supergraph `W_H` is an `r`-graph on `Fin n ⊕ Fin (m H)`: the left vertices are
  old vertices (of `J`), the right vertices `Fin (m H)` are the new vertices of `W_H`.  Using a
  separate label type for every `H` builds in the requirement of Definition 3.6 that new vertices
  of different supergraphs are distinct and do not belong to `V(J)`.
* An embedding of `W_H` (Definition 3.7) is a map `f : Fin (m H) → Fin n` of the new vertices;
  the old vertices stay fixed.  The image of an edge `e` is `e.image (Sum.elim id f)`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {n : ℕ} {ι : Type*}

/-- The vertex set `V(H)` of a subgraph `H` (a set of edge copies) of the multigraph `ends`. -/
def subVerts [DecidableEq ι] (ends : ι → Finset (Fin n)) (H : Finset ι) : Finset (Fin n) :=
  H.biUnion ends

/-- The image of an edge of a supergraph under the embedding `f` of its new vertices. -/
def embedEdge {m : ℕ} (f : Fin m → Fin n) (e : Finset (Fin n ⊕ Fin m)) : Finset (Fin n) :=
  e.image (Sum.elim id f)

/-- **Definition 3.6 (supergraph system)**, for `W = (W_H : H ∈ ℋ)`: every `W_H` is an `r`-graph
containing `H`, and its old vertices lie in `V(H)`. -/
structure IsSupergraphSystem [DecidableEq ι] (r : ℕ) (ends : ι → Finset (Fin n))
    (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) : Prop where
  uniform : ∀ H ∈ ℋ, ∀ e ∈ W H, e.card = r
  super : ∀ H ∈ ℋ, ∀ x ∈ H, (ends x).map Function.Embedding.inl ∈ W H
  roots : ∀ H ∈ ℋ, ∀ e ∈ W H, e.toLeft ⊆ subVerts ends H

/-- `W` is edge-intersecting: for every edge `e` of `W_H` there is an edge `f` of `H` with
`e ∩ V(J) ⊆ f` (Remark 3.3 and Definition 3.6). -/
def IsEdgeIntersecting (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) : Prop :=
  ∀ H ∈ ℋ, ∀ e ∈ W H, ∃ x ∈ H, e.toLeft ⊆ ends x

/-- `W` is `C`-bounded: `e(W_H) ≤ C` and `v(W_H) = |V(H)| + m_H ≤ C` for all `H ∈ ℋ`. -/
def IsCBounded [DecidableEq ι] (C : ℕ) (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι))
    (m : Finset ι → ℕ) (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) : Prop :=
  ∀ H ∈ ℋ, (W H).card ≤ C ∧ (subVerts ends H).card + m H ≤ C

/-- `ℋ` is a `C`-refined family of subgraphs of `J`: every edge copy of `J` lies in at most `C`
members of `ℋ`. -/
def IsCRefinedFamily [DecidableEq ι] (C : ℕ) (ℋ : Finset (Finset ι)) : Prop :=
  ∀ x : ι, (ℋ.filter (fun H => x ∈ H)).card ≤ C

/-- **Definition 3.7**: `f` embeds `W_H` into `G ∖ (E(J) ∖ E(H))`.  The map `Sum.elim id f` is
injective on `V(W_H)` (i.e. `f` is injective and avoids `V(H)`), every edge of `W_H` is mapped to
an edge of `G`, and every edge containing a new vertex is mapped outside `E(J)`.  (Such an image
contains a vertex outside `V(H)`, so it can never be an edge of `H`; hence this is the same as
avoiding `E(J) ∖ E(H)`.) -/
def IsHostEmbedding [DecidableEq ι] (G : Finset (Finset (Fin n))) (ends : ι → Finset (Fin n))
    (H : Finset ι) {m : ℕ} (WH : Finset (Finset (Fin n ⊕ Fin m))) (f : Fin m → Fin n) : Prop :=
  Function.Injective f ∧ (∀ i, f i ∉ subVerts ends H) ∧
    ∀ e ∈ WH, embedEdge f e ∈ G ∧ (e.toRight.Nonempty → ∀ y, embedEdge f e ≠ ends y)

/-- The image `φ(W)` of the whole supergraph system. -/
def systemImage [DecidableEq ι] (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (φ : (H : Finset ι) → Fin (m H) → Fin n) : Finset (Finset (Fin n)) :=
  ℋ.biUnion (fun H => (W H).image (embedEdge (φ H)))

open Classical in
/-- **Lemma 3.8 (General Embedding)** (statement).  For integers `C > r ≥ 1` and `γ ∈ (0,1]` there
is `C' ≥ 1` such that the following holds.  Let `G ⊆ K_n^r`, let `J` be a multi-`r`-graph with
`Simple(J) ⊆ G` whose `(r-1)`-degrees are at most `D ≤ n / C'`, let `ℋ` be a `C`-refined family
of subgraphs of `J` and `W` a `C`-bounded edge-intersecting supergraph system for `ℋ`.  If every
`W_H` has at least `γ n^{|V(W_H) ∖ V(H)|}` embeddings into `G ∖ (E(J) ∖ E(H))`, then there is an
embedding `φ` of `W` into `G` such that the new edges of different supergraphs are distinct and
`Δ_{r-1}(φ(W)) ≤ C' D`. -/
def GeneralEmbeddingLemma : Prop :=
  ∀ (C r : ℕ), 1 ≤ r → r < C → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n : ℕ) (G : Finset (Finset (Fin n))) (ι : Type) [Fintype ι] [DecidableEq ι]
      (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
      (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) (D : ℝ),
      1 ≤ n → IsRGraph r G → (∀ x, (ends x).card = r) → (∀ x, ends x ∈ G) →
      (∀ S : Finset (Fin n), S.card + 1 = r →
        ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D) →
      D ≤ n / C' →
      IsCRefinedFamily C ℋ → IsSupergraphSystem r ends ℋ m W → IsEdgeIntersecting ends ℋ m W →
      IsCBounded C ends ℋ m W →
      (∀ H ∈ ℋ, γ * (n : ℝ) ^ (m H) ≤
        ((univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)).card : ℝ)) →
      ∃ φ : (H : Finset ι) → Fin (m H) → Fin n,
        (∀ H ∈ ℋ, IsHostEmbedding G ends H (W H) (φ H)) ∧
        (∀ H₁ ∈ ℋ, ∀ H₂ ∈ ℋ, H₁ ≠ H₂ → ∀ e₁ ∈ W H₁, ∀ e₂ ∈ W H₂,
          e₁.toRight.Nonempty → e₂.toRight.Nonempty → embedEdge (φ H₁) e₁ ≠ embedEdge (φ H₂) e₂) ∧
        ∀ S : Finset (Fin n), S.card + 1 = r →
          (((systemImage ℋ m W φ).filter (fun f => S ⊆ f)).card : ℝ) ≤ C' * D

end RefinedAbsorption
