module
public import RequestProject.MathlibImports

/-!
# Basic definitions: `r`-graphs, `K_q^r`-divisibility, packings and decompositions

We follow Section 1.3 of L. Postle, *Refined Absorption: A New Proof of the Existence
Conjecture and its Applications to Extremal and Probabilistic Design Theory*.

An `r`-graph on a vertex type `V` is modelled as a finite set `G : Finset (Finset V)` all of
whose members have cardinality `r`.  A copy of the clique `K_q^r` is determined by its vertex
set, a `q`-subset `Q` of `V`; its edges are the `r`-subsets of `Q`.
-/

@[expose] public section

namespace RefinedAbsorption

variable {V : Type*} [DecidableEq V]

/-- `G` is an `r`-graph (an `r`-uniform hypergraph): every edge has exactly `r` vertices. -/
def IsRGraph (r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∀ e ∈ G, e.card = r

/-- The degree of a vertex set `S` in `G`: the number of edges of `G` containing `S`. -/
def deg (G : Finset (Finset V)) (S : Finset V) : ℕ :=
  (G.filter (fun e => S ⊆ e)).card

/-- `G` is `K_q^r`-divisible if for every `i ∈ {0, …, r-1}` and every `i`-set `S`,
`binom(q-i, r-i)` divides the number of edges of `G` containing `S`. -/
def IsDivisible (q r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∀ S : Finset V, S.card < r → (q - S.card).choose (r - S.card) ∣ deg G S

/-- The edges of the copy of `K_q^r` with vertex set `Q`: the `r`-subsets of `Q`. -/
def cliqueEdges (r : ℕ) (Q : Finset V) : Finset (Finset V) :=
  Q.powersetCard r

/-- The number of cliques of the family `𝒬` containing the (vertex set) `e`. -/
def cliqueMult (𝒬 : Finset (Finset V)) (e : Finset V) : ℕ :=
  (𝒬.filter (fun Q => e ⊆ Q)).card

/-- The set of edges covered by a family of cliques `𝒬`. -/
def coveredEdges (r : ℕ) (𝒬 : Finset (Finset V)) : Finset (Finset V) :=
  𝒬.biUnion (cliqueEdges r)

/-- `𝒬` is a `K_q^r`-decomposition of the `r`-graph `G`: a family of copies of `K_q^r`
such that every edge of `G` lies in exactly one clique of `𝒬` and no other `r`-set lies
in any clique of `𝒬`. -/
structure IsDecomposition (q r : ℕ) (G 𝒬 : Finset (Finset V)) : Prop where
  rgraph : IsRGraph r G
  card_eq : ∀ Q ∈ 𝒬, Q.card = q
  mult_eq : ∀ e : Finset V, e.card = r → cliqueMult 𝒬 e = if e ∈ G then 1 else 0

/-- `𝒬` is a `K_q^r`-packing of `G`: a family of pairwise edge-disjoint copies of `K_q^r`
all of whose edges belong to `G`. -/
structure IsPacking (q r : ℕ) (G 𝒬 : Finset (Finset V)) : Prop where
  card_eq : ∀ Q ∈ 𝒬, Q.card = q
  sub : ∀ Q ∈ 𝒬, cliqueEdges r Q ⊆ G
  mult_le : ∀ e : Finset V, e.card = r → cliqueMult 𝒬 e ≤ 1

/-- The (non-isolated) vertex set `V(G)` of a hypergraph `G`. -/
def vertexSet (G : Finset (Finset V)) : Finset V := G.sup id

/-- `G` admits a `K_q^r`-decomposition. -/
def HasDecomposition (q r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∃ 𝒬, IsDecomposition q r G 𝒬

/-- The complete `r`-graph `K_V^r` on the (finite) vertex type `V`. -/
def completeRGraph (V : Type*) [Fintype V] (r : ℕ) : Finset (Finset V) :=
  (Finset.univ : Finset V).powersetCard r

end RefinedAbsorption
