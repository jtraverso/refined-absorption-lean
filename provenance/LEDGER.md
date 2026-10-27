# Ledger: proved theorems vs. stated assumptions (continuation run, 24 Oct 2026)

All Lean files build with Lean 4.28.0 / Mathlib (as pinned in `lean-toolchain` and
`lake-manifest.json`), without `sorry`, `admit`, `native_decide`, `axiom` declarations or
`@[implemented_by]`.  To reproduce the axiom check, run `lake build` and then
`lake env lean checks/AxiomCheck.lean`.  Each of the four new endpoints listed there
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Supplied nibble library (`PROVED_NIBBLE_EGJ_20261024.zip`)

The archive was present among the uploaded files, but in this run uploaded Lean sources could
not be brought into the project's Lean build.  So I did **not** compile, import, repair or diff
`RequestProject/Pseudorandom/*`, and nothing in this project depends on it.  There is no
compatibility diff, because no copy of those sources was made.  None of its modules are in this
project; the existing files `Basic`, `Statements`, `NibbleReserves`, ... are unchanged, except for one
docstring in `NibbleReserves.lean` and one new import line in `Main.lean`.

In place of an import, the weighted theorem is an explicit, named hypothesis,
`EGJWeightedMatching` (in `RequestProject/WeightedNibbleBridge.lean`).  I wrote it from the
published statement of Ehard–Glock–Joos Theorem 1.2, not from your Lean source.  To close the
chain on your side, prove `EGJWeightedMatching` from `Pseudorandom.theorem_1_2` with a short
adapter.  These are the points the adapter must line up:
* `Δ` is a natural number here (`Δ₀ ≤ Δ`).  A version for all real `Δ ≥ Δ₀` specialises to this.
* Vertices form any `α : Type` with `[Fintype α] [DecidableEq α]`.  Edges are a
  `Finset (Finset α)` whose members all have exactly `k` elements.
* Degree is `#{F ∈ E | v ∈ F} ≤ Δ`.  Codegree is `#{F ∈ E | u ∈ F ∧ v ∈ F} ≤ Δ^(1-δ)` for
  `u ≠ v`.  The edge count and the test count `Fintype.card ι` are each at most `exp(Δ^(ε²))`,
  where `ε = δ/(50k²)`.
* Weights are `ω : ι → Finset α → ℝ`, required to be nonnegative on `E`.  Eligibility is stated
  edge by edge: `∀ F ∈ E, ω i F * Δ^(1+δ) ≤ ∑ F ∈ E, ω i F`.
* The conclusion is a pairwise-disjoint `M ⊆ E` with
  `|ω_i(M) - ω_i(E)/Δ| ≤ Δ^(-ε) · ω_i(E)/Δ` for every eligible `i`.

## Proved in this run (`RequestProject/WeightedNibbleBridge.lean`)

| Lean name | Statement | Status |
| --- | --- | --- |
| `nibbleLeftoverDegree_of_egjWeightedMatching` | `EGJWeightedMatching → NibbleLeftoverDegree` | proved |
| `nibbleWithReserves_of_egjWeightedMatching` | `EGJWeightedMatching → NibbleWithReserves` (Corollary 2.4 as in the survey) | proved |
| `nibbleWithReservesGen_of_egjWeightedMatching` | `EGJWeightedMatching → NibbleWithReservesGen` | proved |
| `steinerExistence_of_refinerWithAbsorbers_egjWeightedMatching` | `RefinerWithAbsorbers → EGJWeightedMatching → SteinerExistenceConjecture` | proved |

`NibbleLeftoverDegree`'s quantifiers over `q, r, ρ, β` are unchanged: all `q > r ≥ 1`,
`ρ ∈ (0,1]`, `β ∈ (0,1)`.  Then `γ` and `n₀` are chosen before `n, G, H`.  The route is the one
you proposed:
* Auxiliary hypergraph: vertices are `r`-sets, edges are `cliqueEdges r Q` for `Q ∈ H`.
  `Q ↦ cliqueEdges r Q` is injective (`cliqueEdges_injOn`).  The hypergraph is uniform of degree
  `k = binom(q,r) ≥ 2` (`two_le_choose_of_lt`).  The degree of a vertex `e` is at most
  `cliqueMult H e`, and `0` off `G` (`auxEdges_deg_le`).  The codegree of distinct vertices is at
  most `n^(q-r-1)` (`auxEdges_codeg_le`).
* `Δ = ⌈(ρ + n^(-β)) binom(n, q-r)⌉` and `δ = min(1/2, 1/(4(q-r)))`.  There is one test weight
  `ω_S(F) = #{e ∈ F : S ⊆ e}` for each `(r-1)`-set `S`.  The tests are indexed by the finite
  subtype of `(r-1)`-subsets, so there are `binom(n, r-1) ≤ n^q` of them.
* Double count: `ω_S(E) = Σ_{e ∈ G, S ⊆ e} cliqueMult H e` (`auxEdges_sum_testWeight`).  For a
  matching, `ω_S(M)` is the number of covered `r`-edges containing `S`
  (`sum_testWeight_of_pairwiseDisjoint`).  The matching gives a packing
  (`packing_of_auxMatching`).
* Tests with `deg_G S < n^(1/2)` need no weighted conclusion.  For `deg_G S ≥ n^(1/2)`,
  eligibility holds uniformly, because `(q-r)δ ≤ 1/4`.  Then `large_test_bound` gives
  leftover `≤ deg_G S · (Δ^(-ε) + 2n^(-β)/ρ + 1/(ρ binom(n,q-r))) ≤ n^(1-γ)`, with
  `γ = min(β, ε)/2`.
* Every "for large `n`" step is a real-analytic `∀ᶠ` statement, fixed before `n` is chosen.
  These cover `n ≥ 2(q-r)`, `n^(-β) ≤ ρ/2`, `Δ ≥ Δ₀`, the codegree comparison,
  `n^q ≤ exp((An)^(ε²))`, eligibility, and the three error terms.  The cases `r = 1`, empty `G`
  and empty `H` need no special treatment.

## Stated, not proved (`Prop` assumptions)

| Name | Where | Role |
| --- | --- | --- |
| `EGJWeightedMatching` | `WeightedNibbleBridge.lean` | Ehard–Glock–Joos Thm 1.2.  It is the only input to Corollary 2.4.  Intended to be discharged by your supplied library, which was not imported here |
| `RefinerWithAbsorbers` | `OmniFromRefiner.lean` | my formulation of the constructive steps of Theorem 1.10.  **Not proved, and not claimed to be** |
| `NibbleLeftoverDegree` | `NibbleReserves.lean` | now a proved consequence of `EGJWeightedMatching` (not proved outright) |
| `NibbleWithReserves`, `RefinedEfficientOmniAbsorber`, ... | `Statements.lean` | survey statements as before |

As a result, the Existence Conjecture for Steiner systems is now proved from
`RefinerWithAbsorbers` and `EGJWeightedMatching`.  Corollary 2.4 is proved from
`EGJWeightedMatching` alone.

## The survey PDF (arXiv:2510.19978v1, uploaded as `2510.19978v1-refined-absorption.pdf`)

What I found about the statements behind `RefinerWithAbsorbers`:
* **Theorem 1.10** (Refined Efficient Omni-Absorber, citing [18] = Delcourt–Postle):
  `∀ q > r ≥ 1 ∃ C ≥ 1`: if `X ⊆ K_n^r` and `Δ_{r-1}(X) ≤ n/C`, there is a `C`-refined
  `K_q^r`-omni-absorber `A` for `X` with `Δ_{r-1}(A) ≤ C · max{Δ_{r-1}(X), n^{1-1/r} log n}`.
  Here *`C`-refined* is Definition 1.9: every edge of `X ∪ A` is in at most `C` members of the
  decomposition family.
* **Definition 3.5 (Refiner):** `R` is a `K_q^r`-refiner of `X` if `V(X) = V(R)`, `X` and `R`
  are edge-disjoint, and for every `K_q^r`-divisible `L ⊆ X`, `R ∪ L` decomposes into
  `K_q^r`-divisible subgraphs.  The survey then says it amends `C`-refined to require these
  subgraphs to be small.  This is said in prose; there is no displayed definition.
* **There is no numbered "refiner existence" theorem in the survey.**  Section 3.4 sketches the
  Refine Down Lemma and the Multiplicity Reduction Lemma, without statements, and defers to [18].
  The survey says it suffices to prove Theorem 1.10 for a `C`-refined refiner, *even allowing
  multi-edges*.  The multi-edges are then replaced by embedded fake-edges (Definition 3.4) and
  private absorbers.
* **Absorber embedding:** Lemma 3.8 (General Embedding) states:
  `∀ C > r ≥ 1, γ ∈ (0,1] ∃ C' ≥ 1`.  Suppose `G ⊆ K_n^r`, `J` is a multi-`r`-graph with
  `Simple(J) ⊆ G` and `Δ(J) ≤ n/C'`, `H` is a `C`-refined family of subgraphs of `J`, and `W` is
  a `C`-bounded edge-intersecting supergraph system for `H` (Definitions 3.6, 3.7).  Suppose
  also that each `W_H` has at least `γ n^{|V(W_H)∖V(H)|}` embeddings into `G ∖ (E(J) ∖ E(H))`.
  Then there is an embedding `φ` with `Δ_{r-1}(φ(W)) ≤ C' Δ_{r-1}(J)`.  Lemma 3.9 is the
  corollary for `δ(G) ≥ (1-ε)n`.  The absorbers come from Theorem 1.7, in the edge-intersecting
  form of Remark 3.3.
* So `RefinerWithAbsorbers` is **not** a statement of the survey.  It combines two things:
  (a) existence of a `C`-refined efficient refiner (proved in [18]; in the survey only through
  the multigraph route of Section 3.4), and (b) the fake-edge/absorber embedding of Lemma 3.8.
  In particular, my formulation asks for a *simple* refiner directly, with absorbers on the same
  `n` vertices.  It does not separate the multigraph step or the embedding hypotheses of
  Lemma 3.8.

The separate typed-triangle material you mentioned is not used anywhere.

## Continuation (second run, 24 Oct 2026): inline reference proofs

The continuation request supplied the Ehard–Glock–Joos / nibble library, the `r = 1` refiner and
the fake-edge divisibility file as inline Lean source.  In this environment, user-supplied Lean
code cannot be copied, retyped or transformed into the project's Lean build, so none of it was
used.  Consequently `EGJWeightedMatching` is **still an explicit hypothesis**,
`NibbleLeftoverDegree` / Corollary 2.4 are **still conditional** on it, and the
`r = 1` instance and fake-edge lemma are **not** in this tree.  The proposed adapter
(`egjWeightedMatching_proved` via `exists_nat_ge`) was not added.

Independent work done instead (`RequestProject/RefinerReductions.lean`, proved, standard axioms):

| Lean name | Statement |
| --- | --- |
| `refinerWithAbsorbers_iff_pairs` | `RefinerWithAbsorbers ↔ ∀ q r, 1 ≤ r → r < q → RefinerAbsorbersFor q r` (definitional) |
| `IsRefinedRefiner.mono` | a `C`-refined refiner is `C'`-refined for `C ≤ C'` |
| `isAttachedAbsorbers_of_isAbsorber` | Definition 1.5 absorbers, pairwise edge-disjoint and disjoint from `X ∪ R`, are attached absorbers |
| `isAttachedAbsorbers_empty` | if every `W ∈ 𝒲` has a `K_q^r`-decomposition, empty absorbers can be attached |
| `eq_empty_of_maxDegLE_lt_one` | an `r`-graph (`r ≥ 1`) with `Δ_{r-1} ≤ D < 1` is empty |
| `refinerAbsorbers_empty` | the empty refiner/family/absorbers work for `X = ∅` |
| `refinerAbsorbersFor_of_eventually` | a construction for all `n ≥ n₀` with constant `C` yields `RefinerAbsorbersFor q r` with constant `max C n₀ + 1` |

`RefinerWithAbsorbers` itself remains unproved.

## Continuation (third run, 24 Oct 2026): from-scratch modules

Everything below was written from scratch in this project. All results build with only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry`, `axiom` or
`implemented_by`.

### Nibble with leftover degree control (`RequestProject/Nibble/`)

| File | Content |
| --- | --- |
| `FiniteProb.lean` | product measure on random subsets (`Ex`, `Pr`), union bound, Bernstein / bounded-differences tail bounds |
| `Hyper.lean`, `RoundProb.lean`, `Waste.lean`, `RoundBounds.lean` | degrees, codegrees, coverage, expectations and Lipschitz bounds for one nibble round, waste control |
| `Round.lean` | `nibble_round`: one round of the Rödl nibble with degree, codegree and test-set control |
| `Iterate.lean`, `Params.lean` | iteration (`nibble_iterate`), explicit parameters (`nibble_of_params`) |
| `Main.lean` | `nearRegularNibble`: near-regular bounded-codegree hypergraphs have matchings that leave every test set small |
| `Bridge.lean` | `nibbleLeftoverDegree_proved`, `nibbleWithReserves_proved` (Corollary 2.4), `nibbleWithReservesGen_proved`, `steinerExistence_of_refinerWithAbsorbers` |

Consequence: `EGJWeightedMatching` is no longer needed. The Existence Conjecture now follows
from `RefinerWithAbsorbers` alone.

### `RefinerWithAbsorbers` for `r = 1` (`RequestProject/RefinerOne/`)

- `Chain.lean` builds a chain refiner on abstract labels. Block `i` holds `q - 1` new vertices,
  and a carry state in `{0, …, q-1}` passes through the inputs. Every piece is a single `q`-set,
  and every vertex lies in at most `4q` pieces. For each input subset `L` with `q ∣ |L|`, the
  chosen pieces partition the reservoir together with `L` (`cover`, `chosen_unique`,
  `chosen_not_fin`).
- `Transfer.lean` transports the construction to any vertex type along a labelling that is
  injective on the labels used (`chain_isRefinedRefiner`, `chain_hasDecomposition`).
- `Instance.lean` proves `refinerAbsorbersFor_one : 2 ≤ q → RefinerAbsorbersFor q 1`, with
  constant `C = 8q` and empty attached absorbers.
- `Existence.lean`: `refinerWithAbsorbers_of_two_le` and `steinerExistence_of_refinerAbsorbers_two_le`.
  Together they give the Existence Conjecture from the instances `RefinerAbsorbersFor q r` with
  `r ≥ 2` only.

### Still open

`RefinerAbsorbersFor q r` for `r ≥ 2` is still unproved. This is the constructive core of
Theorem 1.10: refined refiners for `r`-graphs, plus absorbers (Theorem 1.7) attached to every
member of the family. The Existence Conjecture is therefore proved here *conditionally* on this
statement for `r ≥ 2`.

## Continuation (fourth run, 25 Oct 2026): Graver–Jurkat–Wilson and Theorem 1.7

Every result below builds with only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); see `checks/AxiomCheck.lean`. There is no `sorry`, `axiom` or `implemented_by`.

### Theorem 3.2 (Graver–Jurkat, Wilson): `RequestProject/GJW/`

| Lean name | Statement |
| --- | --- |
| `graverJurkatWilson` | `GraverJurkatWilson`: every `K_q^r`-divisible `r`-graph with `v(L) ≥ q + r` has an integral `K_q^r`-decomposition |
| `null_mem_tradeSpan` (`Trades.lean`) | null designs are integer combinations of trades |

### Theorem 1.7 (existence of absorbers): `RequestProject/Absorber17/`

| File | Content |
| --- | --- |
| `Booster.lean` | polynomial MDS booster over a finite field: two `K_q^r`-decompositions of the same graph; the "on" decomposition contains the root clique and the "off" one is strongly orthogonal to it |
| `Maps.lean` | images of hypergraphs and decompositions along injective maps; unions and differences of decompositions |
| `AntiClique.lean` | `ACAbsorber` (absorber for the anti-clique); `exists_ACAbsorber : r ≤ q → Nonempty (ACAbsorber q r)`, built from boosters glued along the off-cliques, over `ZMod p` with `p > q` prime |
| `Transfer.lean` | absorbers under injective maps (`IsAbsorber.gmap`), removal of padding (`IsAbsorber.pad`), moving to `Fin N` |
| `Construction.lean` | `isAbsorber_Abs`: from a multi-absorber (two indexed clique families), anti-edges on private vertices plus attached anti-clique absorbers give a genuine absorber |
| `Theorem.lean` | `absorberExistence : AbsorberExistence` (Theorem 1.7). `L` is padded with two disjoint new `q`-cliques so that the vertex hypothesis of Graver–Jurkat–Wilson holds; afterwards the padding is removed |
| `Attach.lean` | `exists_absorber_fresh` (absorber on `V ⊕ ℕ` whose edges all contain a new vertex); `exists_attachedAbsorbers_fresh` (absorbers attached to every member of any family of divisible pieces, on new vertices, pairwise edge-disjoint and disjoint from `X ∪ R`) |

### Still open

`RefinerAbsorbersFor q r` for `r ≥ 2` remains unproved. Two pieces are missing:

1. Constructing `C`-refined `K_q^r`-refiners for `r`-graphs with `r ≥ 2`, i.e. the Delcourt–Postle refiner construction sketched in Section 3.4 of the survey.
2. Embedding the attached absorbers inside `K_n^r` (rather than on new vertices) with
   `Δ_{r-1} ≤ C · max(D, n^{1-1/r} log n)`.

Theorem 1.7, which supplies the absorbers themselves, is now proved. Its attachment to the pieces
is proved on new vertices.

## Continuation (fifth run, 25 Oct 2026): absorber library, multigraph refiners, multiplicity reduction

Every result below builds with only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); see `checks/AxiomCheck.lean`. There is no `sorry`, `axiom` or `implemented_by`.

### Uniform absorber library (`RequestProject/Absorber17/Library.lean`)

| Lean name | Statement |
| --- | --- |
| `IsBoundedAbsorber q r B L A Qon Qoff` | `A` is an absorber for `L`, `Qon` decomposes `A ∪ L`, `Qoff` decomposes `A`, and `|V(A)|`, `|A|`, `|Qon|`, `|Qoff|` are all `≤ B` |
| `exists_template` | each divisible `r`-graph on `Fin k` has a bounded absorber on `Fin k ⊕ Fin M` with the roots on the left (from Theorem 1.7) |
| `libraryBound q r hr hrq c` | `B(q,r,c)`: the maximum template size over all types on `≤ rc` vertices (finitely many) |
| `absorberLibrary` | for fixed `q > r ≥ 1` and `c` there is `B` such that every divisible `r`-graph `L` with `≤ c` edges and every vertex set `S`, `|S| ≥ B`, disjoint from `V(L)`, admit a `B`-bounded absorber with `V(A) ⊆ V(L) ∪ S` (the template is transported with the roots fixed) |
| `exists_boundedAttachedAbsorbers` | uniform-size attached absorbers for any family of divisible pieces with `≤ C` edges, on `B` new vertices reserved for each piece |

### Multigraph refiners with residue (`RequestProject/MultiRefiner/Basic.lean`)

Multi-`r`-graphs are labelled copies `ends : E → Finset V`; degrees and divisibility count
multiplicity.

| Lean name | Statement |
| --- | --- |
| `IsResidualMultiRefiner q r C ends X R Y 𝒲` | `C`-refined residual refiner of `X`: for every divisible `L ⊆ X`, `R ∪ L` = disjoint pieces of `𝒲` + divisible residue `⊆ Y` |
| `IsMultiRefiner` | residue in `∅` |
| `isResidualMultiRefiner_self` | the trivial residual refiner (residue `L` itself), the start of the refine-down iteration |
| `IsResidualMultiRefiner.trans` | composition of residual refiners (constants add) |
| `isRefinedRefiner_iff_multi` | for `ends = id`, multi-refiners are exactly `IsRefinedRefiner` |
| `MMaxDegLE`, `MMaxDegLE.union` | the `(r-1)`-degree budget, additive over disjoint unions |

### Multiplicity reduction (`FakeEdge.lean`, `Reduction.lean`, `Pipeline.lean`)

| Lean name | Statement |
| --- | --- |
| `fakeEdge` | `m = N − 1` anti-edges on `e` with new vertices, `N = ∏_{s<r} binom(q−s, r−s)` |
| `fakeEdge_deg_cast` | modulo `binom(q−|S|, r−|S|)` the fake edge has degree `[S ⊆ e]` at every `S` with `|S| < r` |
| `ReductionInvariant` | the invariant kept for the final embedding: refined refiner with constant `C·fakeBound`, lifted `X` unchanged, root degrees `≤ fakeBound · mdeg`, degrees of sets with a new vertex `≤ fakeBound` |
| `multiplicityReduction` | a `C`-refined multi-refiner (with `ends` injective on a kept set `K ⊇ X`) satisfies `ReductionInvariant` after the duplicate copies are replaced by fake edges |
| `IsRefinedRefiner.gmap` | refined refiners transported along injective vertex maps |
| `omniAbsorber_of_multiRefiner` | multi-refiner ⇒ `2C·fakeBound`-refined omni-absorber for the lifted `X` on the extended vertex set, with `deg(A, S₀) ≤ fakeBound·mdeg(R, S₀) + B·#{W ∈ 𝒲 : S₀ ⊆ V(W)}` |

### Still open

`RefinerAbsorbersFor q r` for `r ≥ 2` (hence `RefinerWithAbsorbers`) is still **not** proved. What
is missing is the degree budget: (a) building multi-refiners on `K_n^r` whose two terms in the
displayed bound are `O(max(D, n^{1-1/r} log n))` (the Refine Down construction), and (b) embedding
the new vertices of the fake edges and of the absorbers into `K_n^r` (Lemma 3.8 of the survey)
while keeping that bound.

## Session: Partial Clique Embedding Lemma and placement (continuation)

Mathematics: M. Delcourt and L. Postle, *Refined absorption*, arXiv:2402.17855v1 (Section 5.2 and
Sections 3–4). Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.
All results below build (`lake build RequestProject.Main`), contain no `sorry`, and depend only on
`propext`, `Classical.choice`, `Quot.sound` (see `checks/AxiomCheck.lean`).

### Lemma 5.2 (`RequestProject/Placement/`)

| Lean name | File | Statement |
| --- | --- | --- |
| `GadgetWF`, `ValidPlacement`, `newEdges`, `auxImage`, `load`, `cap` | `Defs.lean` | gadgets `(R, T)` with roots `R ⊆ Fin n`, template edges on `Fin n ⊕ Fin h`; a placement is a map `Fin h → Fin n` that is injective and avoids the roots; `load J U` = number of placed gadgets whose roots contain `J` and whose auxiliary image contains `U` (`|J| + |U| = r − 1`) |
| `rootIncidence`, `sum_load_insert_le`, `deg_biUnion_le_loads` | `Counting.lean` | counting lemmas: the new-edge degree is bounded by the mixed loads; adding a gadget raises loads in a controlled way |
| `InnerInv`, `innerInv_step` | `Inner.lean` | one-vertex-at-a-time extension of a partial placement of one gadget, avoiding saturated loads, host edges `G` and already used edges |
| **`partialCliqueEmbedding r h k`** | `Lemma52.lean` | ∃ `C > 0` (depending only on `r, h, k`) such that, if `C·Δ_{r−1}(G) ≤ n`, `C·D ≤ n`, `0 < n` and the root family has `(r−1)`-degree `≤ D`, all gadgets can be placed by injective root-avoiding maps with pairwise disjoint new edges, disjoint from `G`, and union of new edges of `(r−1)`-degree `≤ C·D`. Different gadgets may share vertices. No embedding provider is assumed. |
| **`clusteredPlacement`** | `Cluster.lean` | the same with gadgets grouped into bounded pieces, additionally controlling the `(r−1)`-degree of the final piece vertex sets (`pvOf`) |

### Applications

| Lean name | File | Statement |
| --- | --- | --- |
| `fakeTemplate`, `deg_placedFake_cast` | `FakeGadget.lean` | fake edges as gadgets; placed fake edges keep the divisibility congruence of `fakeEdge_deg_cast` |
| `IsStrongRefiner`, `IsStrongMultiRefiner` | `Interface.lean` | stronger interface: refined refiner + at most one `X`-edge per piece (`oneX`), `Δ(X) ≤ D`, `Δ(R) ≤ C·D`, piece-vertex-set degree `≤ C·D` |
| **`placedMultiplicityReduction`** | `Reduction.lean` | strong `C`-refined multi-refiner on `Fin n` ⇒ strong `C'`-refined simple refiner of `X.image ends` on `Fin n` with the same budget (fake edges placed by `clusteredPlacement`) |
| `exists_absorberGadget`, **`placedAttachedAbsorbers`** | `Absorbers.lean` | the bounded absorber library placed inside `Fin n`: attached `B`-bounded absorbers, pairwise edge-disjoint, disjoint from `X ∪ R`, union of `(r−1)`-degree `≤ C·D` |
| `absorbersOnStrongRefiner`, `refinerAbsorbers_of_strongMultiRefiner` | `Assembly.lean` | combination of both placements |
| `NativeStrongMultiRefiners q r` | `Assembly.lean` | **hypothesis (not proved)**: the native refine-down output, a strong multi-refiner with budget `≤ C·max(D, n^{1−1/r} log n)` |
| **`refinerAbsorbersFor_of_native`** | `Assembly.lean` | `NativeStrongMultiRefiners q r → RefinerAbsorbersFor q r` (`2 ≤ r < q`) |
| **`steinerExistence_of_native`** | `Existence.lean` | `(∀ q r, 2 ≤ r < q → NativeStrongMultiRefiners q r) → SteinerExistenceConjecture` |

### Refine-down (`RequestProject/RefineDown/Step.lean`)

| Lean name | Statement |
| --- | --- |
| `pieceP`, `pieceQ`, `stepR`, `stepY`, `stepW` | for each copy `e`: anti-edge `A_e`, fake edge `F_e`, pieces `P_e = {e} ∪ A_e`, `Q_e = A_e ∪ F_e` |
| `divisible_pieceP`, `divisible_pieceQ` | both pieces are divisible |
| `antiEdgeStep_decomp` | for divisible `L ⊆ X`: `P_e` on `L`, `Q_e` off `L`, residue `⋃_{e∈L} F_e` (divisible) |
| **`antiEdgeStep`** | for `r < q`, `stepR` is an `IsResidualMultiRefiner` of `X` with residue in `stepY`, constant `(fakeCount+1)·binom(q,r)+2`; every copy is in at most two pieces |

### Still open (honest status)

* `NativeStrongMultiRefiners q r` (the native refine-down construction of Theorem 4.4 with Lemmas
  4.1, 3.13, 3.14 and Theorem 3.8, with flatness and the degree budget
  `O(max(D, n^{1−1/r} log n))`) is **not** proved. The anti-edge step above is one basic move of
  it, on abstract new vertices; iterating it down to a bounded-size residue with flatness control
  is not formalized.
* Hence `RefinerAbsorbersFor q r` for `r ≥ 2` and `SteinerExistenceConjecture` remain
  **conditional** on `NativeStrongMultiRefiners`. The placement half (Lemma 5.2 applied to fake
  edges and to the absorber library) is proved.

## Session: placed refine-down rounds (continuation)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855. Lean formalization: Juan Pablo
Traverso Gianini, Apache-2.0. All results below build (`lake build RequestProject.Main`),
contain no `sorry`, `admit`, `native_decide` or new axioms, and depend only on `propext`,
`Classical.choice`, `Quot.sound` (re-run `checks/AxiomCheck.lean` to reproduce). Earlier results
are unchanged.

### Transport of residual multi-refiners (`RequestProject/RefineDown/Transport.lean`)

| Lean name | Statement |
| --- | --- |
| `mdeg_mapEnds_eq_sum` | if `ψ : V → V'` is injective on every copy, the degree of `S` after moving is the sum of the degrees of its pull-backs |
| `divisible_mapEnds`, `divisible_of_mapEnds` | divisibility survives moving vertices (and can be pulled back if `ψ` is injective on all vertices) |
| `residual_mapEnds` | a residual multi-refiner stays one after moving vertices along a map injective on every copy and on `V(X)` |
| `residual_relabel` | a residual multi-refiner stays one after renaming its copies along a map injective on `X ∪ R` |

### One placed round (`RoundGadget.lean`, `Round.lean`)

| Lean name | Statement |
| --- | --- |
| `Lab n`, `labEnds` | copy labels `ℕ × Finset (Fin n)` (creation round, vertex set) |
| `roundTemplate`, `roundTemplate_wf` | the anti-edge `A_e` and fake edge `F_e` of a copy as one gadget with roots `e` and `(q-r)(1+m)` auxiliary vertices |
| `psiV`, `newEdges_roundTemplate`, `psiV_injOn_edge`, `psiV_image_injOn` | the vertex map of a placement; the placed gadget is the image of the abstract new edges; injectivity on edges and on the edges of a copy |
| `RoundSpec` | one-round invariant: residual multi-refiner of `X` with residue `Y ⊆ R`; new copies tagged `k+1`, simple, avoiding the host `G`; at most one copy of `X` per piece; `Δ_{r-1}(R) ≤ C·D`; piece vertex sets of `(r-1)`-degree `≤ C·D` |
| **`placedRound`** | for `1 ≤ r < q` there is `C ≥ 1` such that every labelled `r`-multigraph `X` on `Fin n` with tags `≤ k` and `Δ_{r-1}(X) ≤ D`, with `C·Δ_{r-1}(G) ≤ n` and `C·D ≤ n`, has a round output satisfying `RoundSpec`. The new vertices are placed in the same `Fin n` by `clusteredPlacement` (Lemma 5.2). Its application conditions are derived from `Δ_{r-1}(X) ≤ D`; no provider of embeddings or refiners is assumed |

Proof: `antiEdgeStep` on abstract vertices, then `residual_mapEnds` along `psiV Φ` (where `Φ` is
the clustered placement), then `residual_relabel` into `Lab n`. The degree bounds come from
Lemma 5.2. The pieces' vertex sets are bounded by `pvOf`.

### Chaining rounds (`Iterate.lean`)

| Lean name | Statement |
| --- | --- |
| `IterSpec` | invariant of a chain of `m` rounds (tags in `(k, k+m]`, budget `B`) |
| `RoundSpec.toIterSpec`, **`IterSpec.trans`** | one more round on the residue composes, via `IsResidualMultiRefiner.trans`; budgets add; pieces of later rounds contain no copy of `X` |
| `sum_budget_le_of_halving` | if consecutive round budgets at least halve, the total is `≤ 2·(first budget)`, for any number of rounds |
| **`placedRounds m`** | `m+1` placed rounds chained inside `Fin n`. Each round derives the conditions of Lemma 5.2 from the previous one, and the edges created so far are added to the host. The constant depends on `m` |

### Still open (honest status)

* `NativeStrongMultiRefiners q r` is **not** proved, so `RefinerAbsorbersFor q r` (`r ≥ 2`) and
  the Existence Conjecture remain conditional on it.
* What is missing is the **decrease**. An anti-edge round replaces the residue `⋃_{e∈L} e` by
  `⋃_{e∈L} F_e`, which is no smaller (`Δ_{r-1}(Y) ≤ C·Δ_{r-1}(X)`). Chained rounds therefore
  multiply the budget by `C` each time, and the residue never becomes empty.
* **Next obligation:** a round in which the residue moves to a shrinking reserve `A ⊆ Fin n`.
  Its new vertices should be placed inside `A`, with flatness `deg_Y(S) ≲ D·(|A|/n)^{…}` for
  sets meeting `A`. Then the halving budgets of `sum_budget_le_of_halving` apply, followed by the
  terminal step on a bounded residue. This needs a variant of Lemma 5.2 with candidates
  restricted to `A`; the current `partialCliqueEmbedding`/`clusteredPlacement` places into all of
  `Fin n`. `RoundSpec`, `IterSpec.trans` and the transport lemmas are written so that such a
  round can be plugged in.

## Flat refine-down to empty residue (`RequestProject/FlatDown/`)

All results below are proved without `sorry` (axioms: `propext`, `Classical.choice`,
`Quot.sound`; see `checks/AxiomCheck.lean`).

| Lean name | Statement |
| --- | --- |
| `IsFlat i Z ends Y` | every copy of `Y` has at most `i` vertices outside the reserve `Z` |
| `pairedStep` | combinatorial core of every step: base pieces `B t` with `M` completion copies each give a residual refiner with constant `CB + CC·M + 2`, **independent of the number of base pieces** |
| `antiEdgeStep_reserve` | anti-edge step with auxiliary vertices in a reserve `U`: residual refiner with residue `(r-1)`-flat w.r.t. `U`, at most one copy of `X` per piece |
| `gjw_local`, `completion_dvd` | Graver–Jurkat–Wilson on a finite set; a lifted divisible link plus `resMod`-many clique completions is `K_q^r`-divisible |
| `multReduction`, `smallRefiner` | every `r`-multigraph with at most `k` distinct edges has a multi-refiner with empty residue made of parallel copies, constant depending only on `q, r, k` |
| `link_divisible` | the link `{x ∩ Z : x \ Z = T}` of an `i`-flat divisible multigraph is `K_{q-i}^{r-i}`-divisible |
| `fix_divisible` | one extra completion copy for the pieces used by `L = ∅` makes the refiner divisible |
| `flat_base`, `flat_piece_div` | decomposition of `R₀ ∪ (L ∩ X_act)` into lifted link pieces; divisibility of a lifted and completed piece |
| **`flatStep`** | **from `i`-flat to `(i-1)`-flat**: given multi-refiners (constant `Cl`, empty residue, inside `Z`) of the links of the outside `i`-sets, an `i`-flat `X` has a residual refiner with constant `flatConst q r Cl` whose residue is `(i-1)`-flat and contained in `X ∪ R`; new copies lie in `T ∪ Z` for an outside part `T` |
| `compose_relabel`, `relabel_nat` | composition of residual refiners across a relabelling of copies; relabelling new copies by `ℕ` |
| `linkRefiners_small` | if `|Z| = q + r`, the link refiners required by `flatStep` exist (by `smallRefiner` in uniformity `r - i`) with a constant depending only on `q, r, i` |
| **`flatDown`** | induction on flatness: every `i`-flat `r`-multigraph (`i < r < q`) has a multi-refiner with **empty residue**, constant depending only on `q, r` |
| **`multiRefiner_exists`** | for `1 ≤ r < q` there is `C = C(q,r)` such that every finite `r`-multigraph on a vertex set containing `q + r` vertices has (after an injective relabelling of its copies) a `K_q^r`-multi-refiner with empty residue and constant `C` |

The constant is uniform: the chain has exactly `r + 1` steps (anti-edge step, `r - 1` flat
steps, terminal `smallRefiner`), each with a constant depending only on `q, r`, and the
completion copies are charged to their base piece by `pairedStep`, so no constant grows with the
size of `X`.

### Still open after this step (honest status)

* `NativeStrongMultiRefiners q r` is **still not proved**, so `refinerAbsorbersFor_of_native`
  and `steinerExistence_of_native` keep it as a hypothesis.
* `multiRefiner_exists` works in the abstract multigraph setting with a reserve `Z` of constant
  size `q + r`. All new copies live in `Z` or in `T ∪ Z`, so the `(r-1)`-degrees of the refiner
  inside `Z` grow with `|X|`. `IsStrongMultiRefiner` needs `ends` injective on the kept copies,
  `mdeg R ≤ C·D`, piece degrees `≤ C·D` and the budget `B ≤ C·max(D, n^{1-1/r} log n)` in
  `Fin n`.
* What is missing is the **placed version**: nested reserves `Z` of size growing with `n`, with
  link refiners in lower uniformity placed inside the reserve with degree control (a variant of
  Lemma 5.2 with candidates restricted to the reserve), and the sparsification that makes the
  copies simple. `flatStep` is stated for an arbitrary reserve `Z ⊇ Z₀` and arbitrary link
  refiners, and its constant does not depend on `Z`, so it can be reused in that setting.

## Session: reserves, quantitative multiplicity reduction, uniform chains

All results below build (`lake build RequestProject.Main`) without `sorry`. They depend only on
`propext`, `Classical.choice` and `Quot.sound` (see `checks/AxiomCheck.lean`).

| Lean name | File | Statement |
| --- | --- | --- |
| `IsChainRefiner`, `IsChainRefiner.ofResidual`, **`IsChainRefiner.trans`**, `IsChainRefiner.toResidual` | `MultiRefiner/Chain.lean` | Residual refiners whose residue consists of their own copies. Copies of `X` lie in `≤ A` pieces, copies of `R` in `≤ A + B`, copies of the residue in `≤ B`, and pieces have size `≤ P`. Appending a stage with constant `C ≤ min(A,B,P)` whose residue consists of its new copies keeps `A, B, P` unchanged. So any number of stages gives constant `P + A + B`, whereas `IsResidualMultiRefiner.trans` adds the constants. |
| `card_Rlab_le`, `card_mRcls_le`, **`mdeg_mR_le`**, **`mult_mY_le`**, **`multiplicityReduction_quant`** | `FlatDown/MultDegree.lean` | Quantitative Multiplicity Reduction Lemma: new copies parallel to old ones, `mdeg R S ≤ (M+2)^2 · mdeg X S` for every `S`, residue among the new copies with multiplicity `≤ M` on every `r`-set. |
| `capA`, `InnerInvA`, `innerInvA_step`, `exists_innerInvA_univ` | `Placement/ReserveInner.lean` | Vertex-by-vertex placement of one gadget inside a reserve `Z`, with caps `λ^u · D · |Z|^(r-1-j-u)`. |
| `OuterInvA`, `outerInvA_step`, `card_cover_le_loads`, `sum_loads_leA`, `deg_used_leA`, **`reserveCliqueEmbedding`**, `rootIncidence_of_subset` | `Placement/ReserveLemma52.lean` | **Lemma 5.2 inside a reserve.** Roots may lie anywhere; auxiliary vertices go into `Z`. Hypotheses: `C · Δ(G) ≤ |Z|`, `C · D ≤ |Z|`, and every `j`-set lies in `≤ D · |Z|^(r-1-j)` root sets (implied by an `(r-1)`-degree bound when the roots lie in `U` with `|U| ≤ K|Z|`, via `rootIncidence_of_subset`). Conclusions: new-edge degree `≤ C · D`, and `≤ C · D` gadget vertex sets through every `(r-1)`-set. |
| **`placedReserveRound`** | `RefineDown/ReserveRound.lean` | One anti-edge round with all new vertices in `Z`. It satisfies `RoundSpec` with budget `D`, and every new copy meets `Z` (so the residue is `(r-1)`-flat). |
| `flatStep` (generalized) | `FlatDown/FlatProof.lean` | The completion support `Z₀ T W` may depend on the lifted piece. The old statement is the constant choice. |

### Still open (honest status)

`NativeStrongMultiRefiners q r` is **still not proved**, so `RefinerAbsorbersFor q r` (`r ≥ 2`)
and the Existence Conjecture remain conditional on it. The survey (Section 3.4) describes the
missing argument as follows. First, Refine Down from `X` to a reserve where the remainder is
essentially complete. Then alternate constant-factor Refine Down steps with Multiplicity
Reduction until the reserve has constant size. Of these, the following are now formalized:
* the reserve placement;
* the first (anti-edge) round into a reserve;
* quantitative Multiplicity Reduction;
* uniform-constant chaining of arbitrarily many stages;
* the abstract flat steps.

What is **not** formalized is a degree-controlled flat step in `Fin n`. That step needs:
* link refiners in lower uniformity, placed inside the reserve with control of both degrees and
  multiplicities (an induction on uniformity whose hypothesis carries this control);
* placement of the per-piece completion supports `Z₀ T W` with Lemma 5.2 inside the reserve;
* the degree bookkeeping showing that the remainder in the reserve has degree
  `O(max(D, n^{1-1/r} log n))`.

## Session: degree-controlled flat step in `Fin n` (continuation, 25 Oct 2026)

Everything below builds (`lake build RequestProject.Main`) without `sorry`. It depends only on
`propext`, `Classical.choice` and `Quot.sound` (see `checks/AxiomCheck.lean`).

| Lean name | File | Statement |
| --- | --- | --- |
| **`flatStep_struct`** | `FlatDown/FlatProof.lean` | `flatStep`, plus: every new copy is either a lifted link-refiner copy `(T, y)` with `T` an outside part and `y ∈ RN T`, or a copy of the `k`-th completion (`k ≤ fakeModulus q r`) of a lifted piece `t ∈ fI`. `flatStep` is now derived from it. |
| `flatCompCard`, `pieceSpan`, `compLab_card_le'`, **`flatStep_deg`** | `FlatDown/FlatDegree.lean` | Degree bookkeeping of one flat step: `mdeg R S ≤ ∑_T #{y ∈ RN T : S ⊆ T ∪ endsN T y} + (M+1)·flatCompCard q r Cl·#{t ∈ fI : S ⊆ pieceSpan t}`. |
| `IsResidualMultiRefiner.filter_nonempty`, `LinkRefiners.filter_nonempty`, `fI_mono` | `FlatDown/LinkAccounting.lean` | Empty pieces can be dropped from (residual, link) refiners. |
| **`linkSum_le`** | `FlatDown/LinkAccounting.lean` | `∑_T #{y : S ⊆ T ∪ endsN T y} ≤ ∑_{T ⊇ S \ Z} mdeg(endsN T, RN T, S ∩ Z)`. |
| **`flatRoots_count_le`** | `FlatDown/LinkAccounting.lean` | `#{(T,W) ∈ fI : J ⊆ T ∪ V(W)} ≤ ∑_{T ⊇ J \ Z} #{W ∈ 𝒲 T : J ∩ Z ⊆ V(W)}`. |
| `flatRoots`, **`placedFlatStep`** | `Placement/PlacedFlat.lean` | Flat step in `Fin n` with the supports `Z₀ T W` placed inside the reserve by `reserveCliqueEmbedding` (gadgets with roots `T ∪ V(W)`, no edges, `q + r` auxiliary vertices). Hypotheses: `q + r ≤ |Z|`, `Cs·D ≤ |Z|`, nonempty link pieces, and every `j`-set lies in `≤ D·|Z|^(r-1-j)` root sets. Conclusion: every `(r-1)`-set has degree `≤ (degree in the lifted link refiners) + Cs'·D` in the new copies. |
| **`placedFlatStep_link`** | `Placement/PlacedFlat.lean` | The same, without the nonemptiness hypothesis. The density hypothesis is on the link refiners: `∑_{T ⊇ J \ Z} #{W ∈ 𝒲 T : J ∩ Z ⊆ V(W)} ≤ D·|Z|^(r-1-|J|)`. Conclusion: `mdeg R S ≤ ∑_{T ⊇ S \ Z} mdeg(RN T, S ∩ Z) + Cs'·D`. |

Status of the three items listed as missing at the end of the previous session:

* *Placement of the completion supports `Z₀ T W` with the reserve lemma*: **done**
  (`placedFlatStep`, `placedFlatStep_link`).
* *Degree bookkeeping*: **done for one flat step** (`flatStep_deg`, `linkSum_le`,
  `flatRoots_count_le`). The per-level and multi-level bookkeeping that gives the budget
  `O(max(D, n^{1-1/r} log n))` is **not** done.
* *Link refiners in lower uniformity, placed inside the reserve with degree and multiplicity
  control*: **not done**. Concretely, `placedFlatStep_link` needs, for each outside `i`-set `T`, a
  `K_{q-i}^{r-i}`-multi-refiner of the link of `T` inside `Z` such that:
  * for `|S \ Z| = i`, the `(r-i-1)`-degrees `mdeg(RN T, S ∩ Z)` are bounded;
  * for `|S \ Z| = i - 1`, the multiplicities of the `(r-i)`-set `S ∩ Z`, summed over the
    `T = (S \ Z) ∪ {v}`, are bounded. So the link refiners of different `T` must be spread over
    `Z`;
  * the pieces satisfy the density bound above.

  For `i = r - 1` the links are `1`-uniform. The construction for `r = 1` (`RefinerOne`) gives the
  refiners, but not yet their spread placement inside `Z`.

So `NativeStrongMultiRefiners q r` is **still not proved**. `RefinerAbsorbersFor q r` (`r ≥ 2`)
and the Existence Conjecture remain conditional on it.

A note for the remaining budget argument. The scheme "refine down into a reserve of half size,
then multiplicity reduction, repeated" preserves the number of residue copies until they reach a
reserve `Z` where the average multiplicity is constant. With `|Z| ≈ (D n^{r-1})^{1/r}`, this costs
degree `≈ D^{1/r} n^{1-1/r}`. That is enough for the application in Section 2, where
`D = n^{1-δ}` and any `o(n)` budget suffices. But it exceeds `max(D, n^{1-1/r} log n)` for
`(log n)^r ≪ D ≪ n`. Matching the stated budget of Theorem 1.10 needs the finer compression of
the original Refine Down Lemma, which is not reproduced here.

## Session: link refiners in the reserve, chaining of levels (continuation)

Everything below builds (`lake build RequestProject.Main`) without `sorry`. It depends only on
`propext`, `Classical.choice` and `Quot.sound` (see `checks/AxiomCheck.lean`).

| Lean name | File | Statement |
| --- | --- | --- |
| **`chainLink_refiner`**, `chainFam_count_le`, `mdeg_chainRN_singleton`, `card_chainRN_le` | `FlatDown/ChainLink.lean` | `(4q+1)`-refined `K_q^1`-multi-refiner of a `1`-uniform link, with arbitrary pivots for the connecting copies, plus the counts of pieces and degrees it produces. |
| `greedy_balance` | `Placement/Balance.lean` | Greedy choice `σ : I → Z` with all loads `≤ cap`, provided `N·τ < |Z|·cap`. |
| `lf_pivots`, `lf_slot_count`, `lf_linkRefiners`, `lf_density`, `lf_degSum`, **`placedLastFlatStep`** | `Placement/LastFlat.lean` | The step from `(r-1)`-flat to `(r-2)`-flat in `Fin n` with spread chain refiners. No link-refiner hypotheses. The new copies have `(r-1)`-degree `≤ C'·D`. |
| `PlacedLinkLevel`, **`placedLinkLevel_last`** | `Placement/ChainLevels.lean` | The three hypotheses of `placedFlatStep_link`, at level `i`, for every input. The `(r-i-1)`-degrees and the spread multiplicities of `(r-i)`-sets are the single sum `∑_{T ⊇ S \ Z} mdeg(RN T, S ∩ Z) ≤ Cg·D`. Proved for `i = r - 1`. |
| `PlacedOut`, `placedOut_of_residual`, `PlacedOut.comp` | `Placement/ChainLevels.lean` | Output of a degree-controlled stage, and composition of stages. Composition carries over freshness, containment in `U ∪ Z`, and degree bookkeeping. |
| **`placedStep_of_level`**, **`placedChain`**, `placedChain_two` | `Placement/ChainLevels.lean` | Chaining the levels `j, …, 1`, given `PlacedLinkLevel` at each of them. The residue is `0`-flat and the new copies have degree `≤ C·D`. At each level `K` becomes `K + 1`, because the copies lie in `U ∪ Z`, and `D` becomes `(1 + C)·D`. Unconditional for `r = 2`. |
| **`placedIntoReserve`**, **`placedIntoReserve_two`** | `Placement/ChainLevels.lean` | Refine Down into the reserve: an arbitrary `r`-multigraph on `Fin n` with `(r-1)`-degree `≤ D` and `n ≤ K|Z|` gets a refiner whose residue lies inside `Z`, with new degrees `≤ C·D`. The proof is `placedReserveRound` followed by `placedChain`. Unconditional for `r = 2`. |

### Status of the pending items

* *Link refiners in lower uniformity, spread inside `Z`*: **done for `i = r - 1`**
  (`placedLinkLevel_last`). **Open for `1 ≤ i < r - 1`** (needed only for `r ≥ 3`). There the
  links are `(r-i)`-uniform with `r - i ≥ 2`. The abstract constructions (`multiRefiner_exists`,
  `flatDown`) do not control degrees: `IsMultiRefiner` bounds neither `|R|` nor the degrees of
  `R`. So what is needed is a degree-controlled version in uniformity `r - i`, placed inside
  `Z` and spread across the different `T`. That is an induction on uniformity whose hypothesis is
  `placedIntoReserve`-style, applied to the links.
* *Chaining the levels*: **done** (`placedChain`), conditional on the levels. Unconditional for
  `r = 2`.
* *Global accounting / budget*: **done for one reserve** (`placedIntoReserve`, degree `O(D)`).
  **Not done**: continuing from a residue inside `Z` down to a reserve of constant size. Note
  that our placements need `Cs·D ≤ |Z|`, where `D` is the degree of the input. A residue inside
  `Z` that has passed through Multiplicity Reduction has degree up to `M·|Z|`, so it cannot be
  placed into a strictly smaller reserve by the same mechanism. This step needs the dense part
  of the original Refine Down Lemma, which is not reproduced here. See also the note at the end
  of the previous session about the cost `D^{1/r} n^{1-1/r}`.

So `NativeStrongMultiRefiners q r` is **still not proved** (not even for `r = 2`), and
`RefinerAbsorbersFor q r` (`r ≥ 2`) and the Existence Conjecture remain conditional on it.

## Session: the dense step and Steiner systems for `r = 2` (continuation)

Everything below builds (`lake build RequestProject.Main`) without `sorry`. It depends only on
`propext`, `Classical.choice` and `Quot.sound` (see `checks/AxiomCheck.lean`).

| Lean name | File | Statement |
| --- | --- | --- |
| **`multiCliqueEmbedding`** | `Placement/MultiEmbed.lean` | Gadget placement in the reserve `Z` with parallel new edges allowed. Hypotheses: `C ≤ |Z|`, and every `j`-set lies in `≤ D·|Z|^(r-1-j)` root sets. Conclusion: `(r-1)`-sets lie in `≤ C·D` gadget vertex sets and in `≤ C·D` new edges counted with multiplicity. **No upper bound on `D`.** |
| `placedFlatStep(_link)`, `placedLastFlatStep`, `PlacedLinkLevel`, `placedStep_of_level`, `placedChain`, `placedChain_two` | `Placement/` | Same statements as before, with `Cs·D ≤ |Z|` weakened to `Cs ≤ |Z|`. |
| `Gen.multiRound` | `RefineDown/RoundGadgetGen.lean`, `RefineDown/MultiRound.lean` | Anti-edge round into a reserve, for any input degree. |
| `multiStage`, `IsResidualMultiRefiner.compose`, `mdeg_union_le` | `Dense/Stage.lean` | One stage: round + chain + Multiplicity Reduction, from a residue in `Z` to a residue in a sub-reserve `Z' ⊆ Z`. |
| `IsChainRefiner.mono'`, `.prepend`, `.prepend_relabel` | `Dense/Refiner.lean` | Bookkeeping for chains of stages. |
| `denseRefiner_of`, `stagedRefiner_of`, `exists_quarter` | `Dense/Iterate.lean` | Iteration through reserves of size `≈ n/4^k`. Refinedness stays uniform in the number of stages. |
| `stagedRefiner`, `topRefiner`, `NativeWeakStrongMultiRefiners`, **`nativeWeakStrongMultiRefiners_two`** | `Dense/Native.lean` | Strong multi-refiners with budget `2^t·Bd ≤ 2^t·C_t·D + B·n` for every `t` (that is, `o(n)` for `D = o(n)`). Proved for `r = 2`. |
| `WeakOmniAbsorberFor`, `SteinerExistenceFor`, `weakOmniAbsorberFor_of_native`, `steinerExistenceFor_of_weakOmni` | `Dense/Existence.lean` | Omni-absorbers with `ε·n` degree for inputs of degree `n^{1-δ}`, and the Section 2 argument (reserves, boost, nibble, absorption) from them. |
| **`steinerExistenceFor_two`** | `Dense/Existence.lean` | For every `q > 2`, an `S(2, q, n)` Steiner system exists for all large admissible `n`. **Unconditional.** |
| **`steinerExistence_of_nativeWeak`** | `Dense/Existence.lean` | The Existence Conjecture for Steiner systems, conditional only on `NativeWeakStrongMultiRefiners q r` for `r ≥ 3`. |

### Status of the pending items

* *Dense step (residue inside `Z` down to a reserve of constant size)*: **done** for the `o(n)`
  budget. The obstruction `Cs·D ≤ |Z|` came from the placement lemma forbidding parallel edges.
  `multiCliqueEmbedding` allows them, and Multiplicity Reduction removes them afterwards, so a
  residue of degree `≈ M·|Z|` can be refined into a reserve of a quarter of the size. The
  resulting budget is `C_t·D + B·n/2^t`.
* *`NativeStrongMultiRefiners q r` (exact budget `C·max(D, n^{1-1/r} log n))`*: **not proved**,
  not even for `r = 2`. The budget obtained is `o(n)`, which is all Section 2 uses.
* *`PlacedLinkLevel q r i` for `1 ≤ i < r - 1`* (needed only for `r ≥ 3`): **still open**. For
  each outside part `T`, the link is an `(r-i)`-uniform multigraph inside `Z` with
  `(r-i-1)`-degrees `≤ D`. It needs a `K_{q-i}^{r-i}`-multi-refiner with degrees `O(D)` and
  **no** additive term, spread over `Z` across the different `T`. That amounts to the whole
  theory in lower uniformity with linear degree bounds (an induction on `r`). The `o(n)`
  refiners built here have an additive term, so they do not suffice.
* *Piece degree for `r ≥ 3`*: `IsStrongMultiRefiner.pieceDeg` asks for at most `C·Bd` pieces
  whose vertex set contains a given `(r-1)`-set. For `r = 2` this follows from vertex degrees
  (`pieceDeg_le_of_card_one`). For `r ≥ 3` it is not tracked through the stages. So even with
  all link levels, `NativeWeakStrongMultiRefiners q r` for `r ≥ 3` would also need this
  bookkeeping.

## Session: piece degrees and additive terms (continuation)

Everything below builds (`lake build RequestProject.Main`) without `sorry`. It depends only on
`propext`, `Classical.choice` and `Quot.sound` (see `checks/AxiomCheck.lean`).

| Lean name | File | Statement |
| --- | --- | --- |
| `pdeg`, `pdeg_union_le`, `pdeg_image_le`, `pdeg_mono`, `pdeg_le_card` | `MultiRefiner/PieceDeg.lean` | Piece degree `pdeg ends 𝒲 S = #{W ∈ 𝒲 : S ⊆ ⋃_{c ∈ W} ends c}` (the quantity in `IsStrongMultiRefiner.pieceDeg`). It is subadditive over unions of families and does not increase under relabelling. |
| **`pdeg_le_of_parallel`** | `MultiRefiner/PieceDeg.lean` | If every piece consists of parallel copies, then for nonempty `S`, `pdeg S ≤ C · mdeg(X ∪ R, S)`. |
| **`pairFamily_pdeg_le`** | `MultiRefiner/PieceDeg.lean` | Pieces of a paired completion step: `pdeg S ≤ 2 · #{t : S ⊆ span t}` when both pieces of `t` lie in `span t`. |
| `flatStep_struct`, `flatStep_deg` (extended) | `FlatDown/FlatProof.lean`, `FlatDegree.lean` | The flat step also gives `pdeg S ≤ 2 · #{(T, W) : S ⊆ T ∪ Z₀ T W ∪ V(W)}`. |
| `placedFlatStep`, `placedFlatStep_link` (extended) | `Placement/PlacedFlat.lean` | Also `pdeg S ≤ Cs' · D` for `(r-1)`-sets, from the placement count. |
| `mW_parallel`, `multiplicityReduction_quant` (extended) | `FlatDown/MultDegree.lean` | Multiplicity reduction pieces consist of parallel copies. |
| `PlacedOut` (extended), `placedStep_of_level`, `placedChain`, `placedOut_of_residual`, `PlacedOut.comp` | `Placement/ChainLevels.lean` | `PlacedOut` also records `pdeg S ≤ C · D`; it is carried through steps and compositions. |
| **`PlacedLinkLevelA`**, `PlacedLinkLevel.toA` | `Placement/ChainLevels.lean` | Placed link refiners required only when `D ≥ a |Z|` (equivalently: bounds `C·(D + a|Z|)`). With `a = 0` this is `PlacedLinkLevel`. `placedStep_of_level` and `placedChain` now take `PlacedLinkLevelA` and the hypothesis `a |Z| ≤ D`. |
| `multiStage`, `StageProp`, `baseRefiner`, `RefinerOut`, `refinerOut_of_stage`, `denseRefiner_of`, `stagedRefiner_of`, `stagedRefiner`, `topRefiner` (extended) | `Dense/` | Every stage, the base case (`pdeg ≤ Cm·(1+(M+2)^2)·D + 2^Kf`, using `1 ≤ D`) and the iteration carry the piece-degree bound with the same budget as the degrees. They allow an additive term `a` that is monotone with `a m ≤ m`; the staged budget is `2^t·Bd ≤ 2^t·C_t·(D + a|Z|) + B·|Z|`. |
| **`nativeWeakStrongMultiRefiners_of_levelsA`** | `Dense/Native.lean` | For `2 ≤ r < q` and a monotone `a` with `a m ≤ m` and `k · a m ≤ m` for large `m` (every `k`): `PlacedLinkLevelA q r i a` for `1 ≤ i < r - 1` implies `NativeWeakStrongMultiRefiners q r`, **including `pieceDeg`**. |
| **`nativeWeakStrongMultiRefiners_of_levels`**, `nativeWeakStrongMultiRefiners_three`, `nativeWeakStrongMultiRefiners_two` | `Dense/Native.lean` | The case `a = 0`. For `r = 3` only `PlacedLinkLevel q 3 1` is needed; for `r = 2` nothing. |
| **`steinerExistence_of_levels`**, `steinerExistenceFor_of_levels`, `steinerExistenceFor_of_levelsA`, `steinerExistenceFor_three` | `Dense/Existence.lean` | The Existence Conjecture for Steiner systems, conditional only on the intermediate link levels `1 ≤ i < r - 1` (with or without a sublinear additive term). |

### Status of the pending items

* *Piece degree for `r ≥ 3`*: **done.** `IsStrongMultiRefiner.pieceDeg` is now proved for the
  constructed refiners in every uniformity. In each stage: the round already bounded it; flat
  steps are controlled by the placement of the completion supports (each piece lies in the span
  of one lifted link piece); multiplicity reduction has parallel pieces, so its piece degree is
  bounded by ordinary degrees; and the final finite step has a bounded number of pieces. Through
  the iteration the piece degree has the same budget as the degree.
* *`PlacedLinkLevel q r i` for `1 ≤ i < r - 1`*: **still open**, but the requirement is weaker.
  An additive term is now allowed: `PlacedLinkLevelA q r i a` with a monotone sublinear `a`
  (bounds `C·(D + a|Z|)`) is enough, so link refiners with a budget such as
  `C·max(D, |Z|^{1-1/(r-i)} log |Z|)` (the shape of Theorem 1.10 in uniformity `r - i`) would
  suffice. What remains is constructing such link refiners for all outside parts `T` at once:
  * inside the reserve `Z`;
  * spread over `Z`, so that `∑_T mult(RN T, ·)` is bounded;
  * with the density bound on their pieces.

  Two remarks on why this is not a corollary of what is already proved. (1) The constants of the
  link refiners must not depend on the target `t` of the budget (the `o(n)` argument multiplies
  them by `C_t`), so `ε·|Z|` additive terms with `ε` depending on `t` are not enough; a *fixed*
  sublinear `a` is. (2) The `o(n)` refiners of `NativeWeakStrongMultiRefiners` in uniformity
  `r - i` have such a `t`-dependent additive term, and they are built for one multigraph at a
  time, not spread over `Z` across the different `T`.
* *`NativeStrongMultiRefiners q r` (exact budget `C·max(D, n^{1-1/r} log n)`)*: **not proved**, not
  even for `r = 2`. The stage machinery needs a reserve of a constant fraction of the vertex set;
  refining into a smaller reserve of size `m` costs a factor `(n/m)^{r-1}` in the root density.
  The best budget obtainable this way is `≈ D^{1/r} n^{1-1/r}` (or `o(n)` via the stages). The
  finer compression of the original Refine Down Lemma is not reproduced.

So the Existence Conjecture for Steiner systems is now conditional **only** on the intermediate
link levels (`steinerExistence_of_levels`). For `r = 3` that is the single level `i = 1`, whose
links are graphs.

## Session: link levels in `ε`-form (continuation)

New files, all without `sorry`, imported from `RequestProject/Main.lean` and checked in
`checks/AxiomCheck.lean`. They use only `propext`, `Classical.choice` and `Quot.sound`.

| File | Main results |
| --- | --- |
| `Placement/ChainLevelsE.lean` | `PlacedLinkLevelE`, `PlacedLinkLevel.toE`, `PlacedLinkLevelA.toE`, `PlacedOutE`, `placedOut_iff_E`, `PlacedOutE.comp`, `placedStep_of_levelE`, `placedChainE` |
| `Dense/StageE.lean` | `StagePropE`, `multiStageE` |
| `Dense/NativeE.lean` | `refinerOut_of_stageE`, `stageProp_of_stagePropE`, `stagedRefinerE`, `nativeWeakStrongMultiRefiners_of_levelsE` |
| `Dense/ExistenceE.lean` | `steinerExistenceFor_of_levelsE`, `steinerExistenceFor_threeE`, `steinerExistence_of_levelsE` |

**What changed.** The previous hypothesis on the intermediate link levels, `PlacedLinkLevelA`
(bounds `C·(D + a|Z|)` with a fixed sublinear `a`), is replaced by the weaker `PlacedLinkLevelE`:

* `∀ K, ∃ Cl B, ∀ s, ∃ Ch Cd Cg`;
* the bounds are `2^s·(…) ≤ 2^s·Cd·D + B·|Z|` for the piece density (times `|Z|^{r-1-|J|}`) and
  `2^s·(…) ≤ 2^s·Cg·D + B·|Z|` for the link degrees.

In other words, the additive term only has to be `≤ ε|Z|` for each fixed `ε = B/2^s`, with
constants that depend on `ε`, and the refinedness `Cl` must stay uniform in `ε`. The chains choose
the precisions backwards: level `j+1` gets enough precision to absorb the constants of the later
levels. The stages and the iteration (`multiStageE`, `stagedRefinerE`) carry the
`2^s·Bd ≤ 2^s·C·D + B·n` form through to `NativeWeakStrongMultiRefiners`.

### Status of the pending items (honest)

2. **Link levels with an additive term.** This item is weakened but still open. The new
   hypothesis no longer needs the additive term to be a fixed sublinear function: it may depend on
   the precision, which is the form the existing `o(n)` refiners give. What remains is
   to build, for every `1 ≤ i < r-1`, link refiners for **all** outside parts `T` at once, such
   that:
   (a) they lie inside the reserve `Z`;
   (b) they are spread over `Z`, i.e. the sum over `T` of the link multiplicities at each
       `(r-1)`-set is bounded by `C_s D + B|Z|/2^s`;
   (c) they satisfy the piece-density bound.
   The `o(n)` refiners in the project are built for one multigraph at a time. Spreading them over
   the different `T` while keeping (b) needs a random-like or greedy distribution argument
   (Lemma 5.2 style, applied simultaneously to all link graphs), and that argument is not
   formalized.
3. **`NativeStrongMultiRefiners` with budget `C·max(D, n^{1-1/r} log n)`.** This item is unchanged
   and not proved, even for `r = 2`. The stages need a reserve that is a constant fraction of the
   vertex set, and refining into a smaller reserve of size `m` costs a factor `(n/m)^{r-1}`. On
   this route the best bound is about `D^{1/r} n^{1-1/r}`, or `o(n)` with the stages. Getting the
   exact exponent needs the fine compression of the original Refine Down Lemma, which is not
   reproduced. Section 2 of the paper (Existence Conjecture) only needs the `o(n)` budget, and
   that is what the conditional theorems use.

**Net effect.** `SteinerExistenceFor q 2` is unconditional (`steinerExistenceFor_two`). For
`r ≥ 3`, the Existence Conjecture is reduced to `PlacedLinkLevelE` at the intermediate levels
(`steinerExistence_of_levelsE`); for `r = 3` that is only `PlacedLinkLevelE q 3 1`.

## Session: link refiners for all link graphs at once (`LinkSpread/`)

New files, all without `sorry`, imported from `RequestProject/Main.lean` and checked in
`checks/AxiomCheck.lean`. They use only `propext`, `Classical.choice` and `Quot.sound`.

| File | Main results |
| --- | --- |
| `LinkSpread/Round.lean` | `liftTemplate`, `liftTemplate_wf`, `taggedRound` |
| `LinkSpread/Fibre.lean` | `liftEnds`, `fibre`, `outParts_liftEnds`, `linkRefiners_fibre` |
| `LinkSpread/Flat.lean` | `mdeg_lift`, `pdeg_lift_le`, `taggedFlatStep` |
| `LinkSpread/Chain.lean` | `TaggedOutE`, `liftEnds_rgraph`, `liftEnds_flat`, `mdeg_liftEnds_eq_sum`, `taggedStep_of_levelE` |
| `LinkSpread/Comp.lean` | `pairTg`, `pairBd`, `pairSet`, `fibre_pairSet`, `mdeg_lift_pairSet`, `pdeg_image_le_of_mem`, `TaggedOutE.comp`, `taggedChainE` |
| `LinkSpread/Assembly.lean` | `TaggedRefOutE`, `TaggedLinkRefinersE`, `placedLinkLevelE_of_tagged`, `steinerExistenceFor_three_of_tagged`, `steinerExistence_of_tagged` |

**What is proved.**

* *Simultaneous construction for all `T`.* The link graphs of all outside parts are handled as one
  tagged multigraph. Every degree is the lifted `(r-1)`-degree summed over all tags. The anti-edge
  round (`taggedRound`), one flat step (`taggedFlatStep`, `taggedStep_of_levelE`) and the whole chain
  of flat steps down to the reserve (`taggedChainE`) are built once for all fibres, with gadgets and
  completion supports placed globally. The chain uses the higher link levels in `ε`-form, with the
  precisions chosen backwards as in `placedChainE`.
* *Reduction of the open item.* `placedLinkLevelE_of_tagged` shows that `PlacedLinkLevelE q r i`
  follows from `TaggedLinkRefinersE q r i`. That hypothesis asks for multi-refiners of all fibres
  inside `Z` (point (a)) with lifted degree and lifted piece degree budget
  `C_s·D + B·|Z|/2^s` (point (b)). Point (c), the density bound on the pieces for every `J`, is no
  longer an assumption: every nonempty lifted piece spans at least `r` vertices of `U ∪ Z`, so root
  incidence turns the `(r-1)`-piece degrees into the density bound, with factor `(K+1)^{r-1}`.

### Status of the pending items (honest)

2. **Link levels.** Still open, now in the form `TaggedLinkRefinersE q r i` for `1 ≤ i < r-1`.
   The single-stage parts (round, flat steps, chain) exist for all fibres at once. What is missing
   is the analogue of the stage iteration (`multiStageE`, `stagedRefinerE`) for tagged multigraphs,
   and here two concrete obstacles were identified.
   (i) *Codegree across tags.* The untagged iteration relies on the residue of a stage having
   multiplicity `≤ M` inside a reserve `Z₁`, so its degree is `≤ M|Z₁|` and the budgets form a
   geometric series. For a tagged residue, the lifted degree of an `(r-1)`-set `S` with
   `|S \ Z| = i - 1` is `∑_v mult_{(S\Z) ∪ {v}}(S ∩ Z)`. This is the number of tags sharing the same
   body. Multiplicity reduction inside each fibre does not bound it by `M|Z₁|`, only by `M|U|`, and
   the round and flat bounds only give `C·D`. So the degree parameter does not decrease from stage
   to stage.
   (ii) *Tags outside the shrinking reserves.* The tags stay in `U` while the reserves shrink by a
   factor `4` per stage. Both the root-density hypothesis of `taggedRound` (all `J`, including
   those with few tag vertices) and the constants of the higher link levels (which depend on
   `|U| ≤ K|Z|`) degrade with `|U|/|Z_t|`. Only the sets `J` with at least `i - 1` tag vertices
   actually carry new load. For `i = 1` (the only level needed for `r = 3`) all `J` qualify, so
   (ii) disappears there, but (i) remains.
   Closing the item needs a distribution argument that controls the codegree across tags, for
   example a multiplicity reduction acting on all fibres at once, together with versions of the
   embedding lemma and of the level hypothesis that only measure the relevant sets `J`. Neither is
   formalized.
3. **`NativeStrongMultiRefiners` with the exact budget.** Unchanged, not proved.

**Net effect.** `SteinerExistenceFor q 2` is unconditional. For `r ≥ 3` the Existence Conjecture
follows from `TaggedLinkRefinersE` at the intermediate levels (`steinerExistence_of_tagged`), and
for `r = 3` from `TaggedLinkRefinersE q 3 1` alone (`steinerExistenceFor_three_of_tagged`).

## Session: tagged link refiners at level `1` (`LinkSpread/`, continuation)

New files, all without `sorry`, imported from `RequestProject/Main.lean` and checked in
`checks/AxiomCheck.lean`. They use only `propext`, `Classical.choice` and `Quot.sound`.

| File | Main results |
| --- | --- |
| `LinkSpread/RoundOut.lean` | `taggedRoundOut` (the anti-edge round as a tagged output) |
| `LinkSpread/Stage.lean` | `multRed_explicit`, `TStageOut`, **`taggedStage`** (one stage for all fibres at once, `ε`-form) |
| `LinkSpread/TRefOut.lean` | `TRefOut` (complete tagged refiners with an `S`-dependent budget), `TRefOut.toTaggedRefOutE`, `TRefOut.union`, **`TStageOut.prepend`** |
| `LinkSpread/LevelOne.lean` | `residue_deg_one`, `taggedBase`, `TRefOut.unionFin`, `sum_ite_le_sup`, **`classStep`** |
| `LinkSpread/LevelOneIter.lean` | **`taggedDense`** |
| `LinkSpread/LevelOneFinal.lean` | **`taggedStaged`**, **`taggedLinkRefinersE_one`**, **`steinerExistenceFor_three_unconditional`**, `steinerExistence_of_tagged_two` |

**How the two obstacles are overcome at level `i = 1`.**

(i) *Codegree across tags.* The lifted degree of the residue of a stage is bounded by
`M · (|Z₁| + #tags)` (`residue_deg_one`). That is linear in the reserve only if the number of tags is
linear in the reserve. So the tags are split into four classes, each with at most a quarter of the
tags, and each class gets its own disjoint quarter of the reserve for its residue (`classStep`).
The invariant `#tags ≤ K|Z| + K + 1` is then preserved down the recursion. At an `(r-1)`-set `S`,
only the class whose quarter contains `S ∩ Z` pays for the deeper stages (`TStageOut.prepend`,
`sum_ite_le_sup`), so the budgets form a geometric series (`taggedDense`: budget
`A·D + A'·|Z|`).

*Precision.* The `ε`-form needs the additive term to be `B·|Z|/2^t` with `B` and the refinedness
uniform in `t`. `taggedStaged` proves this by induction on `t`, as in `stagedRefinerE`. Each class
runs one stage at a high precision `s = t + 1 + (C_t + 4)` into its quarter, and then precision `t`
on the residue. The residue's lifted degree is bounded by the stage budget itself, so no codegree
bound is needed at this point. Small reserves and the base `t = 0` use `taggedDense`.

(ii) *Tags outside shrinking reserves.* For `i = 1` the tags are single vertices, so splitting
the tags also splits the tag vertices. Each class has at most `K|Q| + K + 1` tag vertices for its
quarter `Q`, so the set `U` (tag vertices together with the reserve) stays within `(K + 6)|Q|`.
The constants of `taggedStage` are taken once, for `K + 6`.

`taggedLinkRefinersE_one` finally bounds the number of tags by `|U| ≤ K|Z|`, because distinct
single-vertex tags lie in `U` (`card_image_tg_le`).

**Consequences.**

* `taggedLinkRefinersE_one : 2 < r → r < q → (levels 1 + j, j ≥ 1) → TaggedLinkRefinersE q r 1`.
* `steinerExistenceFor_three_unconditional : 3 < q → SteinerExistenceFor q 3`. For `r = 3` the
  only higher level is the last one, `placedLinkLevel_last`, so this holds **without hypotheses**:
  Steiner systems `S(n, q, 3)` exist for every `q > 3` and every large `n` satisfying the
  divisibility conditions.
* `steinerExistence_of_tagged_two`: the Existence Conjecture follows from `TaggedLinkRefinersE q r i`
  at the levels `2 ≤ i < r - 1` only. These levels exist only when `r ≥ 4`.

### Status of the pending items (honest)

2. **Link levels.** Closed for `i = 1`, for every `r ≥ 3`, assuming the higher levels; for `r = 3`
   it is unconditional. Still open: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1`, which only
   arises for `r ≥ 4`. Obstacle (i) is no longer the issue in the staged induction, because there
   the residue's degree is bounded by the stage budget. It still matters for the precision-`0` base
   (`taggedDense`), whose degree reset uses `M · (|Z₁| + #tag vertices)`. Obstacle (ii) remains
   for `i ≥ 2`. The tags are `i`-sets in `U`, so there can be about `|U|^i` of them, and splitting
   the tags into classes does not split the tag vertices. The set `U` of a class therefore does not
   shrink with its reserve. A splitting by vertex classes yields `(#classes)^i` tag types, and
   giving each type its own part of the reserve makes `|U|/|Z|` grow from one level to the next. A
   different distribution argument is needed.
3. **`NativeStrongMultiRefiners` with the exact budget.** Unchanged, not proved.

**Net effect.** `SteinerExistenceFor q 2` and `SteinerExistenceFor q 3` are unconditional. For
`r ≥ 4` the Existence Conjecture follows from `TaggedLinkRefinersE q r i` at the levels
`2 ≤ i < r - 1`.

## Session: the levels `2 ≤ i < r - 1` — diagnosis of the staged scheme (continuation)

New file, without `sorry`, imported from `RequestProject/Main.lean` and checked in
`checks/AxiomCheck.lean` (axioms `propext`, `Classical.choice`, `Quot.sound` only):

| File | Main results |
| --- | --- |
| `LinkSpread/Funnel.lean` | `exists_heavy_kset`, **`exists_heavy_pdeg`** |

**No new level is closed in this session.** `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` and
`NativeStrongMultiRefiners` with the exact budget are still open. This session analysed whether
the level-`1` proof (`classStep`, `taggedDense`, `taggedStaged`) can be extended to `i ≥ 2`. It
cannot, for a reason that goes beyond the `|U| / |Z|` growth recorded last time. The finding is
stated below. Only the counting lemma at its core is formalized; the rest of this section is
informal analysis and is **not** machine-checked.

### What `exists_heavy_pdeg` says (formal)

Let `Ts` be a nonempty set of tags. Suppose every tag `T` has a piece `W T ∈ 𝒲 T` whose span
`⋃_{c ∈ W T} ends T c` has at least `r - 1` vertices and lies inside `Q (part T)`, where `part T`
ranges over a set `P` of indices and every `Q j` has at most `m` vertices. Then some `(r-1)`-set
`S` satisfies

`|Ts| ≤ |P| · C(m, r-1) · ∑_{T ∈ Ts} pdeg (T ∪ ·) (𝒲 T) S`.

The proof is double counting over the `(r-1)`-subsets of the sets `Q j` (`exists_heavy_kset`).

### Why the level-`1` scheme does not extend (informal)

*The scheme.* At depth `t`, every class of tags runs a stage into its own reserve part. The parts
used at depth `t` are pairwise disjoint and have size about `|Z| / 4^t`. The residue then
recurses inside that part, down to a base case whose size `m₀` is bounded independently of the
precision `s`. The base refinedness is `≈ 2^{M·2^{m₀}}`, and the refinedness `Cl` must be uniform
in `s`, so `m₀` cannot grow with `s`. At every depth, each fibre whose residue is nonempty has
pieces whose span lies in its class's part. For the stages built here (round, chain,
multiplicity reduction), the residues are in general nonempty.

*The counting.* At depth `t` there are at most `4^t` parts, each of size `m = |Z| / 4^t`.
`exists_heavy_pdeg` gives an `(r-1)`-set `S ⊆ Z` with lifted piece degree at least
`N / (4^t · C(m, r-1)) ≳ N / (|Z| · m^{r-2})`, where `N` is the number of tags still active. At
the bottom of the recursion (`m ≈ m₀`) this is `≳ N / (|Z| m₀^{r-2})`.

* `i = 1`: `N ≤ |U| ≤ K|Z|`, so the bound is `O(K / m₀^{r-2})`. That is harmless, and consistent
  with `taggedLinkRefinersE_one`.
* `i = 2`: there are inputs with `N ≈ K²|Z|²/2` and `D = O(1)`. For instance, take
  `r = 4` and `q ≥ 5`. Let the tags be all pairs `{a, b}` from a set of `K|Z|` vertices outside
  `Z`. Split `Z` into blocks `B_0, …, B_{p-1}` of size `q - 2`. The fibre of `{a, b}` is the
  clique on `B_{(a + b) mod p}`. Then the lifted `3`-degree is at most
  `max(q - 3, K(q - 2) + 1)`, and every fibre is a `K_{q-2}`, so it needs a piece of span
  `≥ q - 2 ≥ 3`. The bound becomes `≳ K² |Z| / m₀²`. This is linear in `|Z|` with a constant that
  does not decrease with `s`. So it cannot be `≤ C_s D + B|Z|/2^s` with `B` uniform in `s`,
  which is what `TaggedLinkRefinersE` requires.
* `i ≥ 3`: `N` can be `≈ (K|Z|)^i`, and the bound is superlinear in `|Z|`. Then even the dense
  form `A·D + A'·|Z|` is out of reach for this scheme.

Splitting the tags differently does not help as long as the parts at each depth are pairwise
disjoint, or more generally have bounded overlap. The bound only uses the number of parts and
their size. Bounded overlap is exactly what lets "only one class pays at `S`" give a geometric
series. The `(r-1)`-sets that carry the load are the sets `S ⊆ Z` with no tag vertex. Their
control is genuinely needed downstream: `placedLinkLevelE_of_tagged`, and through it the flat
steps `placedFlatStep_link`, need the density of the link pieces at every `J ⊆ Z`, because the
completion cliques contain copies that avoid the outside part.

*What this rules out.* The obstruction (ii) of the previous sessions is a symptom of this. The tag
vertices do not shrink with the reserve, but even a hypothesis that does not involve `U` would
not save the scheme. Here are the variants examined in this session, all of which fail for this
reason:
1. Keep `U` and split by vertex classes: the ratio `|U|/|Z|` grows by a factor `≥ i` per level.
2. Drop `U`, using only "relevant" sets with at least `i - 1` tag vertices plus a codegree bound
   on the tags maintained by Beck–Fiala splitting. The load at the sets `S ⊆ Z` is then no
   longer controlled, but downstream needs it. Inside the chain, level `i + j` must also control
   the sets with `i - 1` vertices outside the outer reserve, which is the same problem one level
   up.
3. Per-tag sub-reserves combined with untagged refiners: this would need edge-multiplicity bounds
   for untagged refiners, with constants that do not depend on the reserve ratio. Neither exists.

*What a correct construction must do (informal).* The pieces of the `≈ |U|^i` link fibres have to
be spread over the whole reserve `Z` at every scale. A global average shows this is possible in
principle: about `D·|U|^{r-1}` piece incidences over `|Z|^{r-1}` sets. So deep residues cannot be
sent into disjoint geometrically shrinking reserves. One possible route uses a family of
overlapping reserve parts at each depth, with bounded co-occurrence of small vertex sets (an
algebraic or design-like family). Every class would get its own part, and the budgets would be
weighted by the spread of each class's tag family. The invariant would be a spread condition
`#{tags ⊇ A} ≤ (K|Q|)^{i - |A|}` for every `A`, maintained by Beck–Fiala splitting, which has
bounded degree `2^i` here. Making this work requires new versions of the stage, of the class
splitting and of the base case. None of it is formalized.

### Status of the pending items (honest)

2. **Link levels.** Closed for `i = 1`, unconditionally for `r = 3`. Still open:
   `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1`, which only arises for `r ≥ 4`. The staged
   scheme of level `1` cannot be extended (see above); a different distribution argument at all
   scales is needed.
3. **`NativeStrongMultiRefiners` with the exact budget.** Unchanged, not proved.

**Net effect.** Unchanged: `SteinerExistenceFor q 2` and `SteinerExistenceFor q 3` are
unconditional. For `r ≥ 4` the Existence Conjecture follows from `TaggedLinkRefinersE q r i` at the
levels `2 ≤ i < r - 1` (`steinerExistence_of_tagged_two`).

## Session: the exact budget for `r = 2` (analysis only, no new Lean)

At the user's request this session looked only at `NativeStrongMultiRefiners q 2`, i.e. strong
multi-refiners of a graph `X ⊆ K_n` with `Δ(X) ≤ D` whose budget is `C · max(D, √n log n)`.
**It is still open.** No Lean file was changed, and the whole project still builds without
`sorry`. Everything below is informal and **not** machine-checked.

*Why the existing tools cannot reach it.* Every construction in the project moves the copies of
`X` into a common reserve `Z` of size `m`, using the anti-edge round (`placedReserveRound`,
`Gen.multiRound`) and the last flat step (`placedLastFlatStep`), and then refines the residue
inside `Z`. Each vertex outside `Z` sends about `D` incidences into `Z`, so some vertex of `Z`
gets load `≳ D · n / m`. Multiplicity reduction then caps the residue at `M m²` copies, and
refining that residue costs `≳ m`. So one stage costs `≳ D n / m + m ≥ √(D n)`. Splitting the
work over nested reserves does not help: either each stage multiplies the degree by a constant,
or the reserve stays a constant fraction of `n`. The best bound on this route is about
`√(D n)`, and that is `O(√n log n)` only when `D = O(log² n)`. For `log² n ≪ D ≪ n` it is
not `O(D)`.

*An attempt that fails: `√n` disjoint groups.* Split `Fin n` into about `√n` groups of size `√n`.
Move every cross edge into a group with a flat step whose reserve is that group, then refine
each group's multigraph with the dense refiner inside the group. The dense refiner costs
`O(D + √n)` inside a universe of size `√n`. The loads would be fine, but the refiner property
fails, in two ways:
1. A flat step needs the link of the outside vertex `u` to be divisible, and only the whole link
   of `u` is (`deg_L u ≡ 0 mod q-1`). The part of the link that goes into a single group is not.
   Moving all of `u`'s edges into one group by an anti-edge round does not work either. The new
   vertices of a gadget on `uv` are adjacent to both `u` and `v`, so they cannot lie in `u`'s
   group and in `v`'s group at once. Some residue edges therefore always join two groups.
2. Even when every residue copy lies inside a group, a divisible residue `Res` only gives
   divisible degrees inside each group. The condition at `S = ∅` (`C(q,2) ∣ |Res|`) holds only
   in total, not group by group. So refining the groups one at a time is not a refiner of the
   union: `IsResidualMultiRefiner.decomp` is only available for divisible `L`.

*What is missing.* A refiner with budget `O(max(D, √n log n))` has to give each vertex its own
reserve, such that every reserve vertex serves `O(1)` vertices on average. It also needs a
global connector that carries both the residues between groups and the edge-count condition at
`S = ∅`. Both require new versions of the round and of the flat step (one reserve per vertex,
with links that stay divisible) and of the multiplicity reduction. None of them exists in the
project, and a complete informal construction was not found in this session.

### Status of the pending items (honest)

2. **Link levels.** Unchanged: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only `r ≥ 4`).
3. **`NativeStrongMultiRefiners` with the exact budget.** Unchanged, not proved, even for `r = 2`.
   Section 2 (Existence Conjecture) only needs the `o(n)` budget, which is proved for `r = 2`
   (`nativeWeakStrongMultiRefiners_two`).

## Session: one reserve per vertex and a global connector (`r = 2`)

**Proved** (no `sorry`, standard axioms only; `checks/AxiomCheck.lean`):

* `LocalRefiner.nativeStrongMultiRefiners_two_even`: `NativeStrongMultiRefiners q 2` for every even
  `q ≥ 4`, with budget `⌊D⌋ + 1` and constant `C = 64 q^4`.
* `LocalRefiner.refinerAbsorbersFor_two_even`: `RefinerAbsorbersFor q 2` for every even `q ≥ 4`.
* Supporting results: `isMultiRefiner_local` (multi-refiner with empty residue), `pc_cover` and
  `pc_unique` (the label-level partition), `touch_card_le`, `degR_le` and `pieceDeg_le` (loads),
  and `chCover`, `chUnique` and `chMult` (families of chain refiners with owners).

*How the obstacles of the previous session are avoided.* No vertex sends its edges into a common
reserve, so the `√(Dn)` load does not arise. Each vertex `u` has its own reserve `{u, u+1, u+2}`.
An edge `uv ∈ L` is not moved: its switch leaves a token at `u`, a token at `v` and a
degree-free bundle. Since the tokens have degree classes concentrated at a single vertex, no residue
joins two groups (obstacle 1). The per-vertex chain only needs `d ∣ deg_L u`, which holds vertex by
vertex. The condition at `S = ∅` is carried by the bundles alone, which a single global chain
absorbs (obstacle 2).

*Odd `q` (informal, not machine-checked).* For odd `q`, `d = q - 1` is even. The degree sum of any
multigraph is even, so a token cannot have degree class `1_u` alone. It must have class
`1_u + β`, where `β` has odd degree sum. Inside one chain all labels must have the same class: the
chain pieces are arbitrary mixtures of `d` labels, and taking `(t, x) = (0, 1)` and `(1, 0)` in the
step equation forces equal classes. So `β = 1_{p(u)}` for one partner `p(u)` per vertex. The
leftover of `e = uv` then has class `-1_{p(u)} - 1_{p(v)}`, which is again an edge, now between
partners. Compressing the partners halves the vertex set and doubles the degree. Even with
multiplicity compression this gives a load of about `Σ_j min(2^j D, n/2^j) ≈ √(Dn)`, the same bound
as before. A different, non-local argument is needed for odd `q`.

### Status of the pending items (honest)

2. **Link levels.** Unchanged: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only `r ≥ 4`).
3. **`NativeStrongMultiRefiners` with the exact budget.** **Proved for `r = 2` and even `q`.**
   Open for `r = 2` with odd `q`, and for `r ≥ 3`.

## Session: odd `q` — the parity obstruction proved in Lean (`GridRefiner/`)

**Proved** (no `sorry`, standard axioms only; `checks/AxiomCheck.lean`), in
`RequestProject/GridRefiner/`:

* `Lift.lean`: `mdeg_sup_eq_sum`, `divisible_of_partition`, `liftS_single`, **`lift_residual`**
  (refiners described on labels with single-copy inputs lift to `IsResidualMultiRefiner`).
* `Labels.lean`: `GLab`, `Plan`, `pe`, `tokSg`, `sg`, `wdeg_list`, `divisible_of_zmod`.
* `Parity.lean`: `sum_mdeg_singleton`, `even_sum_mdeg`, `even_sum_classes`,
  **`single_vertex_class_iff`**, **`no_local_unit_token`**, **`unit_token_needs_partner`**,
  **`partnerTok_deg`**, **`local_token_half_iff`**, **`eq_of_forall_sum_eq_zero`**,
  `sum_mdeg_singleton_on`, **`even_cut_of_divisible`**.

So the first two sentences of the previous section's informal analysis are now theorems: for odd
`q` no local unit token exists (`no_local_unit_token`), and the tokens absorbed by one chain all
have the same class (`eq_of_forall_sum_eq_zero`). Partner tokens exist (`partnerTok_deg`).

*Further analysis (informal, not machine-checked).*

1. *What a per-vertex chain can absorb.* Write `d = q - 1`. A chain at `u` absorbs `deg_L u`
   tokens of one fixed class `ψ_u`, and `ψ_u` must be realizable: its degree sum is even. If the
   switch of `e = uv` leaves tokens of classes `ψ_u`, `ψ_v`, the remainder of `e` has class
   `1_u + 1_v - ψ_u - ψ_v = -(β_u + β_v)`, where `β_u = ψ_u - 1_u` has odd degree sum
   (`even_sum_classes`). The remainder vanishes for every edge only if `β_v = -β_u` along the edges
   of `X`. On a connected component this forces one common vector `β` (up to sign), so all chains
   of the component touch the support of `β`. That costs load `≈ Σ deg = |component| · D`.
2. *The case `q ≡ 3 (mod 4)`.* Here `(d/2 + 1)·1_u` is realizable (`local_token_half_iff`). The
   class of `uv` is two local tokens plus the *parity edge* `(d/2)(1_u + 1_v)`, which has order `2`.
   Parity edges compose like edges over `Z/2`, and the parity edges of a divisible `L` form an even
   graph. By `even_cut_of_divisible`, every vertex set is crossed an even number of times. So the
   problem reduces to a `Z/2` version of itself. The half `(d/2)·1_u` alone is still not
   realizable, so the obstruction remains. For `q ≡ 1 (mod 4)` even this reduction is unavailable.
3. *Routing along cuts does not give `O(D)` on expanders.* Route each parity edge `uv` along
   chains `a(u) + a(v)` with `∂a(y) = y + z`. Then a structure edge `t` is used by exactly the
   `X`-edges crossing `S_t = {y : t ∈ a(y)}`, and its load is `|∂_X S_t|`. On an expander with
   `D ≫ log n`, every `S_t` must have size `O(budget/D)` or co-size `O(budget/D)`. Then the vertex
   where the small chains meet carries load `≳ n D`. So any construction with budget
   `C·max(D, √n log n)` for odd `q` must use pieces that are not of the "switch + chain + route"
   kind used here. A construction of that kind was not found.

### Status of the pending items (honest)

1. **`NativeStrongMultiRefiners q 2`, odd `q`.** Still open. The obstruction to the local
   construction is now proved in Lean (`no_local_unit_token`, `eq_of_forall_sum_eq_zero`). Items 1–3
   above are informal.
2. **Link levels.** Unchanged: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only `r ≥ 4`).
3. **Exact budget for `r ≥ 3`.** Unchanged, open.

## Session: odd `q`, one switch stage with partner tokens (`GridRefiner/OddSwitch.lean`)

**Proved** (no `sorry`, standard axioms only; `checks/AxiomCheck.lean`): `tok_cls`,
`swP1_divisible`, `swP0_divisible`, `switch_decomp`, **`switch_residual`**, `remainder_lift`,
**`swRest_classes`**, **`swRes_classes`**, **`switch_load`**, **`switch_load_inj`**,
**`switch_needs_remainder`**, `shiftPlan_hyp`, **`oddSwitch_stage`**. No use of
`NativeStrongMultiRefiners`; the target budget is unchanged.

*The step.* For `e = uv ∈ X` the tokens `tok u`, `tok v` are the partner tokens of
`partnerTok_deg` (classes `1_u - 1_{π u}`, `1_v - 1_{π v}`). The remainder needed to make
`{anti e, tok u, tok v, rem e}` divisible is forced: its class must be `1_{π u} + 1_{π v}` and its
size `≡ 1 (mod binom(q,2))`, so it is one copy of the edge `π u π v` (this needs `π u ≠ π v`).
Without it the piece is not divisible (`switch_needs_remainder`).

*Load.* The step has load `O(D)`: at most `9 q (q - 1) D` when `π` and `hw` are injective
(`switch_load_inj`). So **this step admits load `O(D)`**, and no obstruction to the step itself
exists. In general the load at `x` is controlled by the edges at `x` and the edges with an end in
`π⁻¹(x) ∪ hw⁻¹(x)` (`switch_load`).

*What remains (not proved).* The residue for `L` is the union of the rests (`switch_decomp`),
i.e. the tokens of `L` and the remainder graph `π(L)`, which has `|L|` edges and the same degree
data as `L` (`swRes_classes`). The step makes no progress on its own: closing it needs the
per-vertex chains for the tokens and a further treatment of `π(L)`. The informal analysis of the
previous sections (iterating with compression gives about `√(D n)`) is unchanged and is **not**
machine-checked.

### Status of the pending items (honest)

1. **`NativeStrongMultiRefiners q 2`, odd `q`.** Still open. One switch stage is proved, with
   load `O(D)`; the global closure is not.
2. **Link levels.** Unchanged: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only `r ≥ 4`).
3. **Exact budget for `r ≥ 3`.** Unchanged, open.

## Session: `NativeStrongMultiRefiners q 2` for every `q ≥ 3` (`OddGrid/`)

**Proved** (no `sorry`, standard axioms only; `checks/AxiomCheck.lean`):

* Plan reduction (`Compose`, `Plan`, `PlanDecomp`, `PlanMult`, `PlanLoad`, `PlanStrong`, `Concat`):
  `plan_ldecomp`, **`plan_strong`** (a valid plan gives an `IsStrongMultiRefiner` with constant
  `Cpl K M` and budget `B` whenever the loads `Σ_t pass t v` and the input degrees are `≤ B`).
  Segments concatenate (`SegOK.append`, `passSum_append`, `planOK_of_segOK`).
* Generic merge segment (`Merge.lean`): **`merge_seg`**, `merge_load0`, `merge_load1`.
* Grids (`Grid.lean`): rook pairs, `deg_le`, `card_le`, `swap`.
* `halve_seg`, `phase_spec` (repeated halving, `≤ 2 ⌈log₂ C⌉` stages), `extra_seg`.
* `greedy_color` (balanced colouring), `xstage` (first stage), `grid_plan`, `base_plan`.
* **`nativeStrongMultiRefiners_two`** (all `q ≥ 3`), `nativeStrongMultiRefiners_two_odd`,
  **`refinerAbsorbersFor_two`**, **`steinerExistence_of_refinerAbsorbers_three_le`**.

*Why the previous obstruction does not apply.* The earlier sessions showed that local tokens and
"switch + chain" constructions cannot reach `O(D)` for odd `q`. The plan construction does not use
tokens. Every edge is rerouted along odd walks (1 or 3 steps), so the parity of every cycle is
preserved. Vertices are emptied by merging all of their pairs into one pair, which is then *moved*
(allowed because a lone pair at a vertex of a divisible `L` carries weight `≡ 0 mod (q-1)`). The
`√(Dn)` compression bound of the earlier analysis is avoided because the input is first routed into
a fixed sparse structure, the rook graph of a `√n × √n` board (degree `O(√n)`). Only that structure
is then compressed. A halving of a rook graph is again a rook graph, so every halving costs
`O(√n)` per vertex, and there are `O(log n)` halvings.

### Status of the pending items (honest)

1. **`NativeStrongMultiRefiners q 2`.** **Proved for every `q ≥ 3`** (even and odd).
2. **Link levels.** Unchanged: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only `r ≥ 4`).
3. **Exact budget for `r ≥ 3`.** Unchanged, open. The Existence Conjecture for Steiner systems now
   needs only `RefinerAbsorbersFor q r` for `3 ≤ r < q`
   (`steinerExistence_of_refinerAbsorbers_three_le`), together with the hypotheses already listed in
   earlier sections (the weighted matching theorem for the nibble).

## Session: status of the remaining items, per-uniformity reduction (`LinkSpread/PerUniformity.lean`)

**Proved** (no `sorry`, standard axioms only; `checks/AxiomCheck.lean`):

* **`steinerExistenceFor_of_tagged_two`**: for fixed `3 ≤ r < q`, `SteinerExistenceFor q r` follows
  from `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` of the **same** `q` and `r` (the global
  version `steinerExistence_of_tagged_two` needed the levels for all `q, r` at once).
* **`steinerExistenceFor_four_of_tagged`**: `S(n, q, 4)` exist for all large admissible `n` as soon
  as the single level `TaggedLinkRefinersE q 4 2` holds.

**The nibble is no longer an assumption.** Both routes to the Existence Conjecture use the proved
nibble (`nibbleLeftoverDegree_proved`, `nibbleWithReservesGen_proved` in `RequestProject/Nibble/`):
`steinerExistence_of_tagged_two`, `steinerExistenceFor_of_tagged_two`,
`steinerExistence_of_refinerAbsorbers_three_le` and `steinerExistenceFor_three_unconditional` depend
only on `propext`, `Classical.choice` and `Quot.sound`, and their only hypotheses are the ones
displayed in their statements. The sentence of the previous summary saying that the nibble
hypotheses were still needed was out of date. `EGJWeightedMatching` is only used by the older
bridge `steinerExistence_of_refinerWithAbsorbers_egjWeightedMatching`, which is superseded.

**Not closed in this session** (honest): `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` and
`NativeStrongMultiRefiners q r` for `r ≥ 3` remain open. The rest of this section is informal
analysis, **not** machine-checked.

*What any construction for `TaggedLinkRefinersE q r i`, `i ≥ 2`, must do.* Write `a = |S \ Z|` for
an `(r-1)`-set `S`. The input hypothesis is vacuous for `a ≤ i - 2`, but the output must bound
`Σ_{T ⊇ S \ Z} #{pieces W of T : V(W) ⊇ S ∩ Z}` by `C_s D + B|Z|/2^s` there, and about
`(K|Z|)^{i-a}` tags contain `S \ Z`. On average this is harmless (the average piece load is
`O(D)`), so the difficulty is purely distributional.

1. *Common reserves.* If all tags of a class send their residues into one reserve, then
   `exists_heavy_pdeg` (previous session) forces a load `≳ N / (#parts · m₀^{r-1})`. With
   disjoint (or boundedly overlapping) parts this is not `o(|Z|)` for `i = 2` and is superlinear
   for `i ≥ 3`. So residues of different tags must go to different, heavily overlapping places.
2. *Per-tag reserves with per-tag stages.* Running `taggedStage` separately for every tag, with its
   own nested reserves, does not work either: the stage gives only a max-type bound `Bd` at every
   `(r-1)`-set inside the tag's reserve, and summing these over the `≈ (K|Z|)^{i}` tags whose
   reserve contains a set is superlinear even for pseudo-random reserves. The placements of all
   tags must share one load function, i.e. a version of the round, of the chain of flat steps and
   of the placement lemmas with a **per-tag host set** `Z_T` instead of one reserve.
3. *Reductions to level `1`.* Grouping the tags `T` into level-`1` instances (one designated
   vertex per tag, distinct inside a group) controls the sets with `a ≥ i - 1`, but for
   `a ≤ i - 2` the star of `S \ Z` meets `≳ |U|^{i-a-1}` groups, and level `1` gives no spread
   inside a group at sets larger than its own `(r-1)`-sets. The same happens when tags are peeled
   one vertex at a time.
4. *Universal templates.* A refiner of a multigraph restricts to a refiner of any sub-multigraph
   (drop the pieces that meet the removed copies; proved as `IsResidualMultiRefiner.restrict` in
   `MultiRefiner/Restrict.lean`), so the residues inside a reserve of size `w`
   can all be handled by copies of one universal refiner of `M · K_w^{(r-i)}`. Embedding these
   templates at random gives the right expected loads (geometric in the depth), but turning this
   into a deterministic bound needs a concentration argument (Chernoff/Bernstein, or a
   derandomised potential-function greedy) for templates of size up to `ε|Z|`; this is not
   available in the project.

So the missing ingredient is a joint placement of many tag-dependent structures in pairwise
overlapping host sets with a common load function, which is also how Delcourt–Postle proceed
(random choices and one final embedding step). For `r = 4` only `i = 2` (graph fibres) is needed
(`steinerExistenceFor_four_of_tagged`).

*`NativeStrongMultiRefiners q r`, `r ≥ 3`.* The budget `C · max(D, n^{1-1/r} log n)` is not implied
by the `o(n)` budget of `NativeWeakStrongMultiRefiners` (which holds for `r = 3`). The `r = 2` proof
routes pairs along odd walks of a rook graph (`OddGrid/`); the plan framework (`plan_strong`) is
specific to pairs, and an `r`-uniform analogue (rerouting `r`-sets through a sparse structure of
degree `O(n^{1-1/r})` and halving it `O(log n)` times) would have to be built from scratch. It is
not needed for the Existence Conjecture, whose remaining input is the tagged levels above.

### Status of the pending items (honest)

1. **Nibble hypotheses.** Closed: not used by any route (see above).
2. **Link levels.** `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only `r ≥ 4`): open. For
   `r = 4` the single level `i = 2` suffices (`steinerExistenceFor_four_of_tagged`).
3. **`NativeStrongMultiRefiners q r`, `r ≥ 3`.** Open; proved for `r = 2`.

**Net effect.** `SteinerExistenceFor q 2` and `SteinerExistenceFor q 3` are unconditional. For each
fixed `r ≥ 4`, `SteinerExistenceFor q r` follows from `TaggedLinkRefinersE q r i`, `2 ≤ i < r - 1`,
alone; the Existence Conjecture for Steiner systems follows from these levels for all `q, r`.

## Continuation (latest session): an `r`-uniform plan framework for `NativeStrongMultiRefiners`

All files in `RequestProject/HyperPlan/` (namespace `RefinedAbsorption.HyperPlan`), proved without
`sorry`, standard axioms only (`checks/AxiomCheck.lean`).

| Declaration | File | Content |
|---|---|---|
| `ModsOK`, `ldivR_iff` | `Class.lean` | divisibility of weighted `r`-sets via face classes modulo `binom(q-i, r-i)` |
| `box_sum_eq_zero`, `box_cover_card` | `Box.lean` | boxes (transversals `J ∪ ρ(e \ J)`) have class `0` at every face of size `< r`; lower boxes only at faces covering the moved part |
| `PlanOKR`, `plan_ldecompR` | `Stage.lean`, `Plan.lean` | multi-stage plans of signed lists of `r`-sets, with loneliness-restricted carries; every valid plan is a decomposition with empty residue |
| `lift_residualR`, `stW_loadR` | `Lift.lean`, `Load.lean` | lifting to multigraphs; route loads at `(r-1)`-sets |
| **`plan_strongR`** | `Strong.lean` | a valid `r`-uniform plan with bounded final family and loads `≤ B` gives an `IsStrongMultiRefiner q r … B` |
| `RPlans q r` | `Native.lean` | purely combinatorial statement: plans with loads `≤ C · max(D, n^{1-1/r} log n)` exist |
| **`nativeStrongMultiRefiners_of_rPlans`** | `Native.lean` | `RPlans q r → NativeStrongMultiRefiners q r` for `1 ≤ r < q` |
| **`rPlans_two`**, `nativeStrongMultiRefiners_two_viaR` | `Two.lean` | the grid plans of `OddGrid` are valid `2`-uniform plans, so `RPlans q 2` holds for `q ≥ 3` (the reduction is not vacuous and recovers the `r = 2` result) |
| `routeOKR_fullBox`, `routeOKR_loneBox`, `routeOKR_stay` | `Moves.lean` | valid moves for `r`-sets: full boxes for every weight; boxes moving a part that lies in no other current set, for the values allowed by loneliness |
| **`collapse_plan`**, `partite_strongMultiRefiner` | `Collapse.lean` | for every `r`: an explicit `(r+1)`-stage valid plan collapsing any `r`-partite `r`-graph onto the single set of hubs, hence a strong multi-refiner with one final set (degree budget not controlled) |

**What remains for `r ≥ 3`: exactly `RPlans q r`, i.e. the load bound.** All bookkeeping of
refiners is done once and for all by `plan_strongR`, and `collapse_plan` shows that valid
`r`-uniform plans with a bounded final family exist; what is missing is a plan whose route loads at
every `(r-1)`-set are `O(max(D, n^{1-1/r} log n))`.

Why `collapse_plan` does not give the budget (informal, not formalised): in a plan built from lone
boxes the canonical form of a set (determined by its non-hub part, which is what makes the moved
part lonely) forces all sets that collapse onto the same final set to use the same `r` hubs, so a
face of hubs is visited by every set of the family with a large non-hub part. Keeping loads small
therefore needs many small collapsing families, i.e. first routing the input into a structure whose
families are small (the analogue of the rook pairs of `OddGrid`, which keep links of size `O(√n)`).
Full boxes keep every proper face of the input set, so an input `(r-1)`-face stays present until it
becomes lonely; a construction must therefore make the `(r-1)`-faces of the input lonely (collapse
their links) with spread-out replacement vertices, then iterate on lower-dimensional faces. The
replacement choices are colouring problems (as `exists_kappa` / `greedy_color` for `r = 2`) whose
`r`-uniform versions, together with the halving schedule and the load accounting, are not done.

### Status of the pending items (updated)

3. **`NativeStrongMultiRefiners q r`, `r ≥ 3`.** Still open, now reduced to the purely
   combinatorial `RPlans q r` (`nativeStrongMultiRefiners_of_rPlans`); `RPlans q 2` is proved.

## Session: toward `RPlans q r` — segments, link lifting, emptying vertices (continuation)

All new files are in `RequestProject/HyperPlan/` (namespace `RefinedAbsorption.HyperPlan`). They are
proved without `sorry` and use only the standard axioms (`checks/AxiomCheck.lean`).
**`RPlans q r` for `r ≥ 3` is still open.** This session built the general machinery that any
construction of such plans needs; the plan with the required load bound was not found.

| Declaration | File | Content |
|---|---|---|
| `SegOKR`, `SegOKR.append`, `planOKR_of_segOKR`, `passSumR_append`, `passSumR_withStay` | `Segment.lean` | plans built from segments; validity and loads of concatenations; a valid segment preceded by one stage that keeps everything is a valid plan |
| `liftRoute`, **`routeOKR_liftRoute`**, **`allowedR_subset_link`**, `visitR_liftRoute` | `LinkLift.lean` | a route of uniformity `r - 1` (parameter `q - 1`) in the link of `u` lifts, with a twin `tw`, to a route of uniformity `r` (parameter `q`) that is valid for the same weights. Loneliness in the link may be used |
| `liftSeg`, `linkF_prunR_liftSeg`, **`segOKR_liftSeg`**, `passR_liftSeg_le`, `card_filter_mem_prunR_liftSeg` | `Empty.lean` | a whole segment on the link of one vertex `u` lifts to a valid segment; the link of `u` evolves exactly as the link segment |
| `moveSpec`, **`segOKR_move`**, `notMem_prunR_move`, `prunR_move` | `Empty.lean` | once `u` is lonely, one stage moves it to a new vertex |
| `liftSegU`, `liftSegU_inv`, **`segOKR_liftSegU`**, `passR_liftSegU_le`, `card_filter_mem_prunR_liftSegU` | `EmptyMany.lean` | the same for all vertices of a set `U` at once, provided no set contains two vertices of `U`; every `u ∈ U` has its own link segment and twins |
| `moveSpecU`, **`segOKR_moveU`**, `prunR_moveU_disjoint`, `prunR_moveU` | `EmptyMany.lean` | moving all lonely vertices of `U` in one stage; afterwards no set meets `U` |

*Why this is the right machinery (informal, partly formal).* A full box keeps every proper face of
the set it reroutes. A vertex `u` can therefore leave the family only through a move of a set in
which `u` is lonely (`segOKR_move` is the corresponding valid move). So emptying `u` means
collapsing its link to a single set. The link-lifting theorems show that this is exactly a problem
of uniformity `r - 1` with parameter `q - 1`, and that loneliness inside the link may be used.
Stages in which a set stays still load it (`passR` counts staying sets), so a plan with loads
`O(max(D, n^{1-1/r} log n))` must have `O(log n)` stages. This is why vertices have to be emptied in
parallel (`EmptyMany.lean`).

*Remarks on the missing construction (informal, not machine-checked).*

1. The budget of uniformity `r - 1` is smaller: `n^{1-1/(r-1)} < n^{1-1/r}`. Collapsing the link
   of a single vertex with an `(r-1)`-uniform plan therefore fits the `r`-uniform budget at the
   faces containing that vertex, which suggests an induction on `r`.
2. Merging every emptied vertex into a hub, i.e. pure compression, doubles degrees at each halving
   unless the family lives in a sparse structure. For `r = 2` this is the rook graph of `OddGrid`.
3. The input `(r-1)`-faces persist until they become lonely. A structure into which the input is
   routed in the first stages must therefore contain completions of arbitrary `(r-1)`-sets, or the
   input faces must be killed first. Coordinate structures on `[m]^r` that are closed under halving
   (collinear sets, sets with pairwise shared coordinates, sets in a common hyperplane) do not
   contain arbitrary faces. Routing the input into the "sum" structure `Σ_v v^c ≡ 0 (mod m)` gives
   first-stage loads of about `D n^{1-2/r}`, too large for big `D`.
4. Twins that depend only on the link set (`tw u t f = τ(f)`) merge the dumps `f ∪ {τ(f)}` of all
   emptied vertices, which sparsifies. Choosing `τ` through coarse classes of `f` is how the rook
   structure arises for `r = 2`. A uniformity-`r` version of this choice, together with the halving
   schedule and the load accounting, is what remains.

### Status of the pending items (updated)

3. **`NativeStrongMultiRefiners q r`, `r ≥ 3`.** Still open, reduced to `RPlans q r`. The
   combinatorial toolkit for building `r`-uniform plans (segments, link lifting, parallel emptying
   of vertices) is now formalized. The plan with the required load bound is not.

## Session: local plans, persistence of faces (continuation)

**`RPlans q r` for `r ≥ 3` is still open.** New files, proved without `sorry` and using only the
standard axioms (`checks/AxiomCheck.lean`):

| Declaration | File | Content |
|---|---|---|
| `LocalSpec`, `LocalList`, `rtR_local`, `prunR_mono_local` | `Mono.lean` | routes that ignore the current family; the present sets only shrink with the input |
| **`PlanOKR.mono_local`**, `SegOKR.mono_local`, `passSumR_mono_local`, `card_prunR_mono_local` | `Mono.lean` | a local plan valid on a structure is valid on each subfamily, with no larger loads or final family |
| **`route_covers_face`**, `face_persists`, **`face_persists_zero`**, `one_mem_allowedR_of_noLone` | `Persist.lean` | valid routes cover every face of size `< r` whenever weight `1` can occur; faces of input sets survive the first stage, and later disappear only through sets with a lone face |

*Further remarks on the missing construction (informal, not machine-checked).*

1. *Coordinate structures.* With `n = m³` points of `[m]³`, the triples in which one point shares a
   coordinate with each of the other two contain every box `J ∪ ρ(e \ J)` with
   `ρ(w) = (u₁, v₂, x)`, `ρ(u) = (v₁, w₂, x)`, `ρ(v) = (w₁, u₂, x)`. Their pair degrees are `O(m²)`.
   But the pairs `{u, ρ(w)}` visited by the first stage only use the `O(m²)` points sharing a
   coordinate with `u`, while about `D n` input sets contain `u`. So some such pair has load at
   least about `D n / m² = D n^{1/3}`, too large. Any first-stage structure must let the replacement
   points of the sets through `u` range over `Θ(n)` vertices.
2. *Sum structures.* For a potential `h : V → ℤ_m`, the sum `Σ_{v ∈ f} h(v)` is additive under
   boxes: the signed sum of `Σ_{v∈f} h(v)` over a box vanishes. So a set with nonzero potential sum can
   never be routed by boxes onto sets of zero sum, which is the "sum structure". Over `ℤ`, the class
   lattice also contains the complete `r`-graph `K_q^{(r)}`, so this obstruction only survives
   modulo `gcd(m, binom(q-1, r-1))`. Using it requires non-box routes built from copies of `K_q`.
3. *Random-like structures.* For a family `T` of density `n^{-1/r}` (pair degrees `n^{2/3}` for
   `r = 3`) the expected number of boxes of `e` lying entirely in `T` is `n^{3 - 7/3} = n^{2/3}`.
   So a first stage into a random-like structure is plausible. What is missing is a structure that is
   also compressible by halving, i.e. whose images under merging vertex classes are again structures
   of the same kind, together with the corresponding emptying schedule.

## Session: descent through windows (`RequestProject/Window/`)

The PDF supplied for this session is again the survey arXiv:2510.19978. The results cited in the
request (Theorem 3.8, Lemmas 3.12/3.13, the construction in §4.2) are not in it. In the survey,
Lemma 3.8 is the General Embedding Lemma, §3.4 is a one-paragraph sketch, and §4.2 is about
Nash-Williams. They presumably refer to the original Delcourt–Postle paper, which is not in the
project.

Proved without `sorry` (standard axioms only):

| Declaration | File | Content |
|---|---|---|
| `WindowStage` | `Window/Descent.lean` | one halving stage: load `Cst (D + a|U|)`, residue in a half window with `Δ_{r-1} ≤ Cst a|U|` |
| **`windowRefiner_of`**, `windowTop_of` | `Window/Descent.lean` | descent through `≤ log₂ n + 1` windows; budget `A D + K (log₂ n + 1) a(n)` |
| **`nativeStrongMultiRefiners_of_windowStage`**, `refinerAbsorbersFor_of_windowStage` | `Window/Native.lean` | `WindowStage` with `a m = ⌈m^{1-1/r}⌉` gives the exact budget `C max(D, n^{1-1/r} log n)` |
| `windowStage_id_of_stagePropE`, `windowStage_id_of_levelsE`, **`windowStage_id_two`**, **`windowStage_id_three`** | `Window/Linear.lean` | the existing stage is a window stage with linear cost `a m = m` (unconditional for `r ≤ 3`) |

This reduction works with refinement families and their loads (`IsResidualMultiRefiner`, `mdeg`,
`pdeg`). It does not go through the typed plans of `HyperPlan/`, so no translation of loads between
the two settings is needed.

### Status of the pending items (updated)

3. **`NativeStrongMultiRefiners q r`, `r ≥ 3`.** Still open. It is now reduced to
   `WindowStage q r Cst m₀ (winCost r)`, a single window stage with cost `⌈m^{1-1/r}⌉`, or
   alternatively to `RPlans q r`. The same stage with linear cost is proved for `r ≤ 3`. The
   sublinear cost requires the spreading of links over about `n^{(r-1)/r}` classes and the
   inductive link refiners of Delcourt–Postle. Neither is in the available sources, and neither
   is formalized.

## Session: Edge Sparsification (Lemma 3.12) and Theorem 3.8 up to the link levels (`RequestProject/Sharp/`)

The source is the paper arXiv:2402.17855, which the user supplied in this session. Proved without
`sorry` (standard axioms only):

| Declaration | File | Content |
|---|---|---|
| `windowRefiner_pot`, `windowTop_pot`, `sharpCost`, `sharpPot_le`, `WindowStageM`, **`nativeStrongMultiRefiners_of_windowStageM_sharp`** | `Sharp/Descent.lean` | descent through windows with cost `sharpCost r m = ⌈m^{1-1/r}⌉(⌊log₂ m⌋+1)`; the total is `≤ 30 n^{1-1/r} log n` |
| `EdgeSparsification` (def), **`windowStage_of_sparsify_levels`** (Lemma 3.14), **`nativeStrongMultiRefiners_of_sparsify_levels`** | `Sharp/Better.lean` | Better Refine Down; Theorem 3.8 from 3.12 plus the link levels |
| `cliqueR`, `cliqueW`, **`cliqueRefiner_residual`**, `mdeg_cliqueR_le`, `pdeg_cliqueW_le` | `Sharp/CliqueRefiner.lean` | the private-clique refiner `R₁` (`binom(q,r)`-refined) |
| `ptype`, `sClique`, `spreadSet`, **`card_clique_supersets_le`**, **`card_clique_link_le`** | `Sharp/SparsCount.lean` | the counting of `Δ(R₁)` and of the link of the remainder |
| **`exists_special_sets`** | `Sharp/Special.lean` | Lemma 3.19 (special sets) |
| **`exists_partition`** | `Sharp/Partition.lean` | Proposition 3.17 (quasi-random partition) |
| `pow_le_winCost_pow`, `winCost_pow_le`, `pow_le_choose_half`, **`partition_union_bound`**, `spread_term_le`, `link_term_le`, `spreadBound_le` | `Sharp/SparsArith.lean` | the parameter inequalities of the proof of 3.12 |
| **`sparsify_build`** | `Sharp/SparsBuild.lean` | `R₁` + Multiplicity Reduction, with degree bounds in terms of the counting quantities |
| **`edgeSparsification_holds`** (Lemma 3.12), **`nativeStrongMultiRefiners_of_levels`**, `nativeStrongMultiRefiners_two_sharp` | `Sharp/Sparsify.lean` | Lemma 3.12, and Theorem 3.8 reduced to the link levels |

Choice of parameters in `edgeSparsification_holds`, with `m = |U|`:
* `k = w = ⌈m^{1-1/r}⌉` parts;
* `D* = D + 4 M₀ (r+1) w (⌊log₂ m⌋+1)`;
* `P = ⌊2m/w⌋` and `Q = ⌊2D*/w⌋`;
* spread bounds `B 0 = w` and `B ℓ = ⌊r 2^r w^{ℓ+1} binom(q-r,ℓ)² / binom(⌊m/2⌋,ℓ)⌋ + 1`, so that
  `B ℓ m^ℓ ≤ K₀ w^{ℓ+1}`;
* `m₀ = 4·64^r (2r)! + (4r)^r + 8r + 2q`.

The two consequences are:
* the residue has `Δ ≤ M' 2^r K₀ (q + 2r) w`, with no dependence on `D`;
* the new copies and pieces have `Δ ≤ Cst (D + sharpCost r m)`.

### Status of the pending items (updated)

3. **`NativeStrongMultiRefiners q r`, `r ≥ 3`.** This is now reduced to the single family of link
   levels `PlacedLinkLevelA q r i (sharpCost r)` for `1 ≤ i < r - 1`
   (`nativeStrongMultiRefiners_of_levels`); Lemmas 3.12 and 3.14 are proved. The missing piece is
   §4 of the paper: the Local Multi-Refiner Theorem 4.4, built from the sharp theorem in uniformity
   `r - i`, and the random embedding of Lemma 4.1. The levels are proved with additive term `ε|Z|`
   (`PlacedLinkLevelE`), but not with the sublinear term.

## Session: §4 for `3`-graphs (`RequestProject/Local/`)

Proved without `sorry` (standard axioms only):

| Declaration | File | Content |
|---|---|---|
| `exp_le_one_add_mul`, `sum_exp_le`, **`card_sum_ge_le`**, `exists_good_choice` | `Local/Chernoff.lean` | Chernoff bound (counting form) and union bound |
| `AffG`, `affMap`, `card_aff_eq_le`, `card_aff_eq₂_le`, `movedLoad`, `sum_movedLoad_le`, **`exists_affine_spread`** | `Local/Affine.lean` | random affine embedding, probabilistic core of Lemma 4.1 |
| `taggedStep_of_level`, `taggedChain0`, **`taggedStage0`** | `Local/StageZero.lean` | tagged stage without additive term |
| `TStageOut.prepend'` | `Local/Prepend.lean` | prepending a tagged stage |
| `TaggedLinkRefinersA` (def), **`placedLinkLevelA_of_taggedA`** | `Local/TaggedA.lean` | link levels with additive term from tagged refiners |
| `locLab`, **`trefOut_of_local`** | `Local/LocalAssembly.lean` | assembly of independent local refiners |
| `FlatGraphRefiners` (def), `exists_prime_emb`, `log_sq_add_one_le_sharpCost`, `lifted_count_le`, … | `Local/FlatEmbed.lean` | input from uniformity 2 and counting tools |
| `mult_image_le`, `sys_deg_le`, `sys_codeg_le`, `spread_bound_le`, **`flatEmbedTagged`** | `Local/FlatEmbedMain.lean` | Lemma 4.1 for `r = 3`, level 1 |
| `taggedLinkRefinersA_three_one`, **`placedLinkLevelA_three_one`**, **`nativeStrongMultiRefiners_three_of_flat`** | `Local/LevelOneSharp.lean` | level 1 with term `sharpCost 3`; Theorem 3.8 for `r = 3` from `FlatGraphRefiners` |
| `FlatCliqueOmniAbsorbers` (def), `card_pieces_through_le`, **`flatGraphRefiners_of_cliqueOmni`**, `sharpCost_two_le_three`, **`nativeStrongMultiRefiners_three_of_cliqueOmni(_two)`** | `Local/CliqueOmni.lean` | Theorem 3.8 for `r = 3` from Theorem 3.7 for graphs (flat, clique pieces) |

### Status of the pending items (updated)

3. **`NativeStrongMultiRefiners q 3`.** This is proved assuming `FlatCliqueOmniAbsorbers (q-1) (sharpCost 2)`,
   which is Theorem 3.7 for graphs in local form, with flatness and clique pieces. That input is not
   proved in this project.
   **`r ≥ 4`**: the levels `2 ≤ i < r - 1` (`TaggedLinkRefinersE`, `PlacedLinkLevelA`) are still
   open. The random embedding generalizes. The tagged stage without additive term (`taggedStage0`)
   needs the exact levels `j > i`, and those are known only for `j = r - 1`.

## Session: Theorem 3.7 for graphs and Theorem 3.8 for `3`-graphs (`FlatOmni/`, `SparseChain/`)

Proved without `sorry`, using only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Declaration | File | Content |
|---|---|---|
| `multiStageK` | `FlatOmni/StageK.lean` | refine-down stage with `|U| ≤ K₀ |Z|` |
| `windowStage_of_sparsify_levels_ge`, `windowStageM_two_ge` | `FlatOmni/WindowGe.lean` | window stage for any multiplicity bound |
| `LocalOut`, `localDescent` | `FlatOmni/Descent.lean` | window descent inside `P` |
| **`localRefiner`** | `FlatOmni/LocalRefiner.lean` | local refiner in `Y ∪ P`, degrees `≤ C (D + sharpPot 2 |P|)` |
| `fakePiece`, `fakePiece_refiner`, `rootDensity_two`, **`fakeStage`** | `FlatOmni/Fakes.lean` | new copies replaced by simple fake edges placed in `P` |
| `AbsData`, `cliqueFam`, **`cliquePieces_refiner`** | `FlatOmni/CliquePieces.lean` | clique pieces from attached absorbers (Remark 3.9) |
| **`absStage`** | `FlatOmni/Attach.lean` | bounded absorbers for all pieces, placed in `P` |
| `sharpPot_two_le`, `exists_mul_sharpPot_le` | `FlatOmni/SharpBounds.lean` | `sharpPot 2 ≤ 6 sharpCost 2`; `c · sharpPot r m ≤ m` eventually |
| `FlatCliqueOmniAbsorbersS` (def), `FlatCliqueOmniAbsorbers.toS`, **`flatCliqueOmniAbsorbersS_two`** | `FlatOmni/Assembly.lean` | **Theorem 3.7 for graphs** (flatness, clique pieces, `Δ ≤ |P|/C`) |
| `FlatGraphRefinersS` (def), `flatGraphRefinersS_of_cliqueOmniS`, `flatEmbedTaggedS` | `SparseChain/FlatEmbedS.lean` | sparse flat local refiners and their random embedding |
| `PlacedLinkLevelS`, `TaggedLinkRefinersS` (defs), `PlacedLinkLevelA.toS`, `PlacedLinkLevel.toS`, `placedStep_of_levelS`, `placedChainS`, `placedLinkLevelS_of_taggedS` | `SparseChain/Levels.lean` | sparse link levels and chain |
| `multiStageS` | `SparseChain/StageS.lean` | sparse refine-down stage |
| `windowStage_of_sparsify_levelsS`, **`nativeStrongMultiRefiners_of_levelsS`** | `SparseChain/WindowS.lean` | Theorem 3.8 (any `r`) from sparse levels |
| `taggedLinkRefinersS_three_one`, `placedLinkLevelS_three_one`, **`nativeStrongMultiRefiners_three`** | `SparseChain/ThreeGraphs.lean` | **Theorem 3.8 for `r = 3`, unconditional** |

### Status of the pending items (updated)

1. **Theorem 3.7 for graphs (flat, clique pieces).** Proved in the form with the paper's
   hypothesis `Δ ≤ n/C` (`flatCliqueOmniAbsorbersS_two`). The version without this hypothesis
   (`FlatCliqueOmniAbsorbers`) is not proved. When `d` is comparable with `|P|`, the construction
   used here does not apply, because it places simple fake edges and absorbers inside `P`.
2. **`NativeStrongMultiRefiners q 3`.** Proved unconditionally (`nativeStrongMultiRefiners_three`),
   via the sparse chain. Only the sparse levels are needed, because the window stage applies the
   levels after edge sparsification.
3. **`r ≥ 4`.** `TaggedLinkRefinersE q r i` and `PlacedLinkLevelA q r i` for `2 ≤ i < r - 1` are
   still open, and so are their sparse forms. Theorem 3.8 for `r ≥ 4` is reduced to the sparse
   levels `PlacedLinkLevelS q r i (sharpCost r)`, `1 ≤ i < r - 1`
   (`nativeStrongMultiRefiners_of_levelsS`).

## Session: all uniformities (`RequestProject/General/`, `RequestProject/Final.lean`)

Proved without `sorry`, standard axioms only:

| Declaration | File | Content |
|---|---|---|
| `FlatOmniK` (def), `flatOmniK_of_levels` | `General/Defs.lean`, `General/FlatOmniK.lean` | Theorem 3.7 in uniformity `k` (flat, clique pieces) from the lower levels |
| `flatEmbedGen` | `General/EmbedGen.lean` | Lemma 4.1 for outer parts of size `i` |
| `taggedStage0S` | `General/StageS.lean` | sparse tagged stage |
| `taggedLinkRefinersS_gen`, **`placedLinkLevelS_all`**, **`nativeStrongMultiRefiners_all`**, **`steinerExistence`** | `General/Levels.lean` | all link levels; Theorem 3.8 for all `q > r ≥ 2`; Existence Conjecture for Steiner systems |
| `theorem_3_8`, `refinerWithAbsorbers_holds`, **`theorem_1_10`**, `theorem_1_7`, `lemma_2_2`, `corollary_2_4`, **`existenceConjecture_steiner`**, `kirkman` | `Final.lean` | the survey's results, unconditionally |

### Status of the pending items (final)

All pending items of the refined absorption proof are closed. `RefinerWithAbsorbers`,
`RefinedEfficientOmniAbsorber` (Theorem 1.10), `NibbleWithReserves` (Corollary 2.4) and
`SteinerExistenceConjecture` are proved. Not covered: `ExistenceConjecture` for `λ > 1`, and the
conjectures of the applications sections (only stated).

## Session: survey Lemma 2.1 and corollaries (`SurveyReserves.lean`, `SurveyCorollaries.lean`)

| Lean | Content |
| --- | --- |
| `lower_tail_frac` | lower tail `P(f ≤ E f - t) ≤ exp(-t²/(4pMT1))` for bounded differences |
| `card_cliquesThrough_complete` | `binom(n-r, q-r)` cliques of `K_n^r` through an edge |
| **`reservesLemma`** | **Lemma 2.1 (Reserves) exactly as stated**, `γ = 1/(4 binom(q,r))` |
| `Final.theorem_1_8` | Theorem 1.8 (efficient omni-absorbers) |
| `Final.existenceConjecture_steiner_section2` | Section 2 with every ingredient proved |
| `Final.existenceConjecture` | Conjecture 1.1 for every `λ ≥ 1` |

Not formalized: the general Theorem 1.3 (nibble for designs, with no bound on the number of
vertices in terms of `D`; the project proves the bounded version `nearRegularNibble` and
Corollary 2.4), and the survey's Lemma 3.8 (general embedding with supergraph systems; the
project uses the article's Lemma 5.2 instead).  The applications sections (4–6) are only stated.

## Final continuation: the two remaining items

| Declaration | File | Status |
|---|---|---|
| `nibbleForDesigns : NibbleForDesigns` (Theorem 1.3, no bound on `n`) | `NibbleDesigns.lean` | proved |
| `localNibble : LocalNibble` (local nibble via the Lovász Local Lemma) | `Nibble/LocalMain.lean` | proved |
| `generalEmbeddingLemma : GeneralEmbeddingLemma` (Lemma 3.8) | `GeneralEmbedding/Main.lean` | proved |

Axioms: `checks/PendingAxioms.lean` (only `propext`, `Classical.choice`, `Quot.sound`).

## Extensions (new theorems beyond the survey)

Proved, no `sorry`, standard axioms only (`checks/ExtensionsAxioms.lean`):

* `RefinedAbsorption.Extensions.partialSteiner_completion` — completion of sparse partial Steiner systems.
* `RefinedAbsorption.Extensions.partialSteiner_embedding` / `partialSteiner_embeds` — finite embedding theorem for partial Steiner systems.
* `RefinedAbsorption.Extensions.log_card_steinerSystems_theta` — `log #S(n,q,r) = Θ(n^r log n)`.
* `RefinedAbsorption.Extensions.steiner_extends_subsystem` / `steiner_with_subsystem` — Steiner systems with prescribed subsystems.

Assumptions: none beyond the project's proved Theorem 6.1 (`theorem_6_1`) and the Existence Conjecture for Steiner systems (`theorem_1_1_steiner`).

## Extensions, second round (combination with classical results)

Proved, no `sorry`, standard axioms only (`checks/ExtensionsAxioms.lean`):

* `optimal_packing`, `optimal_packing_count` (`Extensions/Packing.lean`) — for every large `n`, a `K_q^r`-packing of `K_n^r` with leftover of bounded `(r-1)`-degree; unconditional.
* `optimal_covering` (`Extensions/Packing.lean`) — coverings with `binom(q,r)|𝒞| ≤ binom(n,r) + K n^{r-1}`; unconditional.
* `packing_leftover_lower`, `covering_excess_lower` (`Extensions/Packing.lean`) — the order `n^{r-1}` is best possible when `q - r + 1 ∤ n - r + 1`; elementary.
* `steiner_almost_resolvable`, `exists_almost_resolvable_steiner`, `resolution_classes_lower` (`Extensions/AlmostResolvable.lean`) — asymptotically resolvable Steiner systems. **Conditional** on the Pippenger–Spencer theorem, stated as the hypothesis `PippengerSpencer` (external classical input, not proved).
