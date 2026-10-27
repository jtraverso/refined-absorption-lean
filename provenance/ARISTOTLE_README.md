# Formalization of "Refined Absorption" (L. Postle, arXiv:2510.19978)

Lean 4 / Mathlib formalization of the definitions, statements and the elementary parts of the
survey *Refined Absorption: A New Proof of the Existence Conjecture and its Applications to
Extremal and Probabilistic Design Theory*.

| File | Content |
| --- | --- |
| `RequestProject/Basic.lean` | `r`-graphs, degrees, `K_q^r`-divisibility, packings, decompositions (Sec. 1.3) |
| `RequestProject/Counting.lean` | double counting; decompositions ⇒ divisibility; integral (Def. 3.1) and fractional decompositions |
| `RequestProject/Designs.lean` | designs, Steiner systems, necessity of the divisibility conditions, `r = 1` case, Fano plane |
| `RequestProject/Absorbers.lean` | absorbers, omni-absorbers, `C`-refined, boosters, refiners (Defs. 1.5, 1.6, 1.9, 1.11, 3.5); absorption step; booster exchange |
| `RequestProject/MultiAbsorber.lean` | multi-absorbers ⇔ integral decompositions (Sec. 3.1); Graver–Jurkat–Wilson ⇒ multi-absorbers |
| `RequestProject/Statements.lean` | precise statements (as `Prop`s, not proved) of the cited deep theorems and conjectures; proved implications between them |
| `RequestProject/ExistenceProof.lean` | the refined absorption proof of the Existence Conjecture (Section 2) for Steiner systems: all steps proved, assuming the reserves lemma, Theorem 1.10, the boost lemma and the nibble with reserves (`steinerExistence_of_refinedAbsorption`) |
| `RequestProject/Reserves.lean` | an explicit construction of reserves proving the form of Lemma 2.1 used in the proof (`weakReservesLemma`); hence the Existence Conjecture for Steiner systems follows from Theorem 1.10, Lemma 2.2 and Corollary 2.4 alone (`steinerExistence_of_omniAbsorber_boost_nibble`) |
| `RequestProject/BeckFiala.lean` | Beck–Fiala iterated rounding: a fractional point of `[0,1]^α` rounds to a `0/1` point changing every set sum by at most `t` when each point lies in at most `t` sets (`beck_fiala`) |
| `RequestProject/Gadget.lean` | edge gadgets: weights on the `q`-subsets of `e ∪ W` loading exactly the edge `e` (`gadget_sum`) |
| `RequestProject/Boost.lean` | **proof of Lemma 2.2 (boost)** (`boostLemma`), even with constant error `binom(q,r)` (`exists_boost_const_error`): exact fractional boost via gadgets (`fracWeight_spec`), then Beck–Fiala rounding |
| `RequestProject/BoostExistence.lean` | the Existence Conjecture for Steiner systems from Theorem 1.10 and Corollary 2.4 **exactly as stated in the survey** (`steinerExistence_of_omniAbsorber_nibbleWithReserves`) |
| `RequestProject/ReserveCover.lean` | **covering a leftover with reserves** (`reserve_cover`): if the leftover `L` has `Δ_{r-1}(L) ≤ n^{1-γ}` and every edge of `L` has at least `n^{q-r-α}` reserve cliques in `X ∪ {e}` (`2αr ≤ γ`), the edges of `L` can be covered by edge-disjoint reserve cliques; deterministic greedy proof |
| `RequestProject/NibbleReserves.lean` | **Corollary 2.4 from the nibble with leftover degree control** (`nibbleWithReserves_of_nibbleLeftoverDegree`, and the general-error form `nibbleWithReservesGen_of_nibbleLeftoverDegree`); statement `NibbleLeftoverDegree` |
| `RequestProject/OmniFromRefiner.lean` | refined refiners (`IsRefinedRefiner`) and attached absorbers (`IsAttachedAbsorbers`); **refined refiner + attached absorbers ⇒ `2C`-refined omni-absorber** (`omniAbsorber_of_refiner_absorbers`); Theorem 1.10 from `RefinerWithAbsorbers` (`refinedEfficientOmniAbsorber_of_refinerWithAbsorbers`); final theorem `steinerExistence_of_refinerWithAbsorbers_nibbleLeftoverDegree` |
| `RequestProject/WeightedNibbleBridge.lean` | **`NibbleLeftoverDegree` from the weighted pseudorandom matching theorem** (Ehard–Glock–Joos Thm 1.2, stated as `EGJWeightedMatching`): `nibbleLeftoverDegree_of_egjWeightedMatching`; hence Corollary 2.4 (`nibbleWithReserves_of_egjWeightedMatching`) and `steinerExistence_of_refinerWithAbsorbers_egjWeightedMatching` |
| `RequestProject/Kirkman.lean` | Kirkman's theorem: Steiner triple systems exist iff `n ≡ 1, 3 (mod 6)` (Bose and Skolem constructions) |

## Final status

`RequestProject/Final.lean` proves, with no hypotheses and only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`):

| Declaration | Result of the survey |
| --- | --- |
| `Final.theorem_3_8` | Theorem 3.8 (Multi-Refiner Theorem), every `q > r ≥ 2` |
| `Final.theorem_1_10` | Theorem 1.10 (refined efficient omni-absorber) |
| `Final.theorem_1_7` | Theorem 1.7 (existence of absorbers) |
| `Final.lemma_2_2` | Lemma 2.2 (boost) |
| `Final.corollary_2_4` | Corollary 2.4 (nibble with reserves), as stated in the survey |
| `Final.existenceConjecture_steiner` | the Existence Conjecture for Steiner systems (`λ = 1`) |
| `Final.kirkman` | Kirkman's theorem |

The last missing piece, the link levels `2 ≤ i < r - 1` for `r ≥ 4`, is in
`RequestProject/General/` (see the last section below).

### Designs with `λ ≥ 1` (multigraph versions)

| Declaration | File | Result |
| --- | --- | --- |
| `NibbleWithReservesMulti`, `nibbleWithReservesMulti_proved` | `Multigraph/NibbleMulti.lean` | **Corollary 2.4 for multigraphs**: for a multigraph given by layers `G 0, …, G (m-1)` (which may overlap each other and the reserves), with clique families `H j` of degrees `(ρ ± n^{-β}) binom(n, q-r)` and reserves `X`, there is a *set* of distinct cliques, avoiding a prescribed family `Φ` of bounded multiplicity, covering every `r`-set `T` exactly `#{j : T ∈ G j}` times, plus at most once more if `T ∈ X` |
| `nibbleWithReservesGen_of_multi` | `Multigraph/NibbleMulti.lean` | the case `m = 1`, `Φ = ∅` is Corollary 2.4 of the survey |
| `existenceConjecture_proved` | `Multigraph/Existence.lean` | **the Existence Conjecture (Conjecture 1.1) for every `λ ≥ 1`**, exactly as stated in `Statements.lean` (`ExistenceConjecture`), with simple designs (no repeated blocks) |

Ingredients: the nibble with leftover control now also returns a packing inside the given clique
family (`nibbleLeftoverDegreeSub_proved`, `Nibble/Bridge.lean`); the digit-sum reserves have many
reserve cliques through *every* `r`-set (`strongReservesLemma`, `Multigraph/StrongReserves.lean`);
the greedy reserve cover works for layered leftovers and avoids forbidden cliques
(`reserve_cover_multi`, `Multigraph/ReserveCoverMulti.lean`).

Proof of the `λ`-version: reserves `X`, the refined omni-absorber `A` of Theorem 1.10 (the
`λ = 1` theorem suffices) and its cliques `F'`; the multigraph `λK_n^r − (A ∪ X)` is written as
the layer `J = K_n^r \ (A ∪ X)` plus `λ - 1` copies of `K_n^r`, each with a boosted clique family;
Corollary 2.4 for multigraphs, avoiding `F'`, covers it, using each edge of `X` at most once more;
the remaining edges `L ⊆ X` are divisible by double counting (`isDivisible_of_count`) and are
absorbed by `A`.

### Applications sections

The conjectures and cited theorems of Sections 4–6 are stated in `Statements.lean`; their proofs
are separate research papers (Kwan–Sah–Sawhney–Simkin, Delcourt–Postle, Delcourt–Henderson–
Lesgourgues–Postle, …) and are not formalised.  `RequestProject/Applications.lean` proves the
cases that follow from the Existence Conjecture:

* `IsDecomposition.hasGirthAtLeast_three`: every `K_q^r`-decomposition has girth at least `3`;
* `IsDecomposition.hasGirthAtLeast_four`: every `K_q^2`-decomposition has girth at least `4`;
* `highGirthExistence_small`: Conjecture 5.3 for `g = 3`, and for `g ≤ 4` when `r = 2`;
* `erdosHighGirth_small`: Erdős' Conjecture 5.1 for `g ≤ 4`.

The sections below record the history of the project. Statements in them that say a result is
"open" or "not proved" describe the state at that point and are superseded by this section.

Everything builds without `sorry`; the statements in `Statements.lean` are definitions of
propositions, not proved results.  Of the ingredients of Section 2, the reserves (in the form
used) and the boost lemma (Lemma 2.2) are proved; the main theorem
`steinerExistence_of_omniAbsorber_nibbleWithReserves` takes only the two remaining deep cited
results, Theorem 1.10 (`RefinedEfficientOmniAbsorber`) and Corollary 2.4 (`NibbleWithReserves`,
as stated in the survey), as hypotheses.

### Progress on Theorem 1.10 and Corollary 2.4

Both remain unproved, but each is now reduced, by fully proved deterministic arguments, to a
more basic statement:

* **Corollary 2.4.**  The classical nibble (Theorem 1.3) only bounds the *number* of uncovered
  edges; these could all contain one `(r-1)`-set and exhaust its reserves.  We state the standard
  stronger form of the nibble in which every `(r-1)`-set lies in at most `n^{1-γ}` uncovered
  edges (`NibbleLeftoverDegree`), and prove that it implies Corollary 2.4 exactly as stated in the
  survey.  The leftover is covered with the reserves by a deterministic greedy algorithm
  (`reserve_cover`): each leftover edge gets a reserve clique that avoids the *heavy* sets,
  i.e. sets `S ⊄ e` with `|S| ≤ r` already lying in at least `⌈n^{(r-|S|)(1-2α)}⌉` chosen
  cliques, and a double counting argument shows that a suitable clique always exists.
* **Theorem 1.10.**  The deterministic final step of its proof is formalised: a `C`-refined
  refiner `R` of `X` (a fixed family `𝒲` of `K_q^r`-divisible subgraphs of `X ∪ R`, each of
  size at most `C`, every edge in at most `C` of them, such that `R ∪ L` splits into members of
  `𝒲` for every divisible `L ⊆ X`) together with pairwise edge-disjoint absorbers `A_W`
  attached to the members of `𝒲` gives the `2C`-refined omni-absorber `R ∪ ⋃ A_W`.  Hence
  Theorem 1.10 follows from the existence of such refiners and absorbers with the right
  maximum degree (`RefinerWithAbsorbers`, our formulation of the two constructive steps of the
  Delcourt–Postle proof; it is stated, not proved).

So the Existence Conjecture for Steiner systems is proved from `RefinerWithAbsorbers` and
`NibbleLeftoverDegree` (`steinerExistence_of_refinerWithAbsorbers_nibbleLeftoverDegree`).

* **Weighted nibble bridge.**  `NibbleLeftoverDegree` is in turn proved from the weighted
  pseudorandom hypergraph matching theorem of Ehard, Glock and Joos (Theorem 1.2), stated as
  `EGJWeightedMatching` (`RequestProject/WeightedNibbleBridge.lean`).  The theorem is applied
  to the auxiliary hypergraph whose vertices are the `r`-sets and whose edges are clique edge
  sets, with one test weight per `(r-1)`-set.  Hence Corollary 2.4 follows from
  `EGJWeightedMatching` alone, and the Existence Conjecture for Steiner systems from
  `RefinerWithAbsorbers` and `EGJWeightedMatching`
  (`steinerExistence_of_refinerWithAbsorbers_egjWeightedMatching`).

`EGJWeightedMatching` and `RefinerWithAbsorbers` are stated, not proved here.  See `LEDGER.md`
for a ledger of proved results versus assumptions, and for notes on the survey's statements
behind `RefinerWithAbsorbers`.

The case `λ > 1` of the Existence Conjecture is not covered: the argument of Section 2 (and the
statements of Theorem 1.10 and Corollary 2.4 given in the survey) concern `K_q^r`-decompositions
of the simple `r`-graph `K_n^r`, i.e. Steiner systems.  A `λ`-fold design is a decomposition of
the multi-hypergraph `λK_n^r` into distinct cliques, which would need multigraph versions of
these two theorems.

### Placed refine-down rounds

`RequestProject/RefineDown/Round.lean` proves `placedRound`. It is one anti-edge round of the
refine-down construction, with all new vertices placed inside the same `Fin n` by the Partial
Clique Embedding Lemma. The output is a residual multi-refiner with these properties:
divisible residue, bounded pieces, controlled multiplicities, `Δ_{r-1} ≤ C·D`, controlled piece
vertex sets, the original copies kept, and a simple residue.

`RequestProject/RefineDown/Iterate.lean` chains such rounds (`IterSpec.trans`, `placedRounds`).
The native refiner `NativeStrongMultiRefiners` is still open, because the decreasing rounds of
the paper are not formalized; see `LEDGER.md`.

### Flat refine-down and empty residue

`RequestProject/FlatDown/` formalizes the induction on uniformity of the refine-down argument.
The key results are:

* `flatStep`: the reduction from `i`-flat to `(i-1)`-flat with respect to a reserve.
* `flatDown`: iterating `flatStep` down to an empty residue.
* `multiRefiner_exists`: every finite `r`-multigraph has a `K_q^r`-multi-refiner with
  **empty residue**, with a constant depending only on `q` and `r`. This holds in the abstract
  multigraph setting, with a reserve of `q + r` vertices.

The degree-controlled version in `Fin n` (`NativeStrongMultiRefiners`) is still open; see
`LEDGER.md`.

### Reserves, multiplicity reduction and long chains

Results proved without `sorry` in the latest session:

* `RequestProject/Placement/ReserveLemma52.lean`: `reserveCliqueEmbedding` is the Partial Clique
  Embedding Lemma with all auxiliary vertices placed inside a prescribed reserve `Z ⊆ Fin n`.
  All counting is relative to `|Z|`. It also bounds how many gadget vertex sets contain each
  `(r-1)`-set.
* `RequestProject/RefineDown/ReserveRound.lean`: `placedReserveRound` is one anti-edge round with
  its new vertices placed inside `Z`. Every new copy meets `Z`, so the residue is
  `(r-1)`-flat with respect to the reserve.
* `RequestProject/FlatDown/MultDegree.lean`: `multiplicityReduction_quant` is the quantitative
  Multiplicity Reduction Lemma. The residue has multiplicity at most `M` on every `r`-set, and
  `mdeg R ≤ (M+2)^2 · mdeg X`.
* `RequestProject/MultiRefiner/Chain.lean`: `IsChainRefiner.trans` chains any number of stages
  with a uniform refinement constant, provided each stage's residue consists of its own new
  copies.
* `flatStep` now allows the completion support `Z₀ T W` to depend on the lifted piece.

`NativeStrongMultiRefiners` is still open; see `LEDGER.md`.

### Degree-controlled flat step in `Fin n`

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`):

* `RequestProject/FlatDown/FlatProof.lean`: `flatStep_struct` is `flatStep` with an explicit
  description of the new copies. Each one is either a lifted copy of a link refiner or a
  completion copy of a lifted piece. `flatStep` is now a corollary of it.
* `RequestProject/FlatDown/FlatDegree.lean`: `flatStep_deg` is the degree bookkeeping of one flat
  step. The degree of every set `S` in the new copies is at most its degree in the lifted link
  refiners, plus `(M+1)·K` times the number of lifted pieces `(T, W)` whose span
  `T ∪ Z₀ T W ∪ V(W)` contains `S`.
* `RequestProject/FlatDown/LinkAccounting.lean`:
  * empty pieces can be removed from refiners (`filter_nonempty`);
  * `linkSum_le` and `flatRoots_count_le` reduce both terms to quantities of the individual
    link refiners: degrees of `S ∩ Z`, and pieces whose vertex set contains `J ∩ Z`, summed over
    the outside parts `T ⊇ S \ Z`.
* `RequestProject/Placement/PlacedFlat.lean`: `placedFlatStep` and `placedFlatStep_link` place the
  completion supports `Z₀ T W` with the Partial Clique Embedding Lemma inside the reserve. The
  hypothesis is that the lifted pieces are not too dense compared to `Z`, and `Cs·D ≤ |Z|`.
  Then every `(r-1)`-set `S` has degree at most
  `∑_{T ⊇ S \ Z} mdeg(RN T, S ∩ Z) + Cs'·D` in the new copies.

`NativeStrongMultiRefiners` is still open. What remains is to construct the link refiners in
lower uniformity with the degree, multiplicity and density bounds that `placedFlatStep_link`
takes as hypotheses, and then to chain the levels. See `LEDGER.md`.

### Link refiners in the reserve and chaining of levels

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`):

* `RequestProject/FlatDown/ChainLink.lean`: `chainLink_refiner` gives chain refiners for
  `1`-uniform links. Their connecting copies sit at arbitrary pivots `p_i`.
* `RequestProject/Placement/Balance.lean`: `greedy_balance` is a greedy choice of pivots in `Z`
  with bounded loads.
* `RequestProject/Placement/LastFlat.lean`: `placedLastFlatStep` is the step from `(r-1)`-flat to
  `(r-2)`-flat in `Fin n` with **no** hypothesis on link refiners. The `1`-uniform links are
  refined by chain refiners whose pivots are spread over `Z`.
* `RequestProject/Placement/ChainLevels.lean`:
  * `PlacedLinkLevel q r i` packages, at level `i`, the three bounds that `placedFlatStep_link`
    needs: piece density, the `(r-i-1)`-degrees, and the spread multiplicities of the `(r-i)`-sets.
    The last two are combined into one sum.
  * `placedLinkLevel_last` proves this package for `i = r - 1`.
  * `placedStep_of_level` turns one level into a degree-controlled flat step.
  * `placedChain` chains the levels `j, …, 1`. The residue ends up inside `Z`, and the new copies
    have degree `≤ C·D`.
  * `placedIntoReserve` is "Refine Down into the reserve": the anti-edge round, followed by the
    chain.
  * For `r = 2` both results are unconditional: `placedChain_two` and `placedIntoReserve_two`.

Still open (see `LEDGER.md`):
* `PlacedLinkLevel q r i` for `1 ≤ i < r - 1`, which is needed for `r ≥ 3`.
* The global budget of Theorem 1.10, i.e. iterating reserves with Multiplicity Reduction down to
  constant size. Hence `NativeStrongMultiRefiners` is still not proved.

### Dense step, `o(n)`-budget refiners and Steiner systems

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`):

* `RequestProject/Placement/MultiEmbed.lean`: `multiCliqueEmbedding` places gadgets in the reserve
  `Z` while allowing parallel new edges. It needs only `C ≤ |Z|`, with no upper bound on the input
  degree `D`. This removes the hypothesis `Cs·D ≤ |Z|`, which blocked placing a dense residue
  (degree `≈ M·|Z|`) into a smaller reserve. `placedFlatStep(_link)`, `placedLastFlatStep`,
  `PlacedLinkLevel`, `placedStep_of_level`, `placedChain` and `placedChain_two` now only need
  `Cs ≤ |Z|`.
* `RequestProject/RefineDown/RoundGadgetGen.lean`, `RefineDown/MultiRound.lean`: the anti-edge
  round into a reserve for arbitrary `D` (`Gen.multiRound`).
* `RequestProject/Dense/`: one stage is round + chain of flat levels + Multiplicity Reduction
  (`multiStage`). Stages are iterated through reserves of size `n/4^k` (`denseRefiner_of`,
  `stagedRefiner_of`, `stagedRefiner`, `topRefiner`).
* `NativeWeakStrongMultiRefiners q r` (`Dense/Native.lean`) is strong multi-refiners with an
  `o(n)` budget: `2^t·Bd ≤ 2^t·C_t·D + B·n` for every `t`. **`nativeWeakStrongMultiRefiners_two`**
  proves it for `r = 2`.
* `Dense/Existence.lean`:
  * **`steinerExistenceFor_two`**: for every `q > 2`, Steiner systems `S(2, q, n)` exist for every
    large `n` with the divisibility conditions. Unconditional.
  * **`steinerExistence_of_nativeWeak`**: the Existence Conjecture for Steiner systems (all
    `q > r ≥ 2`), conditional only on `NativeWeakStrongMultiRefiners q r` for `r ≥ 3`.

### Piece degrees and additive terms (latest session)

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`):

* **Piece degrees for every `r`.** `RequestProject/MultiRefiner/PieceDeg.lean` defines
  `pdeg ends 𝒲 S`, the number of pieces whose vertex set contains `S`. This is the quantity in
  `IsStrongMultiRefiner.pieceDeg`. It is now tracked through every part of the construction:
  * flat steps (`flatStep_struct`, `flatStep_deg`, `placedFlatStep`, `placedFlatStep_link`): every
    piece lies inside the span of one lifted link piece, and each lifted piece gives two pieces
    (`pairFamily_pdeg_le`);
  * multiplicity reduction (`multiplicityReduction_quant`): pieces consist of parallel copies
    (`mW_parallel`, `pdeg_le_of_parallel`);
  * the anti-edge round, the chains of levels (`PlacedOut`, `placedChain`), the stages
    (`multiStage`), the base case and the iteration (`RefinerOut`, `StageProp`, `baseRefiner`,
    `denseRefiner_of`, `stagedRefiner_of`) and `topRefiner`.
* **Additive terms.** `PlacedLinkLevelA q r i a` (`Placement/ChainLevels.lean`) asks for link
  refiners only when `D ≥ a |Z|`, which is the same as allowing bounds `C·(D + a|Z|)`. The chains,
  stages and iteration accept this, and a monotone sublinear `a` still gives the `o(n)` budget.
* `Dense/Native.lean`: **`nativeWeakStrongMultiRefiners_of_levelsA`**,
  **`nativeWeakStrongMultiRefiners_of_levels`**, `nativeWeakStrongMultiRefiners_three`;
  `nativeWeakStrongMultiRefiners_two` is now a corollary.
* `Dense/Existence.lean`: **`steinerExistence_of_levels`**, `steinerExistenceFor_of_levels`,
  `steinerExistenceFor_of_levelsA`, `steinerExistenceFor_three`. The Existence Conjecture for
  Steiner systems is conditional only on the intermediate link levels `1 ≤ i < r - 1` (for
  `r = 3`, only `i = 1`).

Still open (see `LEDGER.md`):
* `PlacedLinkLevel q r i` (or `PlacedLinkLevelA` with a sublinear `a`) for `1 ≤ i < r - 1`,
  needed only for `r ≥ 3`. The piece-degree bound is no longer missing.
* `NativeStrongMultiRefiners q r` with the exact budget `C·max(D, n^{1-1/r} log n)` of
  Theorem 1.10, even for `r = 2`. Section 2 (Existence Conjecture) only uses an `o(n)` budget.

### Link levels in `ε`-form (latest session)

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`):

* `Placement/ChainLevelsE.lean`: `PlacedLinkLevelE q r i`. For every precision `s`, the link
  refiners may have bounds `C_s·D + B·|Z|/2^s`, where the refinedness `Cl` and `B` do not depend on
  `s`. This is the `C_ε·D + ε·|Z|` shape that refiners without the fine compression of Refine Down
  give, since `D^α m^{1-α} ≤ C_ε D + ε m`. It is implied by `PlacedLinkLevel` (`PlacedLinkLevel.toE`)
  and by `PlacedLinkLevelA` with a sublinear `a` (`PlacedLinkLevelA.toE`). The chains of levels are
  rebuilt in this form (`PlacedOutE`, `PlacedOutE.comp`, `placedStep_of_levelE`, **`placedChainE`**),
  with the precisions chosen backwards.
* `Dense/StageE.lean`: `StagePropE` and **`multiStageE`**, the stages in `ε`-form.
* `Dense/NativeE.lean`: `stagedRefinerE` and **`nativeWeakStrongMultiRefiners_of_levelsE`**, which
  says `PlacedLinkLevelE` for `1 ≤ i < r-1` implies `NativeWeakStrongMultiRefiners q r`.
* `Dense/ExistenceE.lean`: **`steinerExistenceFor_of_levelsE`**, `steinerExistenceFor_threeE`,
  **`steinerExistence_of_levelsE`**. The Existence Conjecture is conditional only on
  `PlacedLinkLevelE` at the intermediate levels. This hypothesis is strictly weaker than the
  previous ones.

Still open (see `LEDGER.md`, final section): `PlacedLinkLevelE q r i` for `1 ≤ i < r-1` (`r ≥ 3`),
and `NativeStrongMultiRefiners` with the exact budget `C·max(D, n^{1-1/r} log n)`.

### Link refiners for all link graphs at once (latest session)

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`). New directory `RequestProject/LinkSpread/`. A *tagged multigraph* has
copies `x` with a tag `tg x` (an `i`-set outside the reserve, the outside part `T`) and a body
`bd x` (an `(r-i)`-set, the link copy). The lifted copy is `tg x ∪ bd x`. Every degree below is the
`(r-1)`-degree of the lifted copies, **summed over all tags**, which is the "spread over `Z`"
requirement.

* `Round.lean`: **`taggedRound`**, the anti-edge round on the bodies, with the gadgets of all copies
  of all tags placed at once (Partial Clique Embedding in uniformity `i + k`).
* `Fibre.lean`: fibres, and **`linkRefiners_fibre`**: link refiners of the lifted multigraph at
  level `i + j` restrict to link refiners of the fibre bodies at level `j`.
* `Flat.lean`: **`taggedFlatStep`**, one flat step for all fibres at once.
* `Chain.lean`: `TaggedOutE` (tagged output with lifted degree budget) and
  **`taggedStep_of_levelE`**.
* `Comp.lean`: `pairSet` (the residues of all fibres as a new tagged multigraph),
  **`TaggedOutE.comp`** and **`taggedChainE`**: from `j`-flat bodies to bodies inside the reserve,
  for all fibres at once, from the link levels `i + 1, …, i + j` in `ε`-form.
* `Assembly.lean`: `TaggedRefOutE`, `TaggedLinkRefinersE` and **`placedLinkLevelE_of_tagged`**:
  `TaggedLinkRefinersE q r i → PlacedLinkLevelE q r i`. The tagged form only asks for refiners
  inside `Z` with bounded lifted `(r-1)`-degrees and lifted piece degrees. The density bound of the
  pieces for sets `J` of every size, required by `PlacedLinkLevelE`, is now derived (root
  incidence). Corollaries: `steinerExistenceFor_three_of_tagged`, `steinerExistence_of_tagged`.

**Level `1` (continuation).** Files `LinkSpread/RoundOut.lean`, `Stage.lean`, `TRefOut.lean`,
`LevelOne.lean`, `LevelOneIter.lean` and `LevelOneFinal.lean`:

* `taggedStage`: one stage for all fibres at once. `TStageOut.prepend` chains a stage with
  refiners of the residue.
* `classStep` and `taggedDense`: the tags are split into four classes, each with its own quarter of
  the reserve. This keeps the number of tags linear in the reserve, so the codegree across tags
  stays under control.
* `taggedStaged`: induction on the precision.
* **`taggedLinkRefinersE_one`**: `TaggedLinkRefinersE q r 1`, given the higher link levels.
* **`steinerExistenceFor_three_unconditional`**: Steiner systems `S(n, q, 3)` exist for every
  `q > 3` and all large admissible `n`, without hypotheses.
* `steinerExistence_of_tagged_two`: the Existence Conjecture from `TaggedLinkRefinersE` at the
  levels `2 ≤ i < r - 1` only.

Still open: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only for `r ≥ 4`; see `LEDGER.md`,
final section), and `NativeStrongMultiRefiners` with the exact budget.

### Diagnosis of the levels `2 ≤ i < r - 1` (latest session)

No new level is closed. `LinkSpread/Funnel.lean` proves, without `sorry`, the counting bound
**`exists_heavy_pdeg`**: if every tag has a piece whose span (at least `r - 1` vertices) lies in
one of `p` reserve parts of size `≤ m`, then some `(r-1)`-set has lifted piece degree
`≥ #tags / (p · C(m, r-1))`. The final section of `LEDGER.md` uses it, in an informal argument
that is not machine-checked, to explain why the staged scheme of level `1` cannot be extended to
`i ≥ 2`. Sending the residues of the `≈ |U|^i` link fibres into disjoint, geometrically shrinking
reserves forces a load `≳ K²|Z|/m₀²` at some `(r-1)`-set inside `Z` for `i = 2`, and a superlinear
load for `i ≥ 3`. Neither is compatible with `C_s D + B|Z|/2^s`. Still open: `TaggedLinkRefinersE
q r i` for `2 ≤ i < r - 1`, and `NativeStrongMultiRefiners` with the exact budget.

### Exact budget for `r = 2` and even `q`: one reserve per vertex and a global connector (latest session)

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`). New directory `RequestProject/LocalRefiner/`.

* **`nativeStrongMultiRefiners_two_even`** (`LocalRefiner/Native.lean`): for every even `q ≥ 4`,
  `NativeStrongMultiRefiners q 2` holds. The budget is `⌊D⌋ + 1`, so it is `O(max(D, 1))`, below
  `C · max(D, √n log n)`. The constant is `C = 64 q^4`.
* **`refinerAbsorbersFor_two_even`**: hence `RefinerAbsorbersFor q 2` for every even `q ≥ 4`, through
  the placement steps already proved (`refinerAbsorbersFor_of_native`).

The construction does not use a common reserve. Write `d = q - 1` (odd) and `N = binom(q, 2)`.

* *Switch per edge* `e = uv` (`Construction.lean`). The piece `P1 e` is `N` parallel copies of
  `e`, namely `e` plus `N - 1` reserve copies; it is used when `e ∈ L`. The piece `P0 e` consists
  of the same `N - 1` copies, a token at `u`, a token at `v` and a degree-free bundle `κ_e`; it is
  used when `e ∉ L`. So when `e ∈ L` the two tokens and `κ_e` are left over.
* *Token at `u`* (`Gadgets.lean`): a multigraph on the vertex's own reserve `{u, u+1, u+2}` whose
  degrees are `≡ 1` at `u` and `≡ 0` elsewhere modulo `d`. This exists because `d` is odd. Every
  reserve vertex serves three vertices.
* *Chain per vertex*: the chain refiner of the case `r = 1`, run with `q' = d` on the tokens at `u`
  (`OwnedChains.lean`, one owner per vertex). It absorbs the tokens left over at `u`, whose number
  `deg_L u` is divisible by `d`. No residue passes between vertices.
* *Global connector*: one chain refiner with `q' = N` on the bundles `κ_e`. Its blocks are placed
  on the edges of `X`. It absorbs the condition at `S = ∅` (`N ∣ |L|`).
* `Segments.lean` lifts labels to labelled copies (bundles of parallel edges). `Refiner.lean`
  proves the multi-refiner property (`isMultiRefiner_local`). `Loads.lean` proves that every vertex
  touches `O(q^2 (D + 1))` labels, which gives the degree and piece-degree bounds.

Still open: `NativeStrongMultiRefiners q 2` for **odd** `q`. For odd `q`, `d` is even, and every
multigraph has an even degree sum, so no token supported near `u` can have degrees `≡ 1` at `u` and
`≡ 0` elsewhere. Every token needs a partner vertex, and the leftover classes between partners form
again a graph of the same kind. See `LEDGER.md`, final section. Also still open:
`TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1`.

### Odd `q`, `r = 2`: the parity obstruction in Lean (latest session)

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`). New directory `RequestProject/GridRefiner/`:

* `Lift.lean`: `lift_residual` turns a refiner described on labels (each label is a small bundle of
  parallel edges, and the inputs are single copies) into an `IsResidualMultiRefiner` on the copies.
  The divisibility of the residue is derived automatically (`divisible_of_partition`).
* `Labels.lean`: the labels and segment data intended for a staged construction for odd `q`.
* `Parity.lean`: the informal analysis of the previous session, now proved in Lean.
  * `even_sum_classes`: if `q - 1` is even, the degree classes of any multigraph modulo `q - 1`
    have even sum (handshake lemma `sum_mdeg_singleton`).
  * **`single_vertex_class_iff`**: if `d` is even (and `n ≥ 3`), a multigraph with degrees `≡ a` at
    `u` and `≡ 0` at every other vertex modulo `d` exists **iff `a` is even**.
  * **`no_local_unit_token`**, **`unit_token_needs_partner`**: for odd `q` there is no token with
    degree `≡ 1` at `u` alone; every such multigraph has a second vertex with a non-zero class.
  * **`partnerTok_deg`**: tokens with classes `1_u - 1_p` (one partner `p`) do exist for every `q`.
  * **`local_token_half_iff`**: for odd `q`, a local token at `u` with degree
    `≡ (q-1)/2 + 1` exists iff `q ≡ 3 (mod 4)`. For such `q` the class of an edge `uv` is two local
    tokens plus the order-`2` class `(q-1)/2·(1_u + 1_v)`.
  * **`eq_of_forall_sum_eq_zero`**: if every `d`-subset of at least `d + 1` group elements sums to
    `0`, they are all equal. So all tokens absorbed by one chain have the same class.
  * **`even_cut_of_divisible`**: for odd `q`, every vertex set is crossed by an even number of
    edges of any divisible `L`.

Still open (unchanged): `NativeStrongMultiRefiners q 2` for odd `q`, `TaggedLinkRefinersE q r i`
for `2 ≤ i < r - 1`, and the exact budget for `r ≥ 3`. See `LEDGER.md`, final section.

### Odd `q`, `r = 2`: one switch stage with partner tokens (latest session)

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`), in `RequestProject/GridRefiner/OddSwitch.lean`. It does not assume
`NativeStrongMultiRefiners` and does not change the target budget.

* The switch of an edge `e = uv` uses the partner tokens of `partnerTok_deg`: `tok u` has class
  `1_u - 1_{π u}` (`tok_cls`). Pieces: `swP1 e = {x e, anti e}` and
  `swP0 e = {anti e} ∪ swRest e`, where the *rest* `swRest e` consists of the two tokens and a
  *remainder*, one copy of the edge `π u π v` (`remainder_lift`).
* **`switch_residual`**: via `lift_residual`, the stage is an `IsResidualMultiRefiner` with
  constant `3 q (q - 1)`; **`switch_decomp`**: the residue for selected edges `L` is exactly the
  union of the rests of the edges of `L`.
* **`swRest_classes`, `swRes_classes`**: the rest of `e` has the degree classes of `e` modulo
  `q - 1` and `2 q (q - 1) + 1` copies; the residue of `L` has degree `≡ deg_L` at every vertex.
* **`switch_load`, `switch_load_inj`**: with injective partner and helper maps every vertex has
  load at most `9 q (q - 1) D`. So this step **does** have load `O(D)`.
* **`switch_needs_remainder`** (`q ≥ 3`): without the remainder the switch piece is not divisible.
* **`oddSwitch_stage`**: everything above for the concrete shift plan (`π u = u + 1`,
  `hw u = u + 2`), for every graph on `Fin n`, `n ≥ 3`.

Not proved (global closure): absorbing the tokens and the remainder graph `π(L)`, which again has
`|L|` edges. `NativeStrongMultiRefiners q 2` for odd `q` stays open.

### `r = 2` closed for every `q ≥ 3`, including odd `q` (latest session)

Proved without `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`; see
`checks/AxiomCheck.lean`), in `RequestProject/OddGrid/`:

* **`nativeStrongMultiRefiners_two`** (`OddGrid/Native.lean`): `NativeStrongMultiRefiners q 2` for
  **every** `q ≥ 3`, in particular for odd `q` (`nativeStrongMultiRefiners_two_odd`). The budget is
  `5 ⌊D⌋ + 400 ⌊√n⌋ ⌈log₂ n⌉ ≤ 1205 · max(D, √n log n)`, the constant is `Cpl (q(q-1)) 256 + 1205`,
  and `n ≥ 25`.
* **`refinerAbsorbersFor_two`**: `RefinerAbsorbersFor q 2` for every `q ≥ 3`. This is Theorem 1.10 for
  `r = 2`, in the form used by the project.
* **`steinerExistence_of_refinerAbsorbers_three_le`**: the Existence Conjecture for Steiner systems
  follows from `RefinerAbsorbersFor q r` for `3 ≤ r < q` alone. The cases `r = 1` and `r = 2` are
  theorems now.

*The construction.* A *plan* is a sequence of stages. At each stage, every current pair is sent along
a signed walk with 1 or 3 steps between its ends, or it is *moved*. A move is allowed only if the
pair is the only one at one of its vertices; divisibility then makes its weight `≡ 0 (mod q - 1)`.
`plan_strong` (`PlanStrong.lean`) turns a valid plan into a strong multi-refiner. Its degree budget
is the total load `Σ_t pass t v`, and its constant depends only on `q` and the number of final pairs.
Odd walks are what the parity obstruction of the previous sessions allows. The plan on `Fin n`
(`base_plan`) has the following parts.

1. `XStage.lean`: the vertices sit on a `⌊√n⌋ × ⌊n/⌊√n⌋⌋` board, plus an extra partial column. An
   input pair `uw` that is not in one row or one column is routed `u → (r_u, x) → (r_w, x) → w`.
   The column `x` comes from a greedy balanced colouring (`greedy_color`, `Greedy.lean`), so every
   cell is used `O(D)` times.
2. `Merge.lean` (generic): a two-stage *merge segment* empties a set of vertices. Stage 1 reroutes
   every pair at an emptied vertex `u` through its hub `h u`, using twins for pairs to kept vertices.
   Stage 2 moves the single remaining pair `{u, h u}`. `merge_seg` proves validity, and
   `merge_load0`/`merge_load1` bound the loads.
3. `Extra.lean`: one merge segment empties the extra column (`extra_seg`).
4. `Halve.lean`, `Phase.lean`: merge segments halve the columns (odd columns into even ones) until
   fewer than 5 remain (`halve_seg`, `phase_spec`). The same is then done for the rows, on the
   swapped grid (`Grid.swap`). Each halving costs `O(√n)` per vertex, and there are `O(log n)`
   halvings.
5. `Assemble.lean`, `Base.lean`: the complete plan (`grid_plan`, `base_plan`) ends with at most `256`
   rook pairs of a `4 × 4` board, and its load is `O(D + √n log n)`.

Still open for the full paper: the exact budget `NativeStrongMultiRefiners q r` (equivalently
`RefinerAbsorbersFor q r` in the form used) for `r ≥ 3`, and `TaggedLinkRefinersE q r i` for
`2 ≤ i < r - 1`. The construction above is specific to graphs (pairs) and does not extend
directly to `r ≥ 3`.

### Status of the remaining items; per-uniformity reduction (latest session)

Proved without `sorry` (standard axioms only; see `checks/AxiomCheck.lean`):

* `RequestProject/LinkSpread/PerUniformity.lean`: `steinerExistenceFor_of_tagged_two` (for fixed
  `3 ≤ r < q`, `S(n, q, r)` exist for all large admissible `n` from `TaggedLinkRefinersE q r i`,
  `2 ≤ i < r - 1`, of the same `q, r`) and `steinerExistenceFor_four_of_tagged` (`S(n, q, 4)` from
  the single level `TaggedLinkRefinersE q 4 2`).
* `RequestProject/MultiRefiner/Restrict.lean`: `IsResidualMultiRefiner.restrict`, a residual
  multi-refiner of `X` restricts to one of any `X' ⊆ X`.

The nibble is **not** an assumption of any route to the Existence Conjecture: it is proved in
`RequestProject/Nibble/`, and the endpoints above depend only on the hypotheses in their
statements. Still open: `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1` (only `r ≥ 4`) and
`NativeStrongMultiRefiners q r` for `r ≥ 3`; `LEDGER.md` records why the existing schemes do not
extend and what is missing.

### `r`-uniform plans (`RequestProject/HyperPlan/`, latest session)

Proved without `sorry` (standard axioms only):

* `plan_strongR`: valid `r`-uniform plans (signed lists of `r`-sets, class-preserving modulo
  `binom(q-i, r-i)` up to loneliness) give strong multi-refiners, for every `r`.
* `nativeStrongMultiRefiners_of_rPlans`: `NativeStrongMultiRefiners q r` follows from the purely
  combinatorial statement `RPlans q r` (plans with loads `≤ C · max(D, n^{1-1/r} log n)`).
* `rPlans_two`: `RPlans q 2` for `q ≥ 3`, from the grid plans of `OddGrid`
  (`nativeStrongMultiRefiners_two_viaR` recovers the `r = 2` result through the reduction).
* `routeOKR_fullBox`, `routeOKR_loneBox`: the valid moves for `r`-sets (boxes).
* `collapse_plan`, `partite_strongMultiRefiner`: for every `r`, an explicit valid plan collapsing
  an `r`-partite `r`-graph onto one set, with uncontrolled loads.

Still open: `RPlans q r` for `r ≥ 3` (the load bound); see `LEDGER.md`.

### Tools for `r`-uniform plans (`RequestProject/HyperPlan/`, latest session)

`RPlans q r` for `r ≥ 3` (and therefore `NativeStrongMultiRefiners q r`) is **still open**. This
session formalized the general machinery for building `r`-uniform plans. Everything is proved
without `sorry`.

* `Segment.lean`: plans built from segments (`SegOKR.append`, `planOKR_of_segOKR`); loads add up
  (`passSumR_append`).
* `LinkLift.lean`: `routeOKR_liftRoute` lifts a valid route of uniformity `r - 1` (parameter
  `q - 1`) in the link of a vertex `u` to a valid route of uniformity `r`, using a twin vertex.
  `allowedR_subset_link` lets loneliness inside the link be used.
* `Empty.lean`, `EmptyMany.lean`: emptying vertices. A valid segment on the link of every vertex of
  a set `U` lifts to a valid `r`-uniform segment (`segOKR_liftSegU`), provided no set contains two
  vertices of `U`. During this segment the link of each `u` follows its link segment, and the
  loads are bounded by `passR_liftSegU_le`. Once every vertex of `U` is lonely, one stage moves
  them all out (`segOKR_moveU`, `prunR_moveU_disjoint`).

What is missing is the global plan, with routes into a sparse structure and a halving schedule,
whose loads are `O(max(D, n^{1-1/r} log n))`; see `LEDGER.md`.

### Restriction of local plans and persistence of faces (latest session)

`RPlans q r` for `r ≥ 3` is **still open**. Two more general tools were added, both proved without
`sorry`:

* `Mono.lean`: a *local* plan (routes that do not depend on the current family) designed on a large
  structure is valid for every subfamily, with no larger loads and no larger final family
  (`PlanOKR.mono_local`, `passSumR_mono_local`, `card_prunR_mono_local`).
* `Persist.lean`: in every valid plan with `r < q`, a valid route covers every face of size `< r`
  of the set it reroutes whenever weight `1` can occur (`route_covers_face`). So every face of an
  input set is still a face of a present set after the first stage (`face_persists_zero`), and at
  later stages a face can only disappear through a set in which some face is lone
  (`face_persists`).

### Descent through windows (`RequestProject/Window/`, latest session)

The PDF attached in this session is again the survey arXiv:2510.19978. It has no Theorem 3.8 and
no Lemmas 3.12/3.13. Its Lemma 3.8 is the General Embedding Lemma, its §3.4 is a one-paragraph
sketch of Refine Down, and its §4.2 is about Nash-Williams. The construction for `r ≥ 3` is
therefore still not available here.

This session works directly at the level of multi-refiners (refinement families and their loads),
the language of Delcourt–Postle. No translation of loads into typed plans is needed. Proved without
`sorry` (standard axioms only; see `checks/AxiomCheck.lean`):

* `Window/Descent.lean`:
  * `WindowStage q r Cst m₀ a` describes **one halving stage**. The input is `X` inside a window
    `U` with `Δ_{r-1}(X) ≤ D`. The output is a residual multi-refiner whose new copies and pieces
    have load `≤ Cst · (D + a |U|)`, whose pieces contain at most one copy of `X`, and whose
    residue lies in a window `U'` with `2|U'| ≤ |U|` and has `Δ_{r-1} ≤ Cst · a |U|`.
  * **`windowRefiner_of`**: iterating the stage through the windows and finishing with the finite
    base case gives the budget `A · D + K · (log₂ |U| + 1) · a |U|`. The residue degree is reset
    at every stage, so the constants do not grow; the loads of the `≤ log₂ |U| + 1` windows are
    added up.
  * `windowTop_of` is the same result on `Fin n`, as a strong multi-refiner.
* `Window/Native.lean`:
  * **`nativeStrongMultiRefiners_of_windowStage`**: `WindowStage` with cost
    `winCost r m = ⌈m^{1-1/r}⌉` implies `NativeStrongMultiRefiners q r`, i.e. the exact budget
    `C · max(D, n^{1-1/r} log n)`.
  * `refinerAbsorbersFor_of_windowStage` is the corresponding consequence for
    `RefinerAbsorbersFor q r`.
* `Window/Linear.lean`: the stage that is already formalized is a window stage with **linear** cost
  `a m = m` (`windowStage_id_of_stagePropE`, `windowStage_id_of_levelsE`). This holds
  unconditionally for `r = 2` and `r = 3` (**`windowStage_id_two`**, **`windowStage_id_three`**).
  So the window format is realized, and the remaining gap is exactly the cost of one window:
  `m` (proved) versus `⌈m^{1-1/r}⌉` (needed).

Still open: `WindowStage q r Cst m₀ (winCost r)` for `r ≥ 3` (the sparse-residue stage of one
window). The previous open items are unchanged: `NativeStrongMultiRefiners q r` for `r ≥ 3`, and
`TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1`.

### Sharp budget: Edge Sparsification and Better Refine Down (`RequestProject/Sharp/`, latest session)

The correct paper (Delcourt–Postle, *Proof of the Existence Conjecture via Refined Absorption*,
arXiv:2402.17855) was supplied in this session. The following are proved without `sorry`, using
only the standard axioms (see `checks/AxiomCheck.lean`):

* **Lemma 3.12 (Edge Sparsification), `edgeSparsification_holds`** (`Sharp/Sparsify.lean`). For all
  `q > r ≥ 2` and every multiplicity bound `M₀` there are constants `Cst, m₀` with
  `EdgeSparsification q r M₀ Cst m₀`. This is the window form of the lemma, defined in
  `Sharp/Better.lean`: an `r`-multigraph `X` inside a window `U` (`|U| > m₀`), with multiplicity
  `≤ M₀` and `Δ_{r-1}(X) ≤ D`, has a residual multi-refiner with new copies inside `U` whose
  residue has `Δ_{r-1} ≤ Cst · ⌈|U|^{1-1/r}⌉`, independently of `D`. Its new copies and pieces have
  `Δ ≤ Cst · (D + ⌈|U|^{1-1/r}⌉ (⌊log₂|U|⌋ + 1))`. The proof follows §3.4 of the paper:
  * `Sharp/Partition.lean`: the quasi-random partition into `k = ⌈|U|^{1-1/r}⌉` parts
    (Proposition 3.17), proved by Bernstein's inequality and a union bound;
  * `Sharp/Special.lean`: the special sets (Lemma 3.19), built greedily;
  * `Sharp/CliqueRefiner.lean`: the private-clique refiner `R₁`;
  * `Sharp/SparsBuild.lean`: `R₁` followed by the Multiplicity Reduction Lemma (3.16);
  * `Sharp/SparsCount.lean`: the counting of `Δ(R₁)` and of the remainder;
  * `Sharp/SparsArith.lean`: the asymptotic inequalities, i.e. the union bound, the bounds
    `m^{r-1} ≤ k^r ≤ 2^r m^{r-1}` and the binomial lower bounds.
* **Lemma 3.14 (Better Refine Down), `windowStage_of_sparsify_levels`** (`Sharp/Better.lean`):
  edge sparsification followed by the refine-down stage is one window stage of cost
  `sharpCost r m = ⌈m^{1-1/r}⌉ (⌊log₂ m⌋ + 1)`. The descent through the windows with this cost
  (`Sharp/Descent.lean`, potential `sharpPot r n ≤ 30 n^{1-1/r} log n`) yields the exact budget
  `C · max(D, n^{1-1/r} log n)`.
* **Theorem 3.8 from the link levels, `nativeStrongMultiRefiners_of_levels`**
  (`Sharp/Sparsify.lean`): `NativeStrongMultiRefiners q r` (strong multi-refiners with the exact
  budget) holds as soon as `PlacedLinkLevelA q r i (sharpCost r)` holds for `1 ≤ i < r - 1`. For
  `r = 2` there are no such levels, so `nativeStrongMultiRefiners_two_sharp` is unconditional;
  this case was already known in the project by other routes.

**Still open:** the link levels `PlacedLinkLevelA q r i (sharpCost r)` for `1 ≤ i < r - 1`. These
are §4 of the paper (Lemma 4.1, the Local Multi-Refiner Theorem 4.4 and the random embedding),
which use Theorem 3.7 inductively in uniformity `r - i`. For `r = 3` only the level `i = 1` is
missing. The project proves this level with an additive term `ε|Z|` (`PlacedLinkLevelE`), but not
yet with the sublinear term `sharpCost 3 |Z|`. The previously open items are unchanged:
`NativeStrongMultiRefiners q r` for `r ≥ 3`, and `TaggedLinkRefinersE q r i` for `2 ≤ i < r - 1`.

### §4 for `3`-graphs: random embedding of local refiners (`RequestProject/Local/`, latest session)

Source: Delcourt–Postle, arXiv:2402.17855, §4 (Lemma 4.1, Definition 4.2, Theorem 4.4). Everything
below compiles without `sorry` and uses only the standard axioms (`checks/AxiomCheck.lean`).

* `Chernoff.lean`: a Chernoff bound for sums of independent bounded variables, in counting form over
  a product of finite sets (`card_sum_ge_le`), and the union bound (`exists_good_choice`).
* `Affine.lean`: random affine maps `z ↦ a z + t` of `ZMod p`, carried onto a copy of `ZMod p` in the
  vertex set (they replace the random permutations of the paper; the affine group is sharply
  `2`-transitive). **`exists_affine_spread`** is the probabilistic core of Lemma 4.1: there is
  one map per set system such that every pair meeting the copy lies in few moved sets.
* `StageZero.lean` (**`taggedStage0`**), `Prepend.lean`, `LocalAssembly.lean`
  (**`trefOut_of_local`**: independent local refiners for the tags give complete tagged refiners),
  `TaggedA.lean` (`TaggedLinkRefinersA`, **`placedLinkLevelA_of_taggedA`**).
* `FlatEmbed.lean`, `FlatEmbedMain.lean`: **`flatEmbedTagged`** (Lemma 4.1 for `r = 3`, level `1`).
  For each outside vertex, the local refiner of its link graph is built on `Z₁ ∪ P₀`, where `P₀` is
  a copy of `ZMod p`. It is then moved by the chosen affine map. The `2`-degrees of the result are
  `≤ C (Bd₁ + sharpCost 3 |Z|)`.
* `LevelOneSharp.lean`: **`placedLinkLevelA_three_one`**, i.e. the missing level
  `PlacedLinkLevelA q 3 1 (sharpCost 3)`, and **`nativeStrongMultiRefiners_three_of_flat`**,
  i.e. Theorem 3.8 for `r = 3`. Both take as input `FlatGraphRefiners (q-1) a`: flat local
  refiners for graphs, with an additive term `a` dominated by `sharpCost 3`.
* `CliqueOmni.lean`: `FlatCliqueOmniAbsorbers q a` is Theorem 3.7 for graphs in local form. Its
  conclusions are (1) the degrees, (2) flatness (every new edge meets the new vertices), and that
  the pieces are cliques (Remark 3.9). **`flatGraphRefiners_of_cliqueOmni`** shows it implies the
  flat local refiners. **`nativeStrongMultiRefiners_three_of_cliqueOmni_two`** gives
  `NativeStrongMultiRefiners q 3` from `FlatCliqueOmniAbsorbers (q-1) (sharpCost 2)`.

Still open: proving `FlatCliqueOmniAbsorbers` for graphs. This is Theorem 3.7 for `r = 2` with
flatness and clique pieces. The project's proof of Theorem 3.8 for `r = 2` does not record where
the new edges lie, so it does not give this. Also open: the levels `2 ≤ i < r - 1` for `r ≥ 4`.

### Theorem 3.7 for graphs (flat, clique pieces) and Theorem 3.8 for `3`-graphs (`RequestProject/FlatOmni/`, `RequestProject/SparseChain/`, latest session)

Source: Delcourt–Postle, arXiv:2402.17855, Theorem 3.7 (with flatness (2)), Remark 3.9, Lemma 4.1,
Theorems 3.8 and 4.4. Everything below compiles without `sorry` and uses only `propext`,
`Classical.choice` and `Quot.sound` (`checks/AxiomCheck.lean`).

**Main result: `RefinedAbsorption.Local.nativeStrongMultiRefiners_three`**
(`SparseChain/ThreeGraphs.lean`). For every `q > 3`, `NativeStrongMultiRefiners q 3` holds
unconditionally. This is Theorem 3.8 for `3`-graphs: strong `C`-refined multi-refiners with
budget `C · max(D, n^{2/3} log n)` whenever `Δ₂(X) ≤ D ≤ n / C`.

How it is obtained:

* **Theorem 3.7 for graphs, sparse form.** `FlatCliqueOmniAbsorbersS q a` (`FlatOmni/Assembly.lean`)
  is `FlatCliqueOmniAbsorbers q a` plus the hypothesis `Ch · d ≤ |P|`. This is the hypothesis
  `Δ(X) ≤ n / C` of Theorem 3.7 in the paper. **`flatCliqueOmniAbsorbersS_two`** proves
  `FlatCliqueOmniAbsorbersS q (sharpCost 2)` for every `q > 2`. The construction has four steps:
  1. `localRefiner` (`FlatOmni/LocalRefiner.lean`): one refine-down stage from `Y` into `P`, then
     the window descent inside `P`. Degrees are `≤ C (d + sharpPot 2 |P|)`.
  2. `fakeStage` (`FlatOmni/Fakes.lean`): every new copy is replaced by fake edges placed in `P`
     (Lemma 5.2 inside a reserve). The new edges then form a simple graph `F`, and each meets `P`.
  3. `absStage` (`FlatOmni/Attach.lean`): every piece gets a private bounded absorber, placed in
     `P`.
  4. `cliquePieces_refiner` (`FlatOmni/CliquePieces.lean`): the cliques of the on/off
     decompositions are the new pieces (Remark 3.9).

  `sharpPot_two_le` (`FlatOmni/SharpBounds.lean`) shows `sharpPot 2 m ≤ 6 · sharpCost 2 m`.
* **The sparse chain.** In the window stage the link levels are only used after edge
  sparsification, where the degree is `O(sharpCost r |U|) = o(|U|)`. Sparse levels therefore
  suffice:
  * `PlacedLinkLevelS` and `TaggedLinkRefinersS` (`SparseChain/Levels.lean`) are
    `PlacedLinkLevelA` and `TaggedLinkRefinersA` with the hypothesis `Ch · D ≤ |Z|`.
  * `placedChainS`, `multiStageS`, `windowStage_of_sparsify_levelsS` and
    **`nativeStrongMultiRefiners_of_levelsS`** (any `r ≥ 2`) prove Theorem 3.8 from sparse levels
    at `1 ≤ i < r - 1`.
  * `flatEmbedTaggedS` (`SparseChain/FlatEmbedS.lean`) and `placedLinkLevelS_three_one` give the
    sparse level `1` of `3`-graphs from sparse flat graph refiners.

**About the original `FlatCliqueOmniAbsorbers` (without `Ch · d ≤ |P|`).** It is *not* proved. The
placement steps (fake edges and absorbers placed inside `P`, with simple new edges) need the
smallness hypothesis. Without it, a vertex of `Y` would have to carry new degree of order `|P|`. The
conditional theorems `nativeStrongMultiRefiners_three_of_cliqueOmni(_two)` are unchanged.
`FlatCliqueOmniAbsorbers.toS` shows that the original statement implies the sparse one.

**Still open (`r ≥ 4`).** The levels `TaggedLinkRefinersE q r i` and
`PlacedLinkLevelA`/`PlacedLinkLevelS q r i (sharpCost r)` for `2 ≤ i < r - 1` remain unproved.
By `nativeStrongMultiRefiners_of_levelsS`, Theorem 3.8 for `r ≥ 4` now needs only the *sparse*
levels at `1 ≤ i < r - 1`. These would require Theorem 3.7 in uniformity `r - i ≥ 3`, with
flatness and clique pieces, and the random embedding of Lemma 4.1 for outside parts of size `i`.
Neither is formalized here.

### All uniformities: `r ≥ 4` (`RequestProject/General/`, latest session)

The sparse link levels `PlacedLinkLevelS q r i (sharpCost r)`, `1 ≤ i < r - 1`, are proved for
every `r` by induction on the uniformity and downward induction on `i` (`placedLinkLevelS_all` in
`General/Levels.lean`):

* `General/Defs.lean`, `General/FlatOmniK.lean` and the files it uses: Theorem 3.7 in every
  uniformity `k` (flatness, clique pieces) in local form, `FlatOmniK`, from the lower link levels
  (`flatOmniK_of_levels`);
* `General/EmbedGen.lean`: the random embedding of Lemma 4.1 for outer parts of any size `i`
  (`flatEmbedGen`);
* `General/StageS.lean`: the tagged stage without additive term (`taggedStage0S`);
* `General/Levels.lean`: `taggedLinkRefinersS_gen`, `placedLinkLevelS_all`,
  **`nativeStrongMultiRefiners_all`** (Theorem 3.8 for every `q > r ≥ 2`) and
  **`steinerExistence`**.

## The original article (Delcourt–Postle, arXiv:2402.17855v1)

`RequestProject/Original2024/` gives a separate interface for the original 2024 article
(`Defs.lean`: Definitions 1.5–1.6 and 1.8–1.10; Theorems 1.4, 1.7, 1.11, 3.8 and 6.1, with ambient
vertex sets) and proves the following (`Final.lean`, `MinDegree.lean`):
`theorem_1_4`, `theorem_3_8` (without the `Y`-flatness output),
`theorem_1_11`/`theorem_1_11_strong` and `theorem_1_7`/`theorem_1_7_strong` (inside a dense host
`G`), and `theorem_6_1`.  They use only the standard axioms (`checks/Original2024Axioms.lean`).
See `Original2024_LEDGER.md` for the theorem-by-theorem ledger.

### Continuation: the flatness output of Theorem 3.8, corollaries, and survey Lemma 2.1

* `Original2024/FlatChain.lean`, `Original2024/Flat.lean`, `Original2024/FlatOne.lean`:
  **`theorem_3_8_flat`**, i.e. Theorem 3.8 with the flatness output, for all `q > r ≥ 1`. For
  **every** prescribed set `Y` with `|Y| ≥ n/3`, the multi-refiner `R` is `(r-1)`-flat to `Y`
  (`IsFlatTo`: every copy of `R` has at most `r - 1` vertices outside `Y`). The unconditional form
  is `multiRefinerFlat`. The other reading of "flat to `Y`" (some `Y'` with `|Y'| ≥ n/3` such that
  every new copy has at most `r - 1` vertices inside `Y'`) is `MultiRefinerFlatConclusion.exists_inside`.
* `Original2024/Corollaries.lean`: `theorem_1_1_steiner` (Steiner systems, from Theorem 6.1 applied
  to `K_n^r`), `theorem_1_1` (all `λ`), `decomposition_complete_minus_sparse` (`K_n^r` minus a
  sparse graph, from Theorem 6.1), and `theorem_3_7_local` (Theorem 3.7 in local flat form, all
  `2 ≤ k < q`).
* `SurveyReserves.lean`: **`reservesLemma`**, the survey's Lemma 2.1 exactly as stated, via a
  `p`-random subset of `K_n^r` with bounded-differences tail bounds.
* `SurveyCorollaries.lean`: `theorem_1_8` (efficient omni-absorbers), `lemma_2_1`,
  `existenceConjecture_steiner_section2` (the survey's Section 2 argument with every ingredient
  proved) and `existenceConjecture` (all `λ`).

Axiom checks: `checks/Original2024Axioms.lean` and `checks/AxiomCheck.lean`.

### Final continuation: Theorem 1.3 in general and Lemma 3.8 (General Embedding)

Both build without `sorry` and use only `propext`, `Classical.choice`, `Quot.sound`
(`checks/PendingAxioms.lean`).

* **Theorem 1.3 (nibble for designs), general form**: `nibbleForDesigns : NibbleForDesigns`
  (`RequestProject/NibbleDesigns.lean`), exactly the statement in `Statements.lean`, with no bound
  on the number of vertices `n`.  The proof is a local nibble: each round is analysed with the
  symmetric Lovász Local Lemma (`RequestProject/Nibble/LLL.lean`, `LocalRound.lean`,
  `LocalIterate.lean`, `LocalMain.lean`; statement `LocalNibble`, theorem `localNibble`), so
  all error terms depend only on the degree `D` and not on `n`.
* **Lemma 3.8 (General Embedding)**: `generalEmbeddingLemma : GeneralEmbeddingLemma`
  (`RequestProject/GeneralEmbedding/`; statement and Definitions 3.6–3.7 in `Defs.lean`).
  `J` is a multi-`r`-graph given by labelled edge copies, `ℋ` a `C`-refined family of subgraphs,
  `W` a `C`-bounded edge-intersecting supergraph system (new vertices of `W_H` are labelled by
  `Fin (m H)`, so they are automatically distinct from `V(J)` and from those of other `W_H'`).
  `D` is any upper bound on the `(r-1)`-degrees of `J` with `D ≤ n / C'`.  The conclusion gives
  an embedding `φ` of every `W_H` into `G ∖ (E(J) ∖ E(H))`, with new edges of different
  supergraphs having different images, and `Δ_{r-1}(φ(W)) ≤ C' D`.
  The proof is a greedy embedding with degree thresholds `θ_j = K_j D n^{r-1-j}`
  (`Counting.lean`, `State.lean`, `Step.lean`, `Bad.lean`, `Good.lean`, `Greedy.lean`,
  `Main.lean`): at each step at most a quarter of the `γ n^{m_H}` available embeddings reuse a
  new edge and at most a quarter create a nearly saturated set, so a good choice always exists.

## New results extending the formalization (`RequestProject/Extensions/`)

Built on the proved minimum degree version of the Existence Conjecture (Theorem 6.1 of the
original article). All build without `sorry` and use only `propext`, `Classical.choice`,
`Quot.sound` (`checks/ExtensionsAxioms.lean`).

| Declaration | File | Result |
| --- | --- | --- |
| `partialSteiner_completion` | `Extensions/Completion.lean` | **Completion of sparse partial Steiner systems.** For `q > r ≥ 1` there are `ε > 0`, `n₀` such that for every admissible `n ≥ n₀`, every partial Steiner system on `n` points whose covered `r`-graph has `Δ_{r-1} ≤ ε n` is contained in an `(n, q, r)`-Steiner system. |
| `partialSteiner_embedding`, `partialSteiner_embeds` | `Extensions/Embedding.lean` | **Finite embedding theorem.** Every finite partial Steiner system (on any finite set) embeds in an `(N, q, r)`-Steiner system, for every sufficiently large admissible `N`; admissible `N` exist in every progression `q + t·r!·∏ binom(q-i, r-i)` (`designDivisibility_progression`). For Steiner triple systems this is Treash's theorem. |
| `log_card_steinerSystems_theta` | `Extensions/Count.lean` | **The number of Steiner systems is `n^{Θ(n^r)}`:** `c n^r log n ≤ log #S(n,q,r) ≤ (q+1) n^r log n` for all large admissible `n`. |
| `steiner_extends_subsystem`, `steiner_with_subsystem` | `Extensions/Subsystem.lean` | **Doyen–Wilson type theorem.** Every `(m, q, r)`-Steiner system placed on any `m ≤ ε n` of the `n` points extends to an `(n, q, r)`-Steiner system; hence (`r ≥ 2`) for admissible `n, m ≥ n₀` with `m ≤ ε n` there is an `S(n, q, r)` with an `S(m, q, r)` subsystem. |

*Proof ideas.* Completion: the covered `r`-graph `H` of a partial system `P` is decomposed by `P`,
hence `K_q^r`-divisible, so `K_n^r \ H` is divisible and of minimum degree `≥ (1-ε)n`; Theorem 6.1
decomposes it and `P` is added back. Embedding: a fixed partial system placed in `N` points has
`(r-1)`-degrees at most its number of points `≤ ε N`. Counting (lower bound): every partial system
inside a set `U` of `u ≈ n/m ≤ ε n` points completes, and a Steiner system contains at most
`2^{binom(u,r)}` partial systems inside `U`; a greedy double count gives at least `B^k` partial
systems with `k` blocks (`card_psFamily_ge`, `Extensions/Partial.lean`), with
`B = binom(q,r) binom(u-r,q-r)` and `k ≈ binom(u,r)/(2 binom(q,r)^2)`. Upper bound: a Steiner
system is a set of at most `binom(n,r)` of the `binom(n,q)` blocks.

## Second round of extensions: combination with classical results

Files `RequestProject/Extensions/Packing.lean` and `RequestProject/Extensions/AlmostResolvable.lean`.
No `sorry`; only `propext`, `Classical.choice`, `Quot.sound` (`checks/ExtensionsAxioms.lean`).

| Declaration | Result | Assumptions |
| --- | --- | --- |
| `optimal_packing`, `optimal_packing_count` | **Optimal packings (strong Erdős–Hanani).** For `q > r ≥ 1` there are `K, n₀` such that for **every** `n ≥ n₀` (admissible or not) there is a partial Steiner system `P` on `n` points whose uncovered `r`-graph `L` has `Δ_{r-1}(L) ≤ K`; hence `binom(q,r)·|P| + |L| = binom(n,r)` and `r·|L| ≤ K·binom(n,r-1)`. | none |
| `optimal_covering` | **Optimal coverings.** For every `n ≥ n₀` the `r`-sets are covered by `q`-sets `𝒞` with `binom(q,r)·|𝒞| ≤ binom(n,r) + K·n^{r-1}`. | none |
| `packing_leftover_lower`, `covering_excess_lower` | **Sharpness.** If `q - r + 1 ∤ n - r + 1`, every packing leaves `≥ binom(n,r-1)/r` uncovered `r`-sets (one through every `(r-1)`-set), and every covering has total excess `≥ binom(n,r-1)/r`. | none (elementary) |
| `steiner_almost_resolvable` | **Every large Steiner system is asymptotically resolvable**: for `q > r ≥ 2`, `ε > 0`, `n ≥ n₀`, the blocks of every `S(n,q,r)` split into at most `(1+ε)·binom(n-1,r-1)/binom(q-1,r-1)` matchings. | `PippengerSpencer` (hypothesis) |
| `exists_almost_resolvable_steiner` | With the Existence Conjecture: such Steiner systems exist for every large admissible `n`. | `PippengerSpencer` (hypothesis) |
| `resolution_classes_lower` | At least `binom(n-1,r-1)/binom(q-1,r-1)` matchings are always needed. | none |

`PippengerSpencer` is the Pippenger–Spencer theorem (1989): a `k`-uniform hypergraph whose degrees all
lie in `[(1-δ)D, D]` and whose codegrees are `≤ δD` has chromatic index `≤ (1+ε)D`. It is a
hypothesis of the theorems, not an axiom, and it is not proved here.

*Proof ideas.* Packing: take an admissible `N` with `n < N ≤ n + M`, where `M = r!·∏ binom(q-i, r-i)`
(`designDivisibility_progression`), and an `S(N,q,r)`; keep the blocks lying inside `n` of the points.
An `(r-1)`-set `S` misses only the edges whose block meets one of the `N - n ≤ M` extra points `y`.
Each such block contains the `r`-set `S ∪ {y}`, so there are at most `M` of them, and
`deg_L(S) ≤ binom(q,r)·M`. Covering: project the extra points onto the `n` points and complete each
image to a `q`-set. Sharpness: the edges through an `(r-1)`-set covered by a packing come in groups of
`q - r + 1`. Almost resolvable: an `S(n,q,r)` is a `q`-uniform hypergraph that is
`R`-regular, with `R = binom(n-1,r-1)/binom(q-1,r-1)`, and all its codegrees equal `R(q-1)/(n-1)`
(`steiner_codeg_mul`), so the Pippenger–Spencer theorem applies.

## Third round of extensions: disjoint mates and intersection numbers

File `RequestProject/Extensions/Intersection.lean`, built on Theorem 6.3 of the original article
(`Pending.theorem_6_3`) together with the existence and completion theorems above. No `sorry`, no
hypotheses beyond those stated; only `propext`, `Classical.choice`, `Quot.sound`
(`checks/IntersectionAxioms.lean`, output in `checks/IntersectionAxioms.out`).

| Declaration | Result |
| --- | --- |
| `steiner_completion_avoiding` | **Completion avoiding a partial system.** For `q > r ≥ 1` there are `ε > 0`, `n₀` such that for admissible `n ≥ n₀`, every partial Steiner system `P` with `Δ_{r-1}(∂P) ≤ ε n` and every partial Steiner system `F` admit a Steiner system `𝒮 ⊇ P` with `𝒮 ∩ F = P ∩ F`; every block of `𝒮 \ P` meets every block of `F` whose `r`-sets are not covered by `P` in at most `r` points. |
| `steiner_orthogonal_mate` | For every partial Steiner system `F` there is a Steiner system each block of which meets each block of `F` in at most `r` points (so `𝒮 ∩ F = ∅`). |
| `steiner_disjoint_mate` | **Every Steiner system of large order has a disjoint mate**, with cross intersections at most `r`. |
| `decomposition_disjoint_mate` | Every `K_q^r`-decomposition of a divisible `r`-graph with `δ_{r-1} ≥ (1-ε)n` has a disjoint mate (cross intersections `≤ r`). |
| `steiner_intersection_prescribed` | For every Steiner system `𝒮₁` and every sparse `P ⊆ 𝒮₁` there is a Steiner system `𝒮₂` with `𝒮₁ ∩ 𝒮₂ = P`, and blocks of `𝒮₁ \ P`, `𝒮₂ \ P` share at most `r` points. |
| `steiner_intersection_exact` | Every sparse partial Steiner system is the exact intersection of two Steiner systems. |
| `partialSteiner_intersection_embedding` | Every finite partial Steiner system (on any finite set) is, after an injection into `Fin N`, the exact intersection of two `(N, q, r)`-Steiner systems, for every large admissible `N`. |
| `steiner_intersection_spectrum`, `steiner_intersection_spectrum_poly` | **Intersection numbers.** For every `k` with `2 binom(q,r)^2 k ≤ binom(⌊ε n⌋, r)`, in particular for every `k ≤ c n^r`, there are two Steiner systems with exactly `k` common blocks. |
| `exists_two_fold_design_split` | A `2`-fold design that is the disjoint union of two Steiner systems, in which two distinct blocks share at most `r` points. |
| `sts_disjoint_mate_and_spectrum` | The case of Steiner triple systems (`q = 3`, `r = 2`). |

*Proof ideas.* Let `H` be the `r`-graph covered by `P`; `K_n^r \ H` is divisible and has minimum
degree `≥ (1-ε)n`. The blocks of `F` all of whose `r`-sets lie in `K_n^r \ H` form a packing of it,
and Theorem 6.3 gives a decomposition `𝒬₂` of `K_n^r \ H` whose cliques meet those blocks in at
most `r < q` points, so `𝒬₂ ∩ F = ∅` and `𝒮 = P ∪ 𝒬₂`. Intersections: complete `P` to `𝒮₁`, then
apply the avoiding completion with `F = 𝒮₁`. Spectrum: a partial system with exactly `k` blocks
inside a set `U` of `⌊ε n⌋` points exists by the greedy count `card_psFamily_ge`
(using `binom(u,q) binom(q,r) = binom(u,r) binom(u-r,q-r)`), and its covered graph has
`(r-1)`-degrees at most `|U|`.
