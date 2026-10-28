# Formalizing Delcourt–Postle’s refined absorption in Lean

Formalization directed by Juan Pablo Traverso Gianini, with assistance from
Harmonic's Aristotle and OpenAI Codex. The mathematical sources are:

| Source | Authors | Statement basis |
| --- | --- | --- |
| *Refined Absorption: A New Proof of the Existence Conjecture* | Michelle Delcourt and Luke Postle | [arXiv:2402.17855v1](https://doi.org/10.48550/arXiv.2402.17855) |
| *Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory* | Luke Postle | [ICM 2026 publication](https://doi.org/10.1137/25M1805977); formal statement baseline [arXiv:2510.19978v1](https://doi.org/10.48550/arXiv.2510.19978) |

The accompanying research note explains proof interfaces, source fidelity and
selected consequences. It does not reproduce the two source papers, and no
historical priority is claimed for every formalized corollary. The original
results remain attributed to their authors.

Read the [research note and formal companion in English or Spanish](preprints/RESEARCH_NOTE_v1.0.1/README.md).
Preprint **1.0.1** is the editorial update to 1.0, with DOI
[10.5281/zenodo.23715622](https://doi.org/10.5281/zenodo.23715622).
It incorporates the three review rounds, clarifies attribution and coverage,
and improves notation, proof exposition and the Spanish text. The Lean sources,
dependency pins and formal freeze are unchanged.

The original [preprint 1.0](preprints/RESEARCH_NOTE/README.md) and its
[DOI](https://doi.org/10.5281/zenodo.23685654) remain available.
The [publication index](PUBLICATION_INDEX.md) distinguishes document versions,
source DOIs, formal evidence and historical Palomar receipts.

## Formal scope

- Refined omni-absorbers and refiners, dense decomposition, labelled reserve
  matchings and compatible decompositions: source article 1.7, 1.11, 6.1, 2.8,
  6.2 and 6.3 have separate endpoints.
- The existence endpoint covers all fixed `q > r ≥ 2` and `λ ≥ 1`, producing a
  finite set of blocks without repetitions at every sufficiently large
  admissible order.
- Completion avoiding an arbitrary partial Steiner system, prescribed sparse
  intersections, finite exact-intersection embedding and an initial
  intersection spectrum of order `n^r` are derived in the library.
- The closed quantitative endpoints partition Steiner blocks into partial
  parallel classes with polynomial excess in their number, and schedule a
  triangle decomposition at the exact Nash–Williams threshold in rounds of
  vertex-disjoint triangles. Their two external contracts are supplied by
  pinned proved endpoints. The original conditional consumers remain available.

The survey's literal global-injection embedding conclusion has a formal
counterexample. The proved piecewise variant is recorded separately. The survey's
cited Appendix B proof is available; the distinction concerns its conclusion.
The witness covers all old vertices, so it is unaffected by conventions about
unused old labels. General high-girth applications are outside the established
scope. These selections do not certify every statement of either source text.

| Coverage | Status in this release |
| --- | --- |
| Selected absorption, refiner, dense/compatible decomposition and existence endpoints | Proved; the companion identifies their exact declarations and hypotheses. |
| Completion, intersections, partial parallel classes and Nash–Williams rounds | Derived consequences; no claim of historical priority or an improved threshold. |
| Quantitative colouring and Nash–Williams inputs | Proved external sources at pinned revisions, imported by the final applications; not mathematical axioms. |
| Foundational axioms | Endpoint queries contain only `propext`, `Classical.choice`, `Quot.sound`, or none. |
| Global embedding conclusion of the survey | Refuted under the definitions specified in note §4.2; the piecewise replacement is a separate theorem. |
| General high girth, general partite extensions and probabilistic design thresholds | Outside the current certified scope; complete coverage is future work. |
| Omni-absorber degree bound | `C max{Δ(X), n^(1−1/r) log n}`; the order-dependent term cannot be dropped without an additional hypothesis. |
| Palomar Challenges | Intentional statement placeholders, separate from all proof imports. |

The additive `Faithful2024.theorem_6_2_ambient` interface makes the entire old
ambient vertex set independent, including isolated labels. It retains the old
support-based endpoint and permits edges containing both old and new vertices.
The name `steiner_orthogonal_mate` means bounded cross-intersections and no common
blocks; it does not assert classical Steiner orthogonality.

## Build and evidence

The project pins Lean `4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, and its Nash–Williams dependency.
With the pinned toolchain installed:

```sh
lake exe cache get
lake build
```

The clean project Lake campaign completed on 27 October 2026: 300 local library
modules, ten axiom-check modules and six Palomar interface modules. The default
targets are `RefinedAbsorption`, `checks` and `Palomar`. The 360 endpoint axiom
queries report only `propext`, `Classical.choice` and `Quot.sound`, or no axioms.
The project output directory was initially absent; pinned dependency caches
were reused. Bounded Lake calls and their resumptions, followed by the actual
default build, are recorded under `publication/assembly/`.

The formal freeze binds committed source bytes, dependency revisions, genuine
Lake traces and artifact hashes. It is separate from the earlier direct-Lean
migration record in `migration/VALIDATION.json`, the later document release audit
and Palomar's official verification. A local build is not a registry receipt.

The aggregate module `RefinedAbsorption.lean` imports the full local proof
library. The `checks` library runs endpoint axiom queries separately. Palomar
Challenges are standalone statement files with intentional `by sorry`
placeholders; Solutions import the actual proof modules and do not import the
Challenges. A Challenge placeholder is not a proof-library theorem.

Exact external revisions, the three-file Pippenger–Spencer source cut and the
nineteen shared matching modules are recorded in
`provenance/assembly-sources.json`. The mathematical namespaces are preserved;
the local module root was relocated to avoid a clash with the dependency's
`RequestProject` root. The polynomial colouring contract includes a maximum
degree bound, a codegree bound and an exponential edge-count cap. It is derived
via Ehard–Glock–Joos in that source development; it is not identified with the
literal statement of the 1989 Pippenger–Spencer theorem.

## Preservation and provenance

All 300 returned Lean sources are retained. The immutable original archive and
its hashes are under `provenance/`. The migration's proof-script adjustments,
the later import relocation and the additive assembly have separate records.
The current preservation audit compares declaration headers and 821 normalized
non-proof declaration spans. It is a textual preservation check, not a
cross-version kernel equivalence proof.

The included original-source archive is sufficient to rerun the preservation
comparisons; no private Aristotle workspace is required. Historical summaries
and ledgers are retained as provenance. Their old pending-status comments are
not the current build or publication status.

## Publication layout and attribution

The research note uses the same manuscript, validation, reproducibility,
integrity and formalization-companion directory layout as the author's
[Nash–Williams Papers I–II release](https://github.com/jtraverso/nash-williams-triangle-decompositions-release).
That repository remains the publication home of those two papers.

The canonical Palomar submission is **one entry**: `Palomar/Unified.comparator.json`
selects all eighteen principal declarations and uses `Palomar.UnifiedSolution` (the existing
`RefinedAbsorption` aggregate root together with `Palomar/Theorem110.lean`) as its Solution.
Theorem 1.10 is selected in its faithful form (`RefinedAbsorption.Final.theorem_1_10_faithful`):
the omni-absorber and refinedness are those of Definitions 1.5 and 1.6 of arXiv:2402.17855, so
every member of the decomposition family is a copy of `K_q^r` in `X ∪ A` with at most one edge of
`X`; it is derived from the faithful Theorem 1.7 with the complete `r`-graph as host. The article, survey and
research note retain separate source attribution and DOI metadata. The three
narrower profiles remain available as historical views; they are not three
intended submissions. See the [joint comparison record](publication/palomar/UNIFIED_COMPARISON.md).

The joint Challenge is additive. The original 316-source formal freeze is
unchanged; the current project has 319 sources, adding the comparison file and the Theorem 1.10
adapter (`Palomar/Theorem110.lean`, `Palomar/UnifiedSolution.lean`). Local compilation, internal review, official preflight and registry review
are distinct gates. The updated note DOI in the current metadata does not
rewrite or renew the historical preflight and submission, which remain bound
to their original commit. No registration is claimed before a registry receipt exists.

Source code is licensed under Apache 2.0; manuscripts are licensed under
CC BY 4.0. The author is responsible for the formalization and exposition.
Aristotle contributed mathematical development and formal proofs; Codex
contributed migration, assembly, review, exposition and release preparation.
The internal agent audit is not independent human peer review.
