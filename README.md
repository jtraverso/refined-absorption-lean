# Refined absorption in Lean

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

Three scoped Palomar interfaces are prepared: `Article2024`, `Survey2025` and
`ResearchNote`. Local compilation, internal review, official preflight and
registry review are distinct gates. No registration is claimed here before a
registry receipt exists.

Source code is licensed under Apache 2.0; manuscripts are licensed under
CC BY 4.0. The author is responsible for the formalization and exposition.
Aristotle contributed mathematical development and formal proofs; Codex
contributed migration, assembly, review, exposition and release preparation.
The internal agent audit is not independent human peer review.
