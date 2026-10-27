---
title: 'Refined absorption: formalization and reproducibility companion'
author: 'Juan Pablo Traverso Gianini'
date: '27 October 2026'
---

**Companion to** *Formalizing refined absorption: proof interfaces and consequences*, research note, preprint 1.0.

**Editorial draft — 27 October 2026.** The formal freeze is complete; DOI reservation and the public document release remain pending.

© 2026 Juan Pablo Traverso Gianini. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Abstract

This companion identifies the proved declarations, source versions and reproducibility evidence accompanying the research note. The formal freeze contains 316 local Lean sources and the evidence from a clean project Lake campaign, with pinned dependency caches reused. Its 360 endpoint axiom queries report only the three stated foundational axioms or no axioms. We distinguish the complete local build, the aggregate import root, the selected comparison interfaces and Palomar's separate verification. We also record the additive ambient-vertex interface, the survey embedding qualification, the exact scope of the intersection and scheduling results, and the pinned external proofs that close the quantitative assembly.

## 1. Mathematical sources and scope

The two principal texts are Delcourt–Postle [1], with statement baseline arXiv:2402.17855v1, and Postle [2], developed against arXiv:2510.19978v1. The survey's published identifier is DOI 10.1137/25M1805977, ICM 2026, Volume 6, pages 212–231. Its Conjecture 1.1, Theorem 1.10, Definitions 3.6–3.7 and Lemma 3.8 were checked in that edition. This is a check of the identified statements, not whole-document equivalence between editions.

The formalization contains the principal absorption, dense decomposition and design-existence endpoints listed below. The arbitrary-index endpoint proves existence of simple block families for all fixed $q>r\ge2$ and $\lambda\ge1$ at all sufficiently large admissible orders. It is not restricted to the Steiner case. General high-girth applications remain outside this scope.

The source theorem authors retain mathematical attribution. The note explains interfaces and derives consequences from proved inputs. Classical triple-system intersection work [10,11] is acknowledged; historical priority for each general-parameter consequence is not asserted. The Nash–Williams input is attributed to Delcourt–Postle [7], with the reused formal proof documented in [8,9].

## 2. Canonical endpoints

The following tables identify the eighteen declarations selected by the three comparison configurations. Their full types are in the standalone Challenges; the source extraction spans and hashes are in `provenance/palomar-extractions.json`. Every selected name occurs in the frozen axiom-query outputs. The library contains further proved declarations beyond this selection.

### 2.1. Original article

| Source result | Canonical declaration |
| --- | --- |
| [1, Theorem 1.7] | `RefinedAbsorption.Faithful2024.theorem_1_7` |
| [1, Theorem 1.11] | `RefinedAbsorption.Faithful2024.theorem_1_11` |
| [1, Theorem 6.1] | `RefinedAbsorption.Original2024.theorem_6_1` |
| [1, Theorem 2.8] | `RefinedAbsorption.Pending.theorem_2_8` |
| [1, Theorem 6.2], ambient clause exposed | `RefinedAbsorption.Faithful2024.theorem_6_2_ambient` |
| [1, Theorem 6.3] | `RefinedAbsorption.Pending.theorem_6_3` |

The first two endpoints retain explicit host vertex sets and the distinction between bounded edge usage, bounded member size and the refinement degree of a family. The reserve theorem uses labelled edge copies, degree bounds on the designated root set and the stated ambient intersection. It does not substitute global near-regularity or an edge-count cap for that contract.

The old `RefinedAbsorption.Pending.theorem_6_2` remains available. Its absorber predicate uses the edge support of the old graph. The additive endpoint also forbids an absorber edge wholly contained in the full old vertex set. It includes isolated labels and permits mixed old/new edges. The inherited namespace `Pending` is not a statement that these proved endpoints remain open.

### 2.2. Survey

| Source or qualification | Canonical declaration |
| --- | --- |
| [2, Theorem 1.10] | `RefinedAbsorption.Final.theorem_1_10` |
| [2, Conjecture 1.1], fixed index at least one | `RefinedAbsorption.existenceConjecture_proved` |
| Steiner existence specialization | `RefinedAbsorption.Final.existenceConjecture_steiner` |
| Negation of literal global embedding conclusion | `RefinedAbsorption.FaithfulSurvey2025.not_generalEmbeddingLemmaLiteral` |
| Proved piecewise replacement | `RefinedAbsorption.FaithfulSurvey2025.generalEmbedding_piecewise` |

The last two rows are distinct claims. The global predicate uses old vertices occurring in the indexed pieces. The perfect-matching witness covers all old vertices, so it also refutes the printed conclusion on the full old vertex set. No general definitional identity across every unused-vertex convention is inferred from that witness.

The survey's proof reference [4, Appendix B] was followed. Its proof exists; it also writes a global injection. The piecewise theorem permits separate injective maps, with the host conditions and distinct images of new edges. It must not be reported as a proof of the global assertion.

### 2.3. Research note

| Location in the note | Canonical declaration |
| --- | --- |
| Theorem 5.1 | `RefinedAbsorption.Extensions.steiner_completion_avoiding` |
| Corollary 5.2(i) | `RefinedAbsorption.Extensions.steiner_intersection_prescribed` |
| Corollary 5.2(ii) | `RefinedAbsorption.Extensions.partialSteiner_intersection_embedding` |
| Proposition 5.3 | `RefinedAbsorption.Extensions.steiner_intersection_spectrum_poly` |
| Theorem 6.2, every existing system | `RefinedAbsorption.Assembly.steiner_quantitatively_almost_resolvable` |
| Theorem 6.2, existence | `RefinedAbsorption.Assembly.exists_quantitatively_almost_resolvable_steiner` |
| Theorem 6.3 | `RefinedAbsorption.Assembly.nash_williams_scheduled_decomposition` |

The intersection endpoints are in `RefinedAbsorption/Extensions/Intersection.lean`. They use the compatible decomposition theorem, ordinary sparse completion and finite packing lemmas. The three closed quantitative endpoints are in `RefinedAbsorption/Assembly.lean`. Their older conditional predecessors are retained unchanged.

## 3. Quantifiers and representation

For completion and prescribed sparse intersections, fix $q>r\ge1$ first. The positive sparsity constant and order threshold are chosen before the ambient order and the partial systems. Sparsity concerns $\Delta_{r-1}(H(P))$, the covered $r$-graph. The forbidden partial system need not be sparse. The additional crossing guarantee is restricted to forbidden blocks whose $r$-edges avoid $H(P)$.

For arbitrary-index existence, fix $q>r\ge2$ and $\lambda\ge1$ before choosing the order threshold. The threshold may depend on all three parameters. The admissibility condition uses that index; no uniform threshold over all indices is asserted.

For finite exact-intersection embedding, a given finite partial system determines an order threshold. Every larger admissible order admits an injection and two systems with precisely the image block family in common. The injection is chosen with the systems; the endpoint does not quantify over every previously prescribed injection. The spectrum endpoint chooses both systems and gives an initial interval $0\le k\le c n^r$.

The universal Steiner-colouring result fixes $q>r\ge2$, then chooses $\gamma,n_0$ before $n$ and the Steiner system. The existence variant adds admissibility. Lean writes the point-degree quotient as natural division before casting to the reals:
$$
R=\frac{\binom{n-1}{r-1}}{\binom{q-1}{r-1}}.
$$
The counting proof establishes exact divisibility for a Steiner system, so this is the ordinary point degree, rather than a floor approximation. The formal colour map is defined on finite vertex sets and is constrained on the system's blocks. Its number of labels satisfies
$$
R\le m\le R+R^{1-\gamma}.
$$
Unused labels are allowed. The note consequently states an upper bound on the number of partial parallel classes, with the lower bound justified separately.

For the graph application there are universal constants $\gamma,n_0$ before the finite graph. The hypotheses are triangle divisibility, sufficiently large order and the exact inequality
$$
3n\le4\delta(G).
$$
The output is an actual triangle decomposition and a proper colouring of its triangle hypergraph, with
$$
\Delta(G)/2\le m
\le\Delta(G)/2+(\Delta(G)/2)^{1-\gamma}.
$$
No near-regularity hypothesis on the graph, external theorem premise or spanning-factor conclusion appears. Both quantitative applications have $0<\gamma<1$.

Finite types and decidable-equality instances are representation parameters. The selected contracts use ordinary finite types in universe zero. Block families are finite sets, so the fixed-index existence result does not allow repeated blocks. The name `steiner_orthogonal_mate` elsewhere in the library denotes bounded cross-intersections and no common blocks; classical Steiner orthogonality is not asserted.

## 4. Proved external assembly

The source pin for Pippenger–Spencer is

`b19273396d369332fb489fe07e61e27c9e7f9233`

in `jtraverso/pippenger-spencer`. The installed cut contains `Basic.lean`, `ColourHypergraph.lean` and `Polynomial.lean` under `RefinedAbsorption/Upstream/PippengerSpencer/`. Only import routes and line endings changed. Nineteen shared matching sources were verified identical after import-prefix substitution and are reused from the Nash–Williams dependency. Original and installed byte hashes, including CRLF/LF normalization, are recorded in `provenance/assembly-sources.json`.

The polynomial colouring endpoint is `Pseudorandom.chromatic_index_polynomial`. It is proved through the Ehard–Glock–Joos input [6], using an auxiliary colour hypergraph and completion. Its exact contract includes maximum degree, polynomial codegrees and an exponential edge-count cap. It has no lower-degree condition. This is not an assertion that [5] prints that exact quantitative formulation.

The Nash–Williams dependency is `jtraverso/nash-williams-lean` at

`2603197abdbf0a600ec663f6f046f70fbd209d4a`.

The actual endpoint is `NashWilliams18.PaperI.nash_williams_via_paperII`, imported from `RequestProject.NW18.PaperIIAssembly`. The local module `RefinedAbsorption.ExternalProofs` supplies both contracts by direct application of these proved endpoints. The three final declarations in `RefinedAbsorption.Assembly` therefore have neither external theorem hypothesis.

The local module root was relocated from `RequestProject` to `RefinedAbsorption` to avoid a collision with the dependency's module routes. Mathematical declaration namespaces were preserved. The source-cut licence and correspondence records are included in the repository.

## 5. Build, axioms and preservation

The formal source commit is

`5428ee9b772e67dd7ec6da443199b36a003b72d4`.

It is identified by the local formal-source tag `formal-v1.0`. The toolchain is `leanprover/lean4:v4.35.0-rc3`; Mathlib is pinned to

`c55e6e786f49471c72fbddbec5415808896aec1e`.

The manifest fixes ten Git dependencies, including Nash–Williams. Their actual checkout revisions and clean tracked trees were checked. The default Lake targets are `RefinedAbsorption`, `checks` and `Palomar`. The aggregate root imports all 300 local library modules. Ten check modules and six standalone interface modules are additional explicit targets, giving 316 local sources.

The campaign began with the project build directory absent. Pinned dependency caches were reused; a cold rebuild of Mathlib and the whole dependency development is not claimed. After 129 completed modules, the bounded scheduler was resumed using width-one chains, checking saved source hashes and genuine Lake traces. The continuation included two additive source-fidelity modules and completed all 310 library/check targets, followed by the actual default build. The six Palomar interfaces were then registered and compiled sequentially, followed by another successful default build.

One aggregate-root attempt failed because its module documentation preceded imports. Moving that comment after the imports corrected the packaging error. A resumption attempt also exposed a Windows text-decoding issue; the helper was corrected to read UTF-8 traces explicitly. No retained mathematical declaration changed. Failed logs and the corrected campaign history remain in `publication/assembly/`.

After the inputs were committed, the freeze validator compared every Lean source and configuration file with the committed bytes, ran Lake's rehash/no-build freshness check, checked genuine traces and recorded source and artifact hashes. This is a continuation of one clean project campaign, not a claim that each module was compiled exactly once.

| Check module | Queries |
| --- | ---: |
| `AxiomCheck` | 290 |
| `ExtensionsAxioms` | 14 |
| `FaithfulAxioms` | 13 |
| `IntersectionAxioms` | 11 |
| `Original2024Axioms` | 14 |
| `PendingAxioms` | 2 |
| `PendingEndpoints` | 3 |
| `QuantitativeAxioms` | 7 |
| `AssemblyAxioms` | 5 |
| `SourceFidelityAxioms` | 1 |
| Total | 360 |

These are queries, not a claim of 360 distinct theorem names. The outputs contain only `propext`, `Classical.choice` and `Quot.sound`, or no axioms. The retained proof development has no unresolved proof hole or project axiom. The Challenges deliberately contain eighteen statement placeholders; their Solutions do not import them and supply the actual proofs. “Axiom-free” would be inaccurate.

All 300 original returned Lean sources are retained. The migration's comparison reports no textual declaration-header differences and no change to 821 comment/whitespace-normalized non-proof declaration spans. The later import relocation preserves all 301 migrated sources modulo its documented prefix substitution. These are textual checks, not a cross-version kernel equivalence theorem. The older direct-Lean migration record, with 301 sources and 354 queries, remains historical evidence and is not substituted for the final Lake certificate.

## 6. Archive and reproduction

The immutable formal archive is

`publication/formal-freeze/formal-v1.0-5428ee9b772e.tar.gz`,

with SHA-256

`e9bb21b17a110a392a7751afefb9a2e9d6bf218c7e6dac788006234f3af09c05`.

It contains the source commit and the completed build evidence. The external `FREEZE.json` receipt and SHA sidecar identify that archive. The validation record `publication/assembly/VALIDATION.json` has SHA-256

`45321434a170482d8473182ecc8c1fd60b66a84bb9480ef7f6c26f9f2b130157`.

From the complete publication checkout, `python tools/verify_formal_freeze.py` checks current and archived source correspondence, archive integrity, the original-source archive and the recorded axiom logs. It does not execute Lean or independently replay proofs. The formal archive cannot contain its own archive-hash receipt; use the complete publication checkout for that convenience checker.

For a fresh proof reconstruction, use a separate checkout of the formal source commit, or extract the formal archive, install the pinned Lean toolchain, and run:

```sh
lake exe cache get
lake build
```

The public manifest uses immutable Git revisions. Machine-local override paths used in the recorded Windows campaign are ignored by Git and are not needed by this portable configuration. Compiled artifact hashes describe the recorded platform; a reconstruction on another platform need not reproduce those binary bytes.

The manuscripts are maintained in English and Spanish Markdown, then converted through the author's Nash–Williams series template to final TeX and PDFs. Rendered-page inspection, bilingual parity and document hashes are separate from the formal-source freeze. Later document and metadata commits can retain the frozen Lean/configuration bytes; exact publication and registry commits are recorded in their own receipts.

## 7. Comparison and review boundary

The comparison configurations are `Palomar/Article2024.comparator.json`, `Palomar/Survey2025.comparator.json` and `Palomar/ResearchNote.comparator.json`. Each has a standalone Mathlib-only Challenge and a Solution importing the relevant proofs. Definitions in the Challenges have specified bodies; only the theorem statements have deliberate placeholders.

Local compilation and the axiom report establish the evidence described above. Palomar's complete preflight, Challenge/Solution comparison, independent kernel check, editorial review and registration are further stages with separate receipts. This companion does not turn a local build into such a certificate.

The internal review is performed by Codex under the author's direction and is recorded as self-assessment. Aristotle contributed proof development and formalization; Codex contributed migration, assembly, the additive ambient interface, exposition and release preparation. The author accepts responsibility for the work. No independent human peer review is claimed.

## References

[1] M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*, arXiv:2402.17855v1 (2024). <https://doi.org/10.48550/arXiv.2402.17855>.

[2] L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory*, Proceedings of the International Congress of Mathematicians 2026, Volume 6, 212–231. <https://doi.org/10.1137/25M1805977>. Statement baseline: arXiv:2510.19978v1 (2025), <https://doi.org/10.48550/arXiv.2510.19978>.

[3] M. Delcourt and L. Postle, *Finding an Almost Perfect Matching in a Hypergraph Avoiding Forbidden Submatchings*, arXiv:2204.08981. <https://doi.org/10.48550/arXiv.2204.08981>.

[4] M. Delcourt, C. Henderson, T. Lesgourgues and L. Postle, *Erdős meets Nash-Williams*, arXiv:2507.23624v1 (2025), Appendix B. <https://doi.org/10.48550/arXiv.2507.23624>.

[5] N. Pippenger and J. Spencer, *Asymptotic behavior of the chromatic index for hypergraphs*, Journal of Combinatorial Theory, Series A 51 (1989), 24–42. <https://doi.org/10.1016/0097-3165(89)90074-5>.

[6] S. Ehard, S. Glock and F. Joos, *Pseudorandom hypergraph matchings*, Combinatorics, Probability and Computing 29(6) (2020), 868–885. <https://doi.org/10.1017/S0963548320000280>.

[7] M. Delcourt and L. Postle, *A Proof of Nash-Williams' Conjecture*, arXiv:2606.11178 (2026). <https://doi.org/10.48550/arXiv.2606.11178>.

[8] J. P. Traverso Gianini, *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean*, preprint 1.0 (2026). <https://doi.org/10.5281/zenodo.23428173>.

[9] J. P. Traverso Gianini, *Triangle decompositions II: Robust absorption for typed triangles*, preprint 1.0 (2026). <https://doi.org/10.5281/zenodo.23502224>.

[10] C. C. Lindner and A. Rosa, *Steiner triple systems having a prescribed number of triples in common*, Canadian Journal of Mathematics 27(5) (1975), 1166–1175. <https://doi.org/10.4153/CJM-1975-122-4>.

[11] C. C. Lindner and A. Rosa, *Steiner triple systems having a prescribed number of triples in common (corrigendum)*, Canadian Journal of Mathematics 30(4) (1978), 896. <https://doi.org/10.4153/CJM-1978-077-9>.

[12] L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, Automated Deduction — CADE 28 (2021), 625–635. <https://doi.org/10.1007/978-3-030-79876-5_37>.

[13] The mathlib Community, *The Lean Mathematical Library*, Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (2020), 367–381. <https://doi.org/10.1145/3372885.3373824>.
