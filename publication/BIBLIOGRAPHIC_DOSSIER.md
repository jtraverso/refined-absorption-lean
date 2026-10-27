# Bibliographic and version dossier

Checked on 27 October 2026. This dossier supports attribution and precise version references. It does not establish historical priority for the consequences in the note.

## Two principal source texts

1. Michelle Delcourt and Luke Postle, *Refined Absorption: A New Proof of the Existence Conjecture*, arXiv:2402.17855v1 (2024), DOI [10.48550/arXiv.2402.17855](https://doi.org/10.48550/arXiv.2402.17855). The formal statement layer uses this version. Primary full text: <https://arxiv.org/html/2402.17855v1>. The article's Theorems 1.7, 1.11, 2.8, 6.1, 6.2 and 6.3 have distinct canonical endpoints. Its results and proof strategy remain attributed to Delcourt–Postle.

2. Luke Postle, *Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory*, Proceedings of the International Congress of Mathematicians 2026, Volume 6, pp. 212–231, DOI [10.1137/25M1805977](https://doi.org/10.1137/25M1805977). Primary published text: <https://epubs.siam.org/doi/10.1137/25M1805977>. The formalization was developed against arXiv:2510.19978v1 (2025), DOI [10.48550/arXiv.2510.19978](https://doi.org/10.48550/arXiv.2510.19978), <https://arxiv.org/html/2510.19978v1>. The published DOI identifies the survey; its arXiv version identifies the statement baseline. This is one work in two versions, not two independent mathematical sources.

The published survey's Definitions 3.6–3.7 and Lemma 3.8 were checked against the corresponding arXiv definitions. The global injection in Definition 3.7 and the relevant conclusion of Lemma 3.8 remain present. The formal counterexample is therefore described with both version locations. No whole-document equivalence between the two editions has been established.

The last returned round also proves `RefinedAbsorption.existenceConjecture_proved : ExistenceConjecture` for all fixed q > r ≥ 2 and λ ≥ 1. It produces a finite set of blocks, so blocks are not repeated. Its proof is in Multigraph/Existence.lean and was already included in the migrated axiom audit. Earlier scope notes that restricted the established existence theorem to λ = 1 are superseded by this source-level finding. This is a formalization of the cited existence theorem, not a new mathematical existence theorem.

## Following the survey's proof reference

The survey refers to reference [10] for its embedding lemma. That reference is Michelle Delcourt, Cicely (Cece) Henderson, Thomas Lesgourgues and Luke Postle, *Erdős meets Nash-Williams*, arXiv:2507.23624v1 (2025), DOI [10.48550/arXiv.2507.23624](https://doi.org/10.48550/arXiv.2507.23624). Primary text: <https://arxiv.org/html/2507.23624v1>.

Its Appendix B contains Definitions B.1–B.2, Lemma B.3 and a proof. Definition B.2 also writes a global injection. The extension argument controls new-edge collisions and local degree loads. That observation is consistent with the distinction exposed by the formalization; it is not an assertion about the authors' intended definition. The note must not say that no proof is available. The mathematical obstruction is the formally checked global-injection counterexample, rather than an absence of a cited proof. A perfect matching has no isolated vertices, so the additional no-isolated-vertices assumption in the graph version does not remove this obstruction.

## The original article's abbreviated steps

Theorem 2.8 of the article refers to Michelle Delcourt and Luke Postle, *Finding an Almost Perfect Matching in a Hypergraph Avoiding Forbidden Submatchings*, arXiv:2204.08981, DOI [10.48550/arXiv.2204.08981](https://doi.org/10.48550/arXiv.2204.08981). The local proof of 2.8 is checked against the full retained contract for labelled multi-hypergraphs. A special-purpose nibble consumer is not substituted for that contract.

In Section 6.3 of arXiv:2402.17855v1, the discussion following Lemma 6.4 describes two modifications and omits their details. Its final paragraph prints an upper bound of order n^(q−r+1) for forbidden q-sets through a fixed r-edge. The formal counting lemma establishes the stronger bound 2^r q n^(q−r−1). The latter is the bound used in the formal deletion argument. The larger printed upper bound is not itself contradicted by a stronger upper bound; it does not provide the saving needed for that deletion argument. This distinction must be preserved in the note.

The deduction of Theorem 6.2 from 6.3 is made explicit in the library by deleting a complete graph on an admissible old vertex set from a much larger admissible complete graph, then applying 6.1 and 6.3. The deduction and its elementary construction may be explained without reproducing the main absorption proof.

## External proved inputs for scheduling

- Nicholas Pippenger and Joel Spencer, *Asymptotic behavior of the chromatic index for hypergraphs*, Journal of Combinatorial Theory, Series A 51 (1989), pp. 24–42. DOI [10.1016/0097-3165(89)90074-5](https://doi.org/10.1016/0097-3165(89)90074-5). This is the classical colouring result and context, not a claim that its printed theorem has the exact polynomial contract used here.
- Stefan Ehard, Stefan Glock and Felix Joos, *Pseudorandom hypergraph matchings*, Combinatorics, Probability and Computing 29 (2020). DOI [10.1017/S0963548320000280](https://doi.org/10.1017/S0963548320000280). The polynomial colouring endpoint in the pinned Pippenger–Spencer library is a consequence of their Theorem 1.2 via an auxiliary colour hypergraph and greedy completion.
- Michelle Delcourt and Luke Postle, *A Proof of Nash-Williams' Conjecture*, arXiv:2606.11178 (2026), DOI [10.48550/arXiv.2606.11178](https://doi.org/10.48550/arXiv.2606.11178). This is the mathematical source for the graph decomposition input.
- Juan Pablo Traverso Gianini, *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean*, DOI [10.5281/zenodo.23428173](https://doi.org/10.5281/zenodo.23428173), and *Triangle decompositions II: Robust absorption for typed triangles*, DOI [10.5281/zenodo.23502224](https://doi.org/10.5281/zenodo.23502224). These describe the formal decomposition input actually reused, including its replacement constructions. They do not transfer authorship of the Nash–Williams theorem to the formalizer.

Exact formal source revisions, source-cut hashes and reused module identities are in provenance/assembly-sources.json. The three imported Pippenger–Spencer source files keep their mathematical declarations; nineteen shared matching modules are reused from the pinned Nash–Williams dependency after verifying their import-normalized identity. The polynomial contract includes an edge-count cap and no minimum-degree hypothesis. Both facts matter in its applications.

## Classical intersection literature and claim boundaries

Curt C. Lindner and Alexander Rosa, *Steiner triple systems having a prescribed number of triples in common*, Canadian Journal of Mathematics 27 (1975), pp. 1166–1175, DOI [10.4153/CJM-1975-122-4](https://doi.org/10.4153/CJM-1975-122-4), with the corrigendum, Canadian Journal of Mathematics 30 (1978), p. 896, DOI [10.4153/CJM-1978-077-9](https://doi.org/10.4153/CJM-1978-077-9). The primary publisher records and the corrigendum were checked. The note cites both and does not reproduce an uncorrected complete spectrum.

Disjoint mates and intersection problems for Steiner triple systems are classical. The formalized initial interval k ≤ c n^r is a uniform consequence of a completion interface for fixed q and r; it is not advertised as the complete intersection spectrum or as a new solution of the classical triple-system problem. No exhaustive priority search has been completed for every general-parameter corollary. Consequently the note claims a verified derivation and reusable interfaces, not historical novelty for each endpoint.

## Bibliographic release checks still required

Before release, check the final bibliography against these records, include the reserved research-note DOI, identify the exact formal freeze, and verify that both language editions use the same references and source-version qualifications. Check all links and the actual metadata schema at the time of publication. This dossier alone is not a release PASS.
