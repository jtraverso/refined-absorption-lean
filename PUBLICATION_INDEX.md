# Publications and evidence

## Current documents: preprint 1.0.1

[Formalizing Delcourt–Postle’s refined absorption in Lean](preprints/RESEARCH_NOTE_v1.0.1/README.md) is the editorial update, with its separate companion in English and Spanish. DOI: [10.5281/zenodo.23715622](https://doi.org/10.5281/zenodo.23715622). [GitHub release](https://github.com/jtraverso/refined-absorption-lean/releases/tag/preprint-v1.0.1). The [release audit](preprints/RESEARCH_NOTE_v1.0.1/02_validation/RELEASE_AUDIT.md) records the checks; the [change log](CHANGELOG.md) describes the revision.

The 317 Lean files, Lake configuration, dependency pins, proof freeze and existing Palomar receipts are unchanged. Current YAML metadata cites the new document DOI; this does not renew the official preflight or submit a new registry entry. General high-girth applications and complete coverage of the two source texts remain outside this release.

Published from commit `fd36d7d22f35946bdd38c3e092a053cecbf04b49`. The [GitHub receipt](publication/github/v1.0.1/RELEASE.json) verifies all eight release assets; the [Zenodo receipt](publication/zenodo/v1.0.1/PUBLISHED_RECORD.json) verifies the four deposited PDFs. These additive receipts preserve the earlier release evidence.

## Preserved publication and verification history


The original publication is a research note with a separate formalization and reproducibility companion. Both are available in English and Spanish. **Preprint 1.0: internal audit PASS. Published openly on [Zenodo](https://zenodo.org/records/23685654), DOI [10.5281/zenodo.23685654](https://doi.org/10.5281/zenodo.23685654).** The four deposited PDF checksums match the final local files; see the [publication receipt](publication/zenodo/PUBLISHED_RECORD.json).

Start with the [document index](preprints/RESEARCH_NOTE/README.md), the [internal review summary](preprints/RESEARCH_NOTE/02_validation/REVIEW_SUMMARY.md) or the [formal freeze receipt](publication/formal-freeze/FREEZE.json).

The two mathematical source works are:

| Work | DOI | Formal statement basis |
| --- | --- | --- |
| Delcourt–Postle, *Refined Absorption: A New Proof of the Existence Conjecture* | [10.48550/arXiv.2402.17855](https://doi.org/10.48550/arXiv.2402.17855) | arXiv:2402.17855v1 |
| Postle, *Refined Absorption: A New Proof of the Existence Conjecture and Its Applications to Extremal and Probabilistic Design Theory* | [10.1137/25M1805977](https://doi.org/10.1137/25M1805977) | arXiv:2510.19978v1; identified statements checked against the published edition |

The note's quantitative application reuses the proof documented in the author's Nash–Williams [Paper I](https://doi.org/10.5281/zenodo.23428173) and [Paper II](https://doi.org/10.5281/zenodo.23502224). Those papers remain in their existing publication repository.

The canonical Palomar entry uses `Palomar/Unified.comparator.json` and selects eighteen endpoints together: six from the article, five from the survey/fidelity analysis and seven from the note. All three principal DOIs are retained in `Palomar/Unified/formalization.yaml`. The three narrower profiles remain historical views. The [joint comparison record](publication/palomar/UNIFIED_COMPARISON.md) explains the additive interface and unchanged proof freeze. Official preflight, submission, review and registration require their actual receipts.

The [public preprint 1.0 release](https://github.com/jtraverso/refined-absorption-lean/releases/tag/preprint-v1.0) contains the four final PDFs, document and formal archives, and checksums. All ten original assets match their local SHA-256 digests; see [the release receipt](publication/github/RELEASE.json). The earlier separate preflights and the canonical joint run are tracked in [PREFLIGHT_RUNS.json](publication/palomar/PREFLIGHT_RUNS.json).

The same release also carries the additive joint comparison archive, its checksum and its freeze receipt (thirteen assets in total). The [supplement receipt](publication/github/UNIFIED_SUPPLEMENT.json) distinguishes comparison source `867d1e3d5e48ef20a8f1ae68237834eb06211cbc` from the original document release; the original ten assets and published PDFs are unchanged.

The joint [official full preflight](publication/palomar/OFFICIAL_PREFLIGHT.json) passed for all eighteen selected declarations, with NanoDa and con-ron replay and no errors. Its sole warning concerns the preferred Challenge review size; the file remains within the hard caps. The [ordinary submission receipt](publication/palomar/SUBMISSION_RECEIPT.json) records intake `jne18fh5pbug` after the author's explicit confirmation of the exact source and maintainer relationship. The [submission status](publication/palomar/SUBMISSION_STATUS.json) records the service's separate verification. No editorial outcome or registration is claimed before the corresponding evidence and the author's decision.
