# Internal audit and publication status

Current document version: **1.0.1**. Internal reviewer: Codex under Juan Pablo Traverso Gianini's direction; not independent human peer review.

The current [release audit](../preprints/RESEARCH_NOTE_v1.0.1/02_validation/RELEASE_AUDIT.md) and its machine-readable result separate document checks from recorded formal evidence and actual public-release outcomes. The [change log](../CHANGELOG.md) describes this editorial update.

| Scope | Status | Evidence |
| --- | --- | --- |
| Original clean local Lake campaign | PASS, recorded | `assembly/VALIDATION.json`: 316 sources and 360 queries |
| Additive unified comparison and default build | PASS, recorded | `palomar/unified-build/RESULT.json`: 317 current sources |
| Frozen proof-source correspondence | PASS | `../preprints/RESEARCH_NOTE_v1.0.1/02_validation/FORMAL_PRESERVATION.json`; no new Lean build claimed |
| Current editorial, bilingual, visual and metadata audit | PASS | `../preprints/RESEARCH_NOTE_v1.0.1/02_validation/RELEASE_AUDIT.json` |
| Original Zenodo publication | PASS, published | `zenodo/PUBLISHED_RECORD.json`, DOI 10.5281/zenodo.23685654 |
| Original GitHub release | PASS, published | `github/RELEASE.json` and `github/UNIFIED_SUPPLEMENT.json` |
| Version 1.0.1 Zenodo publication | PASS, published; four PDF checksums verified | `zenodo/v1.0.1/PUBLISHED_RECORD.json`, DOI 10.5281/zenodo.23715622 |
| Version 1.0.1 GitHub release | PASS, published; eight asset checksums verified | `github/v1.0.1/RELEASE.json`, tag `preprint-v1.0.1` |
| Official unified Palomar preflight | PASS, historical | `palomar/OFFICIAL_PREFLIGHT.json`, source commit 867d1e3d5e48ef20a8f1ae68237834eb06211cbc |
| Palomar intake | Recorded; last preserved status `verifying` | `palomar/SUBMISSION_RECEIPT.json` and `SUBMISSION_STATUS.json`, 27 October 2026; not a live status claim |
| Complete coverage of both source texts | Future work, outside 1.0.1 | Current scope is explicit in the README, note and companion |

The current YAML profiles cite the 1.0.1 documents. This bibliographic update does not renew or replace the earlier preflight/submission. No final registry decision is claimed. The old audit text remains available in Git history and the immutable 1.0 release.
