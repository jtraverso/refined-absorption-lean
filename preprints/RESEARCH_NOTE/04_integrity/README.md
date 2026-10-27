# Integrity and package boundaries

There are two distinct freezes:

1. **Formal-source freeze:** immutable archive and external receipt under [publication/formal-freeze](../../../publication/formal-freeze/). It binds the actual completed formal campaign to source commit `5428ee9b772e67dd7ec6da443199b36a003b72d4`.
2. **Final document release:** preprint 1.0 manuscripts, companions and audit records containing the actual reserved DOI `10.5281/zenodo.23685654`. Its manifest is generated only after final text, TeX/PDF, bilingual and rendered-page checks. A later content or template change requires refreshed artifacts, reports, hashes and a new bundle.

`DOCUMENT_MANIFEST.json` and `SHA256SUMS.txt` bind the four MD/TeX/PDF triples, reports and reproducibility/license/navigation files in this preprint folder. The manifest excludes itself, its checksum list and ignored local render images to avoid recursive hashes. `publication/document-release/` holds the final archive and an external receipt identifying its scope and hash. The earlier DOI-pending bundle under `publication/document-draft/` remains historical; its receipt refers to that bundle's own archived manifest and the recorded earlier Git snapshot.

The 35-page visual acceptance is in [VISUAL_REVIEW.json](../02_validation/VISUAL_REVIEW.json); source/TeX/PDF hashes and mechanical checks are in [AUDIT_RESULT.json](../02_validation/AUDIT_RESULT.json). The original first-pass layout findings remain recorded. Neither a checksum nor a compiler exit code substitutes for semantic or visual review.

For the complete recorded formal freeze, run `python tools/verify_formal_freeze.py` from the repository root. For the document manifest, recompute SHA-256 for every listed path relative to the repository root and compare it with the recorded value.
