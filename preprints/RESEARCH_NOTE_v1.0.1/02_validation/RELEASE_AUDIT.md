# Internal release audit — preprint 1.0.1

**Final internal audit: PASS.** Editorial verdict: `EDITORIALLY_READY`.
Release decision is governed by `RELEASE_AUDIT.json`, generated after all checks and visual acceptance. This report is an internal agent assessment under the author's direction, not independent human peer review.

| Check | Acceptance evidence |
| --- | --- |
| Mathematical exposition and source fidelity | Reviewed reserve-load summation, forbidden-block count, compatible-absorber construction, counterexample hypotheses, completion chain and both colouring applications; source locators in `SOURCE_AND_LITERATURE_DOSSIER.md`. |
| Scope and attribution | Both source texts are named; partial coverage and the exact efficiency bound are explicit. The note does not claim a new independent proof, an improved Nash–Williams threshold, a complete spectrum or general high-girth coverage. |
| Quantifiers, formulas and proof preservation | Exact formula sequence and protected-body comparison against the reviewed baseline; final diffs in `SEMANTIC_INTEGRITY.json`. |
| Spanish/English parity | Corresponding math-block inventories, display sequences, code identifiers, heading hierarchy and DOI order match. |
| Editorial voice | Concrete hypotheses and transitions explain each deduction. Standard tool lists have been removed from the author's agreed disclosure; two remaining untranslated phrases in the companion are corrected. |
| Typesetting | Four PDFs compiled from the delivered TeX, three passes each; no overfull boxes, missing characters, undefined references or LaTeX errors. |
| Visual review | All 43 final pages inspected; identifiers, Greek symbols, divisibility, unions, inequalities and tables checked. Orphaned commit introductions and command-block pagination corrected. See `VISUAL_QA.json`. |
| Formal preservation | All 317 Lean files and Lake configuration preserved; original freeze integrity checked, 360 recorded queries and 18 selected endpoint names verified. No new proof execution is represented as having occurred. |
| Current metadata | Version 1.0.1, title and new DOI agree across documents, CITATION.cff, README, publication index and the four current YAML profiles. Historical receipts remain bound to their original source. |
| Historical publication | The public 1.0 manuscripts, archives and receipts remain byte-identical; the new DOI is a new version in the existing Zenodo record family. |

## Corrections made in this release audit

1. Replaced draft banners and the old cover DOI with the new version metadata; clarified the old release in the code-availability section.
2. Corrected two untranslated Spanish companion expressions.
3. Kept commit introductions and reproduction instructions with their values or code blocks.
4. Updated stale publication summaries that still described the original Zenodo publication and official preflight as pending.
5. Added a coverage table, updated citation metadata and supplied a repository change log.

The final automated audit must return `PASS` before upload/publication. Public GitHub and Zenodo outcomes are verified separately in additive receipts under `publication/github/v1.0.1/` and `publication/zenodo/v1.0.1/`. Their existence must not be inferred from this internal editorial verdict.

Remaining full-paper formalization and final Palomar registration are outside the scope of this documentary release, explicitly disclosed rather than marked as completed. The historical preferred-size warning in the official preflight is retained; it was not an error and does not justify modifying the frozen comparison during an editorial update.
