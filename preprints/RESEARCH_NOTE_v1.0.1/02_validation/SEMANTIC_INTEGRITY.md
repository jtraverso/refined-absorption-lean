# Semantic integrity — preprint 1.0.1

Verdict: `EDITORIALLY_READY` for the stated scope of this documentary release.
Reviewer: Codex under Juan Pablo Traverso Gianini's direction; internal review, not independent human peer review.

The semantic baseline is the four reviewed Markdown files retained in `baseline/`.
They contain the changes accepted through the three review rounds and the author's subsequent title and disclosure corrections. They are evidence, not the current deliverables. `SEMANTIC_INTEGRITY.json` gives their hashes, final source hashes and complete finalization diffs; `PROTECTED_ELEMENT_INDEX.json` binds every mathematical span.

## Finalization changes

- The title and the general AI/computational disclosure agreed with the author are retained. The disclosure reproduces Nash–Williams Paper I with Certo/Jacobian citations renumbered to [14]/[15]; no standard typesetting applications have been added to that section.
- Draft labels become preprint 1.0.1; the newly reserved version DOI is 10.5281/zenodo.23715622. The previous version is identified separately in the availability section.
- The Spanish companion heading “Research note” becomes “Nota de investigación”; “packings finitos” becomes “empaquetamientos finitos”. These are translations of existing terms, not changes to definitions.
- TeX spacing keeps introductory sentences with commit identifiers and reproduction commands. The Markdown mathematical content is unaffected.

Quantifiers, assumptions, constants, asymptotic orders, equations, proof dependencies and novelty claims are unchanged from the reviewed baseline. Acknowledgements, the AI disclosure and bibliography are byte-identical at the text-section level. No Lean theorem, proof, import, dependency revision or Lake configuration is modified.

## Changes accumulated since public version 1.0

The review cycle clarified the quantifier order in Corollary 5.2(i), the inclusive interval in Proposition 5.3, the use of Theorem 5.1 before Corollary 5.2(i), and the reserve local-lemma estimate. The codegree exponent is denoted by eta to distinguish it from minimum degree. The colouring input is now numbered Theorem 6.1. The exposition derives the intermediate bound |S| ≤ R² from q|S| = nR and n ≤ qR; no final bound or formal proof is strengthened. The source locators, full counterexample hypotheses, attribution and explicit coverage limitations were expanded. These are recorded editorial clarifications of the existing development, not claims of literal text identity with 1.0.

The note's theorem-to-Lean mapping, exact threshold 3n ≤ 4δ(G), polynomial edge-count cap, choice of the colouring exponent after applying the input, and distinction between excess classes and uncovered vertices were reviewed. The global-injection counterexample and the proved piecewise replacement remain separate assertions. Appendix A retains the order-dependent term in the omni-absorber bound and does not add flatness to its conclusion.

## Evidence and limits

`AUDIT_RESULT.json` binds Markdown, TeX, PDF and render hashes, and checks bilingual formula blocks, displays, identifiers, headings and DOI order. `VISUAL_QA.json` records inspection after the final build. `FORMAL_PRESERVATION.json` checks all 317 Lean source bytes and preserved formal evidence. This release reviews the existing frozen build and 360 axiom-query outputs; it does not claim a fresh Lean build or a new independent-kernel replay.

There are no unresolved content queries blocking this editorial release. General high girth, general partite extensions, probabilistic design thresholds and full coverage of both source texts remain future formalization work. The exploratory versions of Certo/Jacobian were not recorded, as disclosed in the bibliography; those tools are not logical dependencies. No exhaustive priority claim or endorsement by the original authors is asserted.

The previous hold on publication is superseded by the author's explicit instruction to publish 1.0.1 after a passing audit. No contact with the original authors is required or performed.
