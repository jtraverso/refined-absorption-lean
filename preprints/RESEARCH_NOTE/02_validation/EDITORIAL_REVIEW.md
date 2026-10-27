# Internal editorial review

Reviewer: Codex under the author's direction; no independent human review is claimed.

Stage: text review completed; typesetting and full rendered-page acceptance are recorded separately. Overall release verdict remains `EDITORIAL_DRAFT_WITH_OPEN_GATES` until the required artifact and publication gates are evidenced.

## Structure and voice

The note addresses combinatorialists without assuming Lean knowledge. The principal source theorems are attributed and referenced. The main text does not reproduce their full absorption machinery. Source-to-declaration maps, implementation representations, dependency pins, run history and hashes are in the separate companion.

The exposition follows the mathematical habits of the author's Nash–Williams I–II papers and the cited Erdős-series samples: direct statements, concrete intermediate objects, proof paragraphs explaining why the next input applies, and explicit scope qualifications. The local Nash–Williams TeX template controls layout. No target journal or novelty assessment is invented.

The readability review followed the transitions, rather than searching for stock phrases alone:

- Reserve matching: a global leftover count does not control reserve load; integer level sets do; the local-lemma probabilities and dependency estimate explain the exponent choice; the ambient intersection explains the final matching union.
- Compatible decomposition: the forced-set count gives the deletion saving; both catalogue and covering steps preserve safety; the final absorption union therefore remains compatible.
- Compatible absorber: admissible-host subtraction, enlargement and a prescribed-packing application have separate roles.
- Completion: the filtered forbidden family explains why both wholly residual and non-residual forbidden blocks are excluded.
- Intersections: the fixed-first-system and choose-both-systems quantifiers are separated; finite support gives the sparsity needed for embedding at every large admissible order.
- Quantitative applications: all three colouring hypotheses are checked, the original exponent is used for the edge cap, and lower bounds are explained by incidence at a point.

No promotional novelty language, invented collaboration, detector-evasion language or generic future-work conclusion was introduced. Repetition of defined mathematical terms and theorem/proof structure is intentional.

## Revisions after the first complete authoring drafts

| Item | Class | Applied clarification | Semantic control |
| --- | --- | --- | --- |
| Fixed-index existence | CLARITY | Admissibility explicitly refers to the selected index | Same frozen existence type; no uniform threshold in the index asserted |
| Local tests | CLARITY | Added the level-set size and per-root incidence explanation | Inequalities already used in the frozen Core28/Theorem28 proof |
| Triangle divisibility | STRUCTURAL_FORM | Moved the definition before the application theorem | Definition unchanged; theorem statement unchanged |
| Matching reference | REFERENCE_FORMAT | Made the 2022 year explicit | Source identifier and meaning unchanged |
| Nash–Williams source | REFERENCE_FORMAT | Made the v1 statement baseline explicit | Same DOI and source used by the reused formal proof |
| Spanish draft status | GRAMMATICAL | Removed the pleonasm in the pending-publication sentence | No formal-status strengthening |

Before those baselines were saved, initial authoring had already made reserve-parameter ranges explicit, source-qualified references to article 6.3, explained the polynomial caps and removed English words from display formulas to support a natural Spanish translation. The protected baseline for that authoring was the already frozen mathematics.

## Bilingual method

The translation is editorial, not a claim that a string comparison establishes mathematical equivalence. Mechanical checks preserve exact display sequence, the exact inventory of mathematical expressions in each corresponding math-bearing block, ordered code identifiers and fenced commands, heading hierarchy and DOI sequence. Inline symbols may change order within a paragraph to preserve natural Spanish syntax. A separate manual review checks quantifiers, conditions, negation, source attribution and scope.

The initial code-span checker wrongly treated text after a fenced command block as inline code. It was corrected to distinguish fenced blocks from inline identifiers; both kinds are now checked. This was an audit-parser correction, not a change to the manuscripts' mathematical content.

Final TeX/PDF compilation and full-page rendered inspection now pass for all four current documents; hashes are in `AUDIT_RESULT.json` and `VISUAL_REVIEW.json`. The first visual pass identified an orphan section heading and a separated final theorem clause. Needspace and samepage layout controls corrected both without changing Markdown. All four PDFs were regenerated, rendered and inspected after that correction.

Open publication gate: actual Zenodo DOI reservation. Its insertion requires fresh downstream artifacts and checks. Palomar's official checks and consent to its concrete review remain separate later stages.
