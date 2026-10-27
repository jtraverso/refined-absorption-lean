# Internal mathematical alignment review

Reviewer: Codex under the author's direction. This is self-assessment, not independent human peer review.

Text-review result: PASS within the scope below. PDF, publication metadata and external registry gates have separate evidence and statuses.

The mathematical authority is source commit `5428ee9b772e67dd7ec6da443199b36a003b72d4`, the completed 316-source Lake record and 360 axiom-query outputs. `publication/PROTECTED_ELEMENT_INDEX.json` was created before manuscript drafting. Every one of the eighteen selected comparison names is present in the actual frozen query messages; unqualified source commands were resolved using those printed names rather than guessed from textual command spelling.

| Passage | Source and reviewed obligation | Finding |
| --- | --- | --- |
| Note 1, fixed-index existence | `Multigraph/Existence.lean`, `existenceConjecture_proved` | All fixed indices at least one for the stated range; finite sets of blocks, no repetitions. Admissibility is for the chosen index, and the threshold may depend on it. |
| Note 3.1, reserve matching | `Pending/Core28.lean`, `Pending/Theorem28.lean` | Labelled parallel copies retained; near-regularity only on the designated roots. Local test sizes and incidences control level sets without a global edge/test count cap. The load estimate and local-lemma exponents match the frozen argument. |
| Note 3.2, dangerous cliques | `Pending/Danger.lean`, `Pending/Theorem63.lean` | The count is `2^r q n^(q-r-1)`. The forced-set count treats impossible sizes separately. Both the absorber catalogue and nibble/reserve packing must be safe. The larger printed source bound is described as insufficient for the deletion saving, not refuted merely by a stronger bound. |
| Note 3.3 and 4.1 | `Pending/Theorem62.lean`, `Faithful2024/Theorem62Ambient.lean` | Subtraction of admissible complete hosts proves divisibility; enlargement supplies density; 6.3 gives compatibility. The entire old ambient set is independent, while mixed edges are allowed. The old support-based theorem remains. |
| Note 4.2 | `FaithfulSurvey2025/Embedding.lean` | The perfect-matching witness satisfies local counts, sparsity and boundedness at the stated parameters. It covers all old vertices, resolving the domain-convention qualification. The cited Appendix B proof exists. The negative global theorem and positive piecewise variant are different claims. |
| Theorem 5.1 | `Extensions/Intersection.lean`, `steiner_completion_avoiding` | The forbidden partial system is arbitrary. Residual divisibility and density precede application of article 6.3. Filtering wholly residual forbidden blocks explains exact avoidance; the crossing guarantee has its required restriction. |
| Corollary 5.2 | Same file, prescribed/exact-intersection and finite embedding endpoints | The first system is fixed in part (i); sparsity is on covered r-edges. Part (ii) holds at every sufficiently large admissible order and chooses an injection together with the systems. |
| Proposition 5.3 | Same file, packing and polynomial-spectrum deduction | The greedy sufficient condition and constant match the source proof. Both systems are chosen. No complete spectrum or universal prescription against an arbitrary first system is claimed. |
| Theorem 6.2 | `Extensions/PolynomialResolution.lean`, closed `Assembly.lean` endpoints | Natural division is exact by regularity counting. The input checks uniformity, maximum degree, polynomial codegrees and the edge-count cap at the original exponent before weakening the output exponent. The error counts classes, not per-class deficit. |
| Theorem 6.3 | `Extensions/NashWilliamsSchedule.lean`, closed `Assembly.lean` endpoint | Actual Nash–Williams decomposition at the exact threshold, triangle degrees and codegrees, polynomial edge count, then colouring. Graph near-regularity is not added. Rounds need not be spanning factors; unused labels are allowed. |

The new local-test explanation only exposes inequalities already used by the frozen reserve proof. The incidence explanations in the quantitative section expose existing counting arguments. No new mathematical theorem was inserted to improve the prose. The named theorem/corollary/proposition statements remain unchanged from the complete authoring baselines.

Scope exclusions are explicit: general high-girth assertions, a full intersection spectrum, classical Steiner orthogonality, perfect resolutions, per-round deficit bounds, an optimized exponent and historical priority for every consequence. The original source theorems remain attributed to their authors.

Unresolved mathematical content queries: none. This verdict does not certify Palomar comparison or independent kernel replay.
