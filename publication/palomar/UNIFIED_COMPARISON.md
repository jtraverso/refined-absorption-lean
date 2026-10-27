# One Palomar entry for the assembled development

At the author's request, the canonical submission is a **single entry** selecting all eighteen principal declarations. The three source groups retain separate attribution: Delcourt–Postle's article (six), Postle's survey and its fidelity qualifications (five), and the research note (seven).

| Item | Canonical value |
| --- | --- |
| Comparator configuration | `Palomar/Unified.comparator.json` |
| Challenge | `Palomar.UnifiedChallenge` |
| Solution | `RefinedAbsorption`, the existing aggregate proof root |
| Formalization metadata | `Palomar/Unified/formalization.yaml` |
| Article DOI | `10.48550/arXiv.2402.17855`; statement baseline v1 |
| Survey DOI | `10.1137/25M1805977`; statement baseline arXiv:2510.19978v1 |
| Research-note DOI | `10.5281/zenodo.23685654` |

This changes the comparison packaging, not the mathematical claims. The aggregate Solution already publicly imports all 300 local proof-library modules. No new Solution wrapper or theorem proof is introduced. The new standalone Challenge imports only Mathlib and copies the existing statement vocabulary once, removing only byte-identical shared prefixes from the three generated views. It is 731 lines / 44,465 bytes, below Palomar's Challenge caps. All eighteen selected names are retained, with the same original source extraction spans.

The three narrower configurations and their six interface files remain unchanged as optional historical views. Their earlier separate preflight dispatches were cancelled when the author requested one entry; they are not the intended registry submissions.

## Frozen proof development and additive interface

The immutable formal-source archive still records the actual 316-source clean Lake campaign, 360 axiom queries and the same formal source commit `5428ee9b772e67dd7ec6da443199b36a003b72d4`. Those bytes and their receipt have not been rewritten. The manuscripts and formal companion describe that freeze and those original views; this file records the later canonical comparison collation.

The current project adds one Challenge, giving 317 local Lean sources. Its eighteen deliberate statement placeholders are not proof-library holes. The existing aggregate root is the Solution, so the comparison is against the same frozen proofs. The additive local build record is `publication/palomar/unified-build/RESULT.json`; its status and exact command exits must be read as evidence, not inferred from this document. The original freeze remains independently checkable with `tools/verify_formal_freeze.py`.

The supplemental interface freeze binds the new Challenge, configuration, metadata and actual local build evidence to their public source commit. It supplements the original formal archive. It does not replace the required complete official preflight, Comparator and independent kernel checks for the combined configuration.

The mathematical research note and its four published-release PDF assets are unchanged by this collation. No theorem, hypothesis, definition, proof, source attribution or mathematical body is weakened to obtain a combined comparison.
