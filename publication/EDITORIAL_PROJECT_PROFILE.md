# Editorial project profile

Project: Refined absorption formalization and research note.
Paper title: Formalizing refined absorption: proof interfaces and consequences.
Manuscript version: 1.0 editorial draft, authored after the completed clean formal freeze; English and Spanish note and companion exist.
Target journal: No journal selected; public research note with a Zenodo DOI.
Audience: Combinatorialists familiar with designs and absorption; Lean experience is not assumed.
Editorial owner: Juan Pablo Traverso Gianini.
Mathematical content owner: The cited authors for their results; Traverso for the formalization and the accompanying exposition and derived consequences. Historical priority for those consequences is not claimed.
Audit owner: Codex acting for the author. This is an internal agent audit, not independent human peer review.
Literature dossier: publication/BIBLIOGRAPHIC_DOSSIER.md and source-version correspondence in the formal companion.
Author voice samples: Nash–Williams papers I–II and their formal companions; Erdős 81 papers V–VI and research notes I–II.
Semantic source authority: English Markdown note and companion, grounded in the recorded Lean freeze; Spanish Markdown is the synchronized translation.
Layout source authority: The author's Nash–Williams series_template.tex, adapted only as needed for this note.
Output languages: English and Spanish; separate note and formal companion in each language.
First-person policy: Restrained authorial voice; no invented collaboration or independent review.
Notation policy: Fixed q > r, degrees distinguished by their uniformity, block families distinguished from covered r-edges. Source theorem numbers always identify the source text.
Citation style: Numbered bibliography, DOI links, version-specific theorem locations.
Abstract limit: Approximately 180 words in English; mathematically identical Spanish abstract.
Length constraints: Initial target 12–16 pages; the complete note occupies 10 English / 11 Spanish pages without padding. The companions each occupy seven pages. Clarity takes priority over an arbitrary page target.
Protected elements: Existing Lean definitions, statements and proofs; exact external contracts; quantifier ranges; divisibility conditions; thresholds; the distinction between partial parallel classes and a resolution; the distinction between global and piecewise embeddings.
Permitted structural changes: Group corollaries around the completion-avoiding theorem; move module names, full endpoint maps, execution records and hashes into the companion.
Formal aggregate root: RefinedAbsorption.lean, covering all 300 library modules after adding the ambient-vertex interface for 6.2.
Formal canonical/public entry points: Original article endpoints in Faithful2024, Original2024 and Pending, including the additive theorem_6_2_ambient; survey endpoints in Final, Multigraph.Existence and FaithfulSurvey2025; intersection consequences in Extensions.Intersection; three closed quantitative endpoints in Assembly.
Recorded build target list: All local library and check modules, followed by the default Lake build; standalone Palomar interfaces checked separately. Exact counts and logs belong to the final validation record.
Lean audit mode: Rerun with a clean project build directory and pinned cached dependencies; fresh endpoint axiom checks. Palomar preflight is a further independent mechanical gate.
Artifact package boundary: preprints/RESEARCH_NOTE/{01_manuscript,02_validation,03_reproducibility,04_integrity,05_formalization}, plus the actual Lean library, provenance, publication receipts and scripts in the repository.
Required release reports: Semantic change report; source-to-formal alignment; scope and limitation ledger; bibliography/version audit; human readability review; bilingual parity review; build and axiom record; complete PDF render index and visual review; final artifact hashes and release audit.

## Scope decisions

The note explains proof interfaces and a small number of consequences. It does not reproduce the source papers' full development. The case studies are the original article's Theorems 2.8 and 6.3 and the deduction of 6.2. Prescribed intersections are organized around one completion theorem. The quantitative section explains the application of proved polynomial edge-colouring and Nash–Williams endpoints, retaining every hypothesis needed to apply them.

The library includes many more results than the note discusses. Neither the note nor the Palomar descriptions may say that every result in both source texts is formalized. The last returned round includes `RefinedAbsorption.existenceConjecture_proved : ExistenceConjecture` for every index λ ≥ 1, with no repeated blocks; it is included in the migration's axiom checks and the current full build. General high-girth statements remain outside the established scope. The printed global embedding statement is distinguished from the proved piecewise variant and its formal counterexample.

No new mathematical result may be inserted merely to improve the exposition. Any proposed extension beyond the current library must be returned to a separate mathematical proof phase. No release status is PASS until its actual technical, semantic and visual evidence exists.
