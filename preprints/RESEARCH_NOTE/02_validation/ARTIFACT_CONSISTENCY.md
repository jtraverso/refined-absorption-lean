# Artifact consistency

Internal result: **PASS for the four final preprint 1.0 documents**, bound by [AUDIT_RESULT.json](AUDIT_RESULT.json) and [VISUAL_REVIEW.json](VISUAL_REVIEW.json).

The delivered Markdown is semantic authority; the adapted Nash–Williams series template is layout authority. Pandoc converts the body, then the template supplies the final TeX. Each PDF was generated from its delivered TeX in three passes with Tectonic 0.17.0. The actual compiler records identify the expected output and bind the source, template, TeX and PDF hashes. No separate PDF editing occurred.

Current pagination is note EN 10 / ES 11 and companion EN 7 / ES 7. All 35 pages and four contact sheets were inspected after the final correction. There are no figures. Title/author blocks, a theorem page, tables and references were compared visually with the actual Nash–Williams Paper II PDF (reference pages 1, 2, 3, 6 and 18). Fonts, margins and bibliography presentation follow its template; subsection spacing and keeping a theorem statement together are recorded adaptations.

The first pass found an orphan section heading and a theorem's final scope clause on the following page. The template/converter fixes were followed by regeneration, rendering and full inspection of all four documents. The compiler reports no retained layout diagnostics. Tables, hashes, accents, mathematical glyphs, references and page boundaries were checked.

Mechanical checks confirm current source/TeX/PDF/render correspondence, bilingual equation and identifier parity, manuscript local-link targets and all eighteen selected names in actual frozen axiom logs. These checks do not substitute for the separate semantic and visual judgments.

The actual DOI insertion invalidated the draft's downstream acceptance. All four PDFs were regenerated; an orphan opening line in the English note was then corrected with club/widow penalties, including the post-heading club penalty, and the complete pipeline was repeated. The final 35 pages and four contact sheets were inspected after that last correction. No mathematical body was changed.

Any future source or template edit invalidates this acceptance. The earlier DOI-pending review bundle remains historical and immutable under `publication/document-draft/`. The final document release has its own manifest and archive under `publication/document-release/`, distinct from the formal-source archive and from a Palomar certificate.
