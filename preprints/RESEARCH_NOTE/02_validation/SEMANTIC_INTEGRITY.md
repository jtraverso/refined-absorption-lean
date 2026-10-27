# Semantic integrity report

Input hashes: four first-complete authoring drafts in [baseline/INDEX.json](baseline/INDEX.json). Mathematical authority: formal source commit `5428ee9b772e67dd7ec6da443199b36a003b72d4` and [protected-element index](../../../publication/PROTECTED_ELEMENT_INDEX.json), created before drafting.

Output hashes: the four Markdown, TeX and PDF triples in [AUDIT_RESULT.json](AUDIT_RESULT.json).

Protected elements changed: none. The ten named note statement blocks (five per language, seven selected endpoints) remain unchanged from the authoring baselines. All eighteen selected exact Lean headers and nine proof-source files remain bound to the frozen source.

Quantifier changes: none to a protected statement. The prose now explicitly associates admissibility with the fixed index and distinguishes universal colouring of existing systems from admissible-order existence. Assumption changes: none. Constant changes: none. Proof-dependency changes: none; the local test explanation was expanded using estimates already present in the reserve proof. Citation-scope changes: matching year and Nash–Williams v1 baseline made explicit, with no changed attribution. Novelty-scope changes: none.

The Markdown equations were not changed for pagination. Needspace and samepage controls changed only the layout. TeX and PDFs were regenerated from the delivered sources after the final layout correction. All current rendered pages were inspected after that regeneration.

Bilingual checks preserve 320 mathematical expressions in each note and 19 in each companion, with exact display sequence and per-corresponding-block expression inventories, code identifiers, heading hierarchy and DOI sequence. Inline order may follow natural Spanish syntax within a corresponding paragraph. Manual review additionally checks quantifiers, assumptions, negation, representation and scope; a string comparison alone is not presented as semantic equivalence.

Final PDF compiled from delivered TeX: yes, actual three-pass compiler records. Rendered QA postdates final PDF: yes. Hashes/manifests must follow this review and are recorded in the integrity directory. Unresolved mathematical/editorial content queries: none.

The actual reserved DOI `10.5281/zenodo.23685654` replaces the draft header in all four sources. `publication/zenodo/DOI_INSERTION.json` binds the before/after source hashes and verifies that every body after the abstract heading is unchanged. Club/widow pagination controls are layout-only changes. Final TeX/PDF regeneration, all-page visual inspection and bilingual checks followed those edits.

Internal semantic audit: **PASS**. Editorial verdict: `EDITORIALLY_READY`. Public publication and Palomar registration are evidenced separately.
