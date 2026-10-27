# Reproducibility

The formal source freeze is commit `5428ee9b772e67dd7ec6da443199b36a003b72d4`, also identified by tag `formal-v1.0`. The immutable [archive and receipt](../../../publication/formal-freeze/) include the source snapshot and completed Lake campaign evidence.

## Check the recorded freeze

From the complete publication checkout:

```sh
python tools/verify_formal_freeze.py
```

This static checker verifies current/archived source correspondence, original-source archive integrity and recorded axiom outputs. It does not execute Lean or independently replay proofs. The source-only tag cannot contain its own later external receipt; use the complete publication checkout for this convenience check.

## Reconstruct the proofs

Use a separate checkout of the formal source commit, or extract the formal archive. Install the pinned `leanprover/lean4:v4.35.0-rc3` toolchain, then run:

```sh
lake exe cache get
lake build
```

The committed manifest uses immutable Git revisions and no private local path is needed. The default targets are `RefinedAbsorption`, `checks` and `Palomar`. The root imports all 300 local library modules. Ten check modules and six standalone comparison modules are additional targets. Challenges deliberately have statement placeholders; Solutions import the actual proved declarations.

The recorded campaign began with no project build output directory and reused pinned dependency caches. It compiled all 316 local sources and obtained 360 actual endpoint axiom messages, allowing only the stated foundational axioms. It was resumed with source/hash/trace checks; it was not a cold rebuild of Mathlib. Failures and corrections are retained in [BUILD_HISTORY.md](../../../publication/assembly/BUILD_HISTORY.md). Another platform need not reproduce the compiled binary hashes.

## Rebuild the documents

The four Markdown sources are semantic authority and `scripts/series_template.tex` is layout authority. The recorded versions are Pandoc 3.12.1, Tectonic 0.17.0, Python with PyMuPDF 1.28.2 and Pillow 12.2. The build helper accepts executable paths:

```sh
python tools/build_preprints.py --pandoc /path/to/pandoc --tectonic /path/to/tectonic
python tools/render_preprints.py
python tools/audit_preprints.py
```

Run these in a working copy: they regenerate TeX/PDF, compiler records, render index and mechanical report. All rendered pages must then be inspected again. The original visual acceptance applies only to its recorded PDF hashes. Documentary changes do not require modifying the frozen Lean sources. Compiler font/package caches may need ordinary network or filesystem access.

The four current PDFs are bound to their delivered TeX by actual three-pass records under `02_validation/typeset/`. Rendered PNGs are ignored local QA artifacts reproducible from the PDFs; their hashes and page count are in `RENDER_INDEX.json`.

Official Palomar preflight, Comparator comparison, independent kernel check and registry review remain separate pending stages. These local instructions do not produce a Palomar certificate.
