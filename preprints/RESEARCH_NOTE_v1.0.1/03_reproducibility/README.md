# Reproduction

Run from the repository root. These scripts typeset and audit the documents; they do not run Lean.

```sh
python preprints/RESEARCH_NOTE_v1.0.1/03_reproducibility/build_preprints.py --pandoc /path/to/pandoc --tectonic /path/to/tectonic
python preprints/RESEARCH_NOTE_v1.0.1/03_reproducibility/render_preprints.py
python preprints/RESEARCH_NOTE_v1.0.1/03_reproducibility/audit_preprints.py
python tools/verify_formal_freeze.py
```

The recorded document build uses Pandoc 3.12.1 and Tectonic 0.17.0. Rendering uses Python, PyMuPDF and Pillow. The delivered TeX is generated from Markdown through the included series template. Each build record binds the source, template, TeX and PDF hashes. Rendering every page and checking the final images remains a human/agent inspection task, not a conclusion of the script.

The frozen formal build and current source correspondence are checked separately. The 360 recorded axiom queries and the original official preflight are historical evidence at their stated commits; no new Lean or external-kernel run is claimed for this editorial version.

The archive contains document sources, generated PDFs, release reports and hashes. Baseline paths and proof evidence are relative to the complete repository; use that checkout when running source-preservation checks. Local render images are reproducible and are not included in the public archive.
