"""Render every delivered PDF page and bind the QA index to the PDF bytes."""
from pathlib import Path
import hashlib
import json
import math
import pymupdf
from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "preprints/RESEARCH_NOTE_v1.0.1"
QA = BASE / "02_validation"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pdfs = sorted(BASE.glob("*/*preprint_v1.0.1_*.pdf"))
assert len(pdfs) == 4
index = []
for pdf in pdfs:
    digest = sha(pdf)
    folder = QA / "_render" / (pdf.stem + "." + digest[:12])
    folder.mkdir(parents=True, exist_ok=True)
    pages = []
    texts = []
    with pymupdf.open(pdf) as document:
        for number, page in enumerate(document, 1):
            target = folder / f"page-{number:03}.png"
            page.get_pixmap(dpi=150, alpha=False).save(target)
            pages.append({"page": number, "image": target.relative_to(ROOT).as_posix(), "sha256": sha(target)})
            texts.append(page.get_text())
    textpath = folder / "extracted.txt"
    textpath.write_text("\n\f\n".join(texts), encoding="utf-8", newline="\n")
    sheet = Image.new("RGB", (960, math.ceil(len(pages) / 3) * 470), "#e6e6e6")
    draw = ImageDraw.Draw(sheet)
    for i, record in enumerate(pages):
        with Image.open(ROOT / record["image"]) as page:
            page.thumbnail((300, 435))
            x, y = (i % 3) * 320 + 10, (i // 3) * 470 + 25
            sheet.paste(page, (x, y))
            draw.text((x, y - 18), f"Page {record['page']}", fill="black")
    contact = folder / "contact-sheet.png"
    sheet.save(contact)
    index.append({"pdf": pdf.relative_to(ROOT).as_posix(), "pdf_sha256": digest, "dpi": 150,
                  "page_count": len(pages), "pages": pages,
                  "text": textpath.relative_to(ROOT).as_posix(), "text_sha256": sha(textpath),
                  "contact_sheet": contact.relative_to(ROOT).as_posix(), "contact_sha256": sha(contact),
                  "note": "Rendered images are local QA artifacts; the script reproduces them from the published PDF. Visual acceptance is recorded separately."})
    print(pdf.stem, len(pages), "pages", flush=True)
(QA / "RENDER_INDEX.json").write_text(json.dumps(index, indent=2) + "\n", encoding="utf-8", newline="\n")
