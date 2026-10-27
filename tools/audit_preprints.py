"""Check final document artifacts; semantic and visual review remain separate.

This script never runs Lean and never substitutes a presence check for a
mathematical review. It binds the mechanical document evidence to the files
that will actually be released.
"""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "preprints/RESEARCH_NOTE"
QA = BASE / "02_validation"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def math_spans(text):
    # Manuscripts use dollar delimiters and no dollar currency amounts.
    spans = re.findall(r"(?<!\\)\$\$(.*?)\$\$|(?<!\\)\$(?!\$)(.*?)(?<!\\)\$", text, re.S)
    return [re.sub(r"\s+", " ", a or b).strip() for a, b in spans]


def math_blocks(text):
    # Translation may reorder inline symbols within a paragraph. The exact
    # expression inventory remains bound to each corresponding math block.
    return [Counter(math_spans(block)) for block in re.split(r"\n\s*\n", text) if math_spans(block)]


def displays(text):
    return [re.sub(r"\s+", " ", span).strip()
            for span in re.findall(r"(?<!\\)\$\$(.*?)\$\$", text, re.S)]


def code_spans(text):
    pattern = r"^```([^\n]*)\n(.*?)^```[ \t]*$|(?<!`)`([^`\n]+)`(?!`)"
    return [("fence", lang, body.rstrip()) if body else ("inline", inline)
            for lang, body, inline in re.findall(pattern, text, re.M | re.S)]


def main():
    formal = json.loads((ROOT / "publication/assembly/VALIDATION.json").read_text())
    assert formal["status"] == "PASS"
    assert formal["axiom_query_count"] == 360
    queried = {name for check in formal["axiom_checks"]
               for name in re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",
                                      (ROOT / check["log"]).read_text(encoding="utf-8"))}
    selected = {name for config in (ROOT / "Palomar").glob("*.comparator.json")
                for name in json.loads(config.read_text())["theorem_names"]}
    assert len(selected) == 18 and selected <= queried
    for item in formal["sources"]:
        assert sha(ROOT / item["source"]) == item["source_sha256"], item["source"]
    builds = json.loads((QA / "typeset/artifact_build.json").read_text())
    renders = json.loads((QA / "RENDER_INDEX.json").read_text())
    assert len(builds) == len(renders) == 4
    documents = []
    failures = []
    for build in builds:
        source = ROOT / build["source"]
        tex, pdf = source.with_suffix(".tex"), source.with_suffix(".pdf")
        text = source.read_text(encoding="utf-8")
        assert sha(source) == build["markdown_sha256"], source
        assert sha(tex) == build["tex_sha256"], tex
        assert sha(pdf) == build["pdf_sha256"], pdf
        assert sha(ROOT / "scripts/series_template.tex") == build["template_sha256"]
        assert build["passes"] >= 2 and not build["lean_build_executed"]
        failures.extend({"file": build["source"], "issue": issue} for issue in build["layout_issues"])
        render = next(r for r in renders if r["pdf"] == pdf.relative_to(ROOT).as_posix())
        assert render["pdf_sha256"] == sha(pdf)
        assert render["page_count"] == len(render["pages"])
        for token in ("\x08", "\x00", "\t"):
            assert token not in text, (source, repr(token))
        for target in re.findall(r"\]\(([^)]+)\)", text):
            if re.match(r"(?:https?://|mailto:|#)", target):
                continue
            path = target.strip("<>").split("#")[0]
            assert (source.parent / path).is_file(), (source, target)
        documents.append({"source": build["source"], "markdown_sha256": sha(source),
                          "tex_sha256": sha(tex), "pdf_sha256": sha(pdf),
                          "pages": render["page_count"], "math_spans": len(math_spans(text))})
    pairs = []
    for english in sorted(BASE.glob("*/*preprint_v1.0_en.md")):
        spanish = english.with_name(english.name.replace("_en.md", "_es.md"))
        en, es = [p.read_text(encoding="utf-8") for p in (english, spanish)]
        assert math_blocks(en) == math_blocks(es), (english, "math expressions per corresponding block")
        assert displays(en) == displays(es), (english, "display sequence")
        # Headings are translated; their hierarchy and number remain identical.
        assert re.findall(r"^(#+) ", en, re.M) == re.findall(r"^(#+) ", es, re.M)
        assert code_spans(en) == code_spans(es), (english, "identifier and code-block parity")
        assert re.findall(r"https://doi.org/[^\s>)]+", en) == re.findall(r"https://doi.org/[^\s>)]+", es)
        pairs.append({"english": english.relative_to(ROOT).as_posix(),
                      "spanish": spanish.relative_to(ROOT).as_posix(),
                      "math_expressions_per_block_identical": True, "display_sequence_identical": True,
                      "inline_reordering": "Allowed only within corresponding blocks; mathematical meaning is reviewed separately.",
                      "code_identifiers_identical": True,
                      "heading_hierarchy_identical": True, "doi_sequence_identical": True})
    result = {"status": "PASS_LOCAL_DOCUMENT_CHECKS" if not failures else "FAIL",
              "checked_utc": datetime.now(timezone.utc).isoformat(),
              "scope": "Artifact freshness, typesetting diagnostics, local file links, bilingual equation/identifier/heading/DOI parity. Mathematical and visual judgments are recorded in separate internal reviews.",
              "formal_source_commit": formal["source_commit"],
              "auditor_script_sha256": sha(Path(__file__)), "selected_names_with_axiom_queries": len(selected),
              "documents": documents, "bilingual_pairs": pairs, "failures": failures}
    (QA / "AUDIT_RESULT.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"], "documents": len(documents),
                      "pages": sum(d["pages"] for d in documents), "failures": failures}))
    assert not failures


if __name__ == "__main__":
    main()
