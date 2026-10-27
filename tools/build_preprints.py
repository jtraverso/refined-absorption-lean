"""Typeset the four note documents from semantic Markdown; never builds Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "preprints/RESEARCH_NOTE"
QA = BASE / "02_validation/typeset"
TEMPLATE = ROOT / "scripts/series_template.tex"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def code_breaks(match):
    text = match[1]
    if re.fullmatch(r"[0-9a-f]{40,64}", text):
        text = r"\allowbreak{}".join(text[i:i+8] for i in range(0, len(text), 8))
    else:
        text = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", text)
        text = text.replace(".", r".\allowbreak{}").replace(r"\_", r"\_\allowbreak{}")
        text = text.replace("/", r"/\allowbreak{}")
    return r"\texttt{" + text + "}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pandoc", required=True)
    parser.add_argument("--tectonic", required=True)
    parser.add_argument("--only")
    args = parser.parse_args()
    QA.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    if os.name == "nt":
        fontconfig = QA / "fonts.conf"
        fontconfig.write_text('<?xml version="1.0"?><!DOCTYPE fontconfig SYSTEM "fonts.dtd"><fontconfig><dir>C:/Windows/Fonts</dir><cachedir prefix="xdg">fontconfig</cachedir></fontconfig>', encoding="utf-8", newline="\n")
        env["FONTCONFIG_FILE"] = str(fontconfig)
    record_path = QA / "artifact_build.json"
    records = json.loads(record_path.read_text()) if record_path.exists() else []
    sources = sorted(BASE.glob("*/*preprint_v1.0_*.md"))
    assert len(sources) == 4, "Expected note and companion, each in English and Spanish."
    engine = subprocess.check_output([args.tectonic, "--version"], text=True).strip()
    converter = subprocess.check_output([args.pandoc, "--version"], text=True).splitlines()[0]
    for source in sources:
        if args.only and args.only not in source.name:
            continue
        digest = sha(source)
        md = source.read_text(encoding="utf-8")
        title = re.search(r"^title: '(.*)'$", md, re.M)[1]
        lang = source.stem[-2:]
        assert lang in {"en", "es"}
        body = re.sub(r"^---\n.*?\n---\n", "", md, count=1, flags=re.S)
        converted = subprocess.run([args.pandoc, "--from=markdown+tex_math_dollars", "--to=latex", "--wrap=none", "--syntax-highlighting=none"], input=body, capture_output=True, text=True, encoding="utf-8", check=True)
        texbody = re.sub(r"\\def\\LTcaptype\{none\}[^\n]*\n", "", converted.stdout)
        texbody = re.sub(r"\\texttt\{([^{}]*)\}", code_breaks, texbody)
        texbody = re.sub(r"(\\subsubsection\{)", r"\n\\Needspace{7\\baselineskip}\n\1", texbody)
        bibliography = re.search(r"\\subsection\{(?:References|Referencias)\}[^\n]*\n", texbody)
        if bibliography:
            texbody = texbody[:bibliography.end()] + "\n\\begingroup\\small\\raggedright\n\\setlength{\\parskip}{3pt}\n" + texbody[bibliography.end():] + "\n\\endgroup\n"
        tex = TEMPLATE.read_text(encoding="utf-8")
        replacements = {
            "LANG": "english" if lang == "en" else "spanish",
            "BABEL": "english" if lang == "en" else "spanish,es-noshorthands,es-tabla",
            "TITLE": title, "PDFLANG": "en-US" if lang == "en" else "es-ES",
            "AFFILIATION": "Independent researcher, Santiago, Chile" if lang == "en" else "Investigador independiente, Santiago, Chile",
            "BODY": texbody,
        }
        for key, value in replacements.items():
            tex = tex.replace("@@" + key + "@@", value)
        assert "@@" not in tex
        texpath = source.with_suffix(".tex")
        texpath.write_bytes(tex.encode("utf-8"))
        for iteration in range(1, 4):
            command = [args.tectonic, "--keep-logs", "--keep-intermediates", "--outdir", str(source.parent), str(texpath)]
            result = subprocess.run(command, cwd=source.parent, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
            output = result.stdout + result.stderr
            sanitized = output.replace(str(ROOT), "<REPO>").replace(ROOT.as_posix(), "<REPO>")
            (QA / (source.stem + f"_pass{iteration}.txt")).write_bytes(sanitized.encode("utf-8"))
            print(source.stem, "pass", iteration, "exit", result.returncode, flush=True)
            assert result.returncode == 0, output[-6000:]
        pdf = source.with_suffix(".pdf")
        log = source.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
        (QA / (source.stem + "_texlog.txt")).write_bytes(log.replace(str(ROOT), "<REPO>").replace(ROOT.as_posix(), "<REPO>").encode("utf-8"))
        assert pdf.is_file() and pdf.stat().st_mtime >= texpath.stat().st_mtime
        assert re.search(r"Writing[^\n]*" + re.escape(pdf.name), output)
        assert sha(source) == digest, "Markdown changed while typesetting."
        issues = [line for line in log.splitlines() if any(flag in line for flag in ("Overfull", "Missing character:", "undefined references", "LaTeX Error"))]
        item = {"source": source.relative_to(ROOT).as_posix(), "markdown_sha256": digest,
                "tex_sha256": sha(texpath), "pdf_sha256": sha(pdf), "template_sha256": sha(TEMPLATE),
                "engine": engine, "converter": converter, "passes": 3, "layout_issues": issues,
                "lean_build_executed": False}
        records = [r for r in records if r["source"] != item["source"]] + [item]
        record_path.write_bytes((json.dumps(records, indent=2) + "\n").encode("utf-8"))
        print(json.dumps(item), flush=True)
        for suffix in (".log", ".aux", ".out", ".toc"):
            source.with_suffix(suffix).unlink(missing_ok=True)


if __name__ == "__main__":
    main()
