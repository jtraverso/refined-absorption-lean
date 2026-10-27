"""Compare non-proof declaration bodies with the original returned sources.

Formatting and comments are ignored. Any difference is reported for review;
this script cannot prove equivalence between different implementations.
"""
from pathlib import Path
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = Path(r"C:\nw\aristotle-refined-extension-return-review-20261026\source")
# Reuse the existing lexical comment stripper without executing its CLI.
tree = ast.parse((ROOT / "tools/audit_migration.py").read_text(encoding="utf-8"))
function = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "strip")
scope = {}
exec(compile(ast.Module(body=[function], type_ignores=[]), "comment-stripper", "exec"), scope)
strip = scope["strip"]
pattern = re.compile(r"^\s*(?:(?:public|private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([^\s:({]+)", re.M)

def declarations(text):
    text = strip(text)
    matches = list(pattern.finditer(text))
    return [(m.group(1), m.group(2), re.sub(r"\s+", " ", text[m.start():matches[i+1].start() if i+1 < len(matches) else len(text)]).strip())
            for i, m in enumerate(matches)]

baseline = json.loads((ROOT / "provenance/source-baseline.json").read_text(encoding="utf-8"))
changed = []
checked = 0
for old in baseline:
    new = old.replace("RequestProject/", "RefinedAbsorption/", 1) if old.startswith("RequestProject/") else old
    before = declarations((ORIGINAL / old).read_text(encoding="utf-8"))
    after = declarations((ROOT / new).read_text(encoding="utf-8"))
    assert [(k, n) for k, n, _ in before] == [(k, n) for k, n, _ in after], old
    for (kind, name, a), (_, _, b) in zip(before, after):
        if kind in {"theorem", "lemma", "instance"}:
            continue
        checked += 1
        if a != b:
            changed.append({"source": old, "current_source": new, "kind": kind, "name": name,
                            "before": a, "after": b})
result = {"status": "REVIEW_REQUIRED" if changed else "PASS", "checked_declarations": checked,
          "scope": "Comment/whitespace-normalized non-proof declaration spans, including structures. Instance proofs and theorem proofs are outside this comparison.",
          "changed_spans": changed}
(ROOT / "publication/assembly/definition-preservation.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"status": result["status"], "checked": checked, "changed": [{k: v for k, v in r.items() if k not in {"before", "after"}} for r in changed]}))
