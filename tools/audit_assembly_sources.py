"""Check exact preservation across the module relocation and the import root.

This is stronger than the historical declaration-header check for this assembly
step: every pre-existing byte must match after the documented import rewrite.
It does not replace the separate original-to-rc3 migration review.
"""
from pathlib import Path
import hashlib
import io
import json
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
BASE = "8164fe5e9debd978308768e42d718f9150d40434"
git = lambda *args: subprocess.check_output(["git", *args], cwd=ROOT)
with tarfile.open(fileobj=io.BytesIO(git("archive", "--format=tar", BASE, "RequestProject", "checks"))) as archive:
    originals = {item.name: archive.extractfile(item).read() for item in archive
                 if item.isfile() and item.name.endswith(".lean")}
records = []
for old, original in sorted(originals.items()):
    target = old.replace("RequestProject/", "RefinedAbsorption/", 1) if old.startswith("RequestProject/") else old
    before = original.decode("utf-8").replace("\r\n", "\n")
    expected = before.replace("RequestProject.", "RefinedAbsorption.")
    current = (ROOT / target).read_text(encoding="utf-8")
    records.append({"original_path": old, "current_path": target,
                    "matches_documented_rewrite": expected == current,
                    "sha256": hashlib.sha256((ROOT / target).read_bytes()).hexdigest()})
assert all(r["matches_documented_rewrite"] for r in records), [r for r in records if not r["matches_documented_rewrite"]]
sources = {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): p
           for p in (ROOT / "RefinedAbsorption").rglob("*.lean")}
sources["RefinedAbsorption"] = ROOT / "RefinedAbsorption.lean"
imports = {n: re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)", p.read_text(encoding="utf-8"), re.M)
           for n, p in sources.items()}
seen = set()
def visit(n):
    if n in seen or n not in sources:
        return
    seen.add(n)
    for child in imports[n]:
        visit(child)
visit("RefinedAbsorption")
uncovered = sorted(set(sources) - seen)
assert not uncovered, uncovered
upstream = json.loads((ROOT / "provenance/assembly-sources.json").read_text())
for record in upstream["imported_source_cut"]:
    path = ROOT / record["installed"]
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record["installed_sha256"]
    restored = re.sub(r"^.*import.*$", lambda m: m[0].replace(
        "RefinedAbsorption.Upstream.PippengerSpencer.", "PseudorandomLib.PippengerSpencer.").replace(
        "RequestProject.Pseudorandom.", "PseudorandomLib."), path.read_text(encoding="utf-8"), flags=re.M)
    original_hashes = {hashlib.sha256(text.encode()).hexdigest()
                       for text in (restored, restored.replace("\n", "\r\n"))}
    assert record["source_sha256"] in original_hashes, path
result = {"status": "PASS", "assembly_baseline_commit": BASE,
          "scope": "Exact text modulo newline normalization and RequestProject. -> RefinedAbsorption. throughout pre-existing sources; public-root local import coverage.",
          "preserved_sources": len(records), "records": records,
          "public_root": "RefinedAbsorption", "root_coverage": len(seen), "uncovered_local_modules": uncovered,
          "upstream_cut_sources_verified": len(upstream["imported_source_cut"]),
          "upstream_cut_verification": "Current installed hashes and original-source hashes after reversing import-only rewrites and the documented CRLF-to-LF normalization."}
output = ROOT / "publication/assembly/source-relocation-and-root.json"
output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
print(json.dumps({k: v for k, v in result.items() if k != "records"}))
