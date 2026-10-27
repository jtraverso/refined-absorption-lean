"""Record the immutable return and prepare read-only use of the existing rc3 cache."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path(r"C:\nw\aristotle-refined-extension-return-review-20261026\source")
CACHE_ROOT = Path(r"C:\nw\nash-williams-lean")
PIN = "c55e6e786f49471c72fbddbec5415808896aec1e"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
baseline = {p.relative_to(SOURCE).as_posix(): sha(p) for p in SOURCE.rglob("*.lean")}
baseline_path = ROOT / "provenance/source-baseline.json"
if baseline_path.exists():
    assert json.loads(baseline_path.read_text(encoding="utf-8")) == baseline
else:
    baseline_path.write_text(json.dumps(baseline,indent=2)+"\n",encoding="utf-8")
for rel in baseline:
    p = ROOT / rel
    text = p.read_text(encoding="utf-8")
    if not re.search(r"^module\s*$",text,re.M):
        assert rel.startswith("checks/"), rel
        text = "module\n\n" + re.sub(r"^import ","public import ",text,flags=re.M)
        p.write_text(text,encoding="utf-8",newline="\n")
manifest = json.loads((CACHE_ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
assert next(p for p in manifest["packages"] if p["name"]=="mathlib")["rev"]==PIN
manifest["name"] = "refined_absorption"
(ROOT / "lake-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
deps=[]
for pkg in manifest["packages"]:
    path = CACHE_ROOT / ".lake/packages" / pkg["name"]
    actual = subprocess.check_output(["git","-C",str(path),"rev-parse","HEAD"],text=True).strip()
    assert actual == pkg["rev"], (pkg["name"],actual,pkg["rev"])
    # Cli is a Lake executable dependency and need not have a Lean library cache.
    assert (path / ".lake/build/lib/lean").is_dir() or pkg["name"] == "Cli", path
    deps.append(dict(name=pkg["name"],path=str(path),revision=actual))
env = dict(lean=str(Path.home()/".elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean.exe"),
           dependencies=deps, mathlib_commit=PIN,
           scope="Existing pinned dependencies are read-only. All new artifacts and logs stay in this project.")
(ROOT / "migration/local-environment.json").write_text(json.dumps(env,indent=2)+"\n",encoding="utf-8")
print(json.dumps(dict(imported_lean_sources=len(baseline),dependencies=len(deps),mathlib=PIN)))
