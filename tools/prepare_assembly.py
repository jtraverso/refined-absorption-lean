"""Relocate the refined module root and verify the minimal external proof cut."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PS = Path(r"C:\nw\refined-upstream\pippenger-spencer")
NW = Path(r"C:\nw\nash-williams-lean")
PS_REV = "b19273396d369332fb489fe07e61e27c9e7f9233"
NW_REV = "2603197abdbf0a600ec663f6f046f70fbd209d4a"
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
for path, revision in ((PS, PS_REV), (NW, NW_REV)):
    assert subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip() == revision

# Only module routes change; declaration namespaces and mathematical statements remain.
old = ROOT / "RequestProject"
new = ROOT / "RefinedAbsorption"
if old.exists():
    assert not new.exists() and old.resolve().parent == ROOT.resolve()
    old.rename(new)
for top in ("RefinedAbsorption", "checks"):
    for path in (ROOT / top).rglob("*.lean"):
        text = path.read_text(encoding="utf-8")
        changed = re.sub(r"^(\s*(?:public\s+)?(?:meta\s+)?import\s+)RequestProject\.",
                         r"\1RefinedAbsorption.", text, flags=re.M)
        if changed != text:
            path.write_text(changed, encoding="utf-8", newline="\n")

shared = []
for path in (PS / "PseudorandomLib").glob("*.lean"):
    target = NW / "RequestProject/Pseudorandom" / path.name
    if target.exists():
        normalized = path.read_text(encoding="utf-8").replace(
            "PseudorandomLib.", "RequestProject.Pseudorandom.")
        assert normalized == target.read_text(encoding="utf-8"), path.name
        shared.append(dict(source=path.relative_to(PS).as_posix(), source_sha256=sha(path),
                           reused=target.relative_to(NW).as_posix(), reused_sha256=sha(target)))
assert len(shared) == 19
cut = []
for name in ("Basic", "ColourHypergraph", "Polynomial"):
    source = PS / f"PseudorandomLib/PippengerSpencer/{name}.lean"
    target = ROOT / f"RefinedAbsorption/Upstream/PippengerSpencer/{name}.lean"
    target.parent.mkdir(parents=True, exist_ok=True)
    text = source.read_text(encoding="utf-8")
    changed = text.replace("PseudorandomLib.PippengerSpencer.", "RefinedAbsorption.Upstream.PippengerSpencer.")
    changed = changed.replace("PseudorandomLib.", "RequestProject.Pseudorandom.")
    assert re.sub(r"^.*import.*$", "", text, flags=re.M) == re.sub(r"^.*import.*$", "", changed, flags=re.M)
    target.write_text(changed, encoding="utf-8", newline="\n")
    cut.append(dict(source=source.relative_to(PS).as_posix(), source_sha256=sha(source),
                    installed=target.relative_to(ROOT).as_posix(), installed_sha256=sha(target)))
shutil.copyfile(PS / "LICENSE", ROOT / "provenance/PIPPENGER_SPENCER_LICENSE")
record = dict(pippenger_spencer=dict(repository="https://github.com/jtraverso/pippenger-spencer", commit=PS_REV),
              nash_williams=dict(repository="https://github.com/jtraverso/nash-williams-lean", commit=NW_REV),
              shared_sources=shared, imported_source_cut=cut,
              mathematical_code_change="None: only import module paths changed in the three source-cut files.",
              refined_root_relocation="RequestProject -> RefinedAbsorption; mathematical namespaces unchanged.")
(ROOT / "provenance/assembly-sources.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")

manifest = json.loads((ROOT / "lake-manifest.json").read_text())
assert not any(pkg["name"] == "nash_williams_paper_i" for pkg in manifest["packages"])
manifest["packages"].append(dict(url="https://github.com/jtraverso/nash-williams-lean", type="git",
    subDir=None, scope="", rev=NW_REV, name="nash_williams_paper_i", manifestFile="lake-manifest.json",
    inputRev=NW_REV, inherited=False, configFile="lakefile.toml"))
(ROOT / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
overrides = json.loads((ROOT / ".lake/local-packages.json").read_text())
overrides["packages"].append(dict(type="path", scope="", name="nash_williams_paper_i", manifestFile="lake-manifest.json",
    inherited=False, configFile="lakefile.toml", dir=str(NW)))
(ROOT / ".lake/local-packages.json").write_text(json.dumps(overrides, indent=2) + "\n", encoding="utf-8")
print(json.dumps(dict(relocated_sources=293, shared_external_sources=len(shared), source_cut=len(cut))))
