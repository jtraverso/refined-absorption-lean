"""Record the completed Lake build without publishing compiled artifacts.

Run after the bounded clean build and sequential Palomar interface builds.
The final no-build rehash is a freshness check, not a second proof compilation.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import io
import json
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "publication/assembly"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
state = json.loads((EVIDENCE / "lake-state.json").read_text())
assert state["status"] == "PASS" and state["final_exit_code"] == 0
interfaces = json.loads((EVIDENCE / "palomar-interface-lake.json").read_text())
assert interfaces["status"] == "PASS" and interfaces["final_exit_code"] == 0
assert len(interfaces["modules"]) == 6
start = json.loads((EVIDENCE / "clean-build-start.json").read_text())
assert start["project_build_directory_initially_absent"]
sources = sorted([ROOT / "RefinedAbsorption.lean"] + [p for top in ("RefinedAbsorption", "checks", "Palomar") for p in (ROOT / top).rglob("*.lean")])
before = {p.relative_to(ROOT).as_posix(): sha(p) for p in sources}
configuration = {p: sha(ROOT / p) for p in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}
assert interfaces["configuration_sha256"] == configuration["lakefile.toml"]
git_inputs = before | configuration
snapshot = subprocess.check_output(["git", "archive", "--format=tar", "HEAD", "RefinedAbsorption.lean", "RefinedAbsorption", "checks", "Palomar", "lean-toolchain", "lakefile.toml", "lake-manifest.json"], cwd=ROOT)
with tarfile.open(fileobj=io.BytesIO(snapshot)) as archive:
    committed = {item.name: hashlib.sha256(archive.extractfile(item).read()).hexdigest()
                 for item in archive if item.isfile() and item.name in git_inputs}
assert committed == git_inputs, "Commit every current Lean source and configuration before freezing; Git and compiled inputs must agree."
command = ["lake", "--quiet", "--packages=.lake/local-packages.json", "--rehash", "--no-build", "build"]
log = EVIDENCE / "lake-freshness.log"
with log.open("w", encoding="utf-8", newline="\n") as out:
    out.write("COMMAND " + json.dumps(command) + "\n"); out.flush()
    code = subprocess.run(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT).returncode
assert code == 0, "Lake freshness check failed: " + str(log)
assert before == {p.relative_to(ROOT).as_posix(): sha(p) for p in sources}
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
overrides = {p["name"]: Path(p["dir"]) for p in json.loads((ROOT / ".lake/local-packages.json").read_text())["packages"]}
dependencies = []
for package in manifest["packages"]:
    assert package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"])
    assert re.fullmatch(r"https://github.com/[^/?#]+/[^/?#]+", package["url"])
    actual = subprocess.check_output(["git", "-C", str(overrides[package["name"]]), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(overrides[package["name"]]), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    assert actual == package["rev"] and not dirty, package["name"]
    dependencies.append({"name": package["name"], "repository": package["url"], "commit": actual})
records = []
queries = []
checkdir = EVIDENCE / "axioms"
checkdir.mkdir(exist_ok=True)
for source in sources:
    relative = source.relative_to(ROOT)
    module = relative.with_suffix("").as_posix().replace("/", ".")
    stem = ROOT / ".lake/build/lib/lean" / relative.with_suffix("")
    tracepath = stem.with_suffix(".trace")
    trace = json.loads(tracepath.read_text(encoding="utf-8"))
    assert trace.get("synthetic") is False, module
    artifacts = [stem.with_suffix(suffix) for suffix in (".olean", ".olean.private", ".olean.server", ".ilean", ".ir")]
    artifacts += [ROOT / ".lake/build/ir" / relative.with_suffix(".c")]
    assert all(p.is_file() for p in artifacts), module
    records.append({"module": module, "source": relative.as_posix(), "source_sha256": sha(source),
                    "trace_sha256": sha(tracepath), "artifacts": {p.relative_to(ROOT).as_posix(): sha(p) for p in artifacts}})
    if relative.parts[0] == "checks":
        expected = len(re.findall(r"^#print axioms ", source.read_text(encoding="utf-8"), re.M))
        messages = [entry["message"] for entry in trace["log"] if "depends on axioms:" in entry["message"] or "does not depend on any axioms" in entry["message"]]
        assert len(messages) == expected, (module, expected, len(messages))
        querylog = checkdir / (source.stem + ".log")
        querylog.write_text("\n".join(messages) + "\n", encoding="utf-8", newline="\n")
        for message in messages:
            match = re.search(r"depends on axioms:\s*\[(.*?)\]", message, re.S)
            axioms = [a.strip() for a in match[1].split(",") if a.strip()] if match else []
            assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, (module, message)
        queries.append({"module": module, "queries": expected, "log": querylog.relative_to(ROOT).as_posix(), "sha256": sha(querylog)})
for filename in ("source-preservation.json", "source-relocation-and-root.json", "definition-preservation.json"):
    assert (EVIDENCE / filename).is_file(), filename
preservation = json.loads((EVIDENCE / "source-preservation.json").read_text())
assert not any(preservation[k] for k in ("deleted_original_sources", "signature_text_differences", "active_flags"))
assert json.loads((EVIDENCE / "source-relocation-and-root.json").read_text())["status"] == "PASS"
assert json.loads((EVIDENCE / "definition-preservation.json").read_text())["status"] == "PASS"
githead = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
result = {"status": "PASS", "checked_utc": datetime.now(timezone.utc).isoformat(),
          "scope": "All current local Lean sources and the default Lake targets; clean project build directory, pinned dependency caches reused. This is not a Palomar verification certificate.",
          "source_commit": githead, "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
          "lean_version": subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip(),
          "dependencies": dependencies, "initial_scheduler_modules": state.get("initial_required", state["required"]),
          "continuation_scheduler_modules": state["required"], "continuation_run": state["run"], "current_modules": len(sources),
          "modules_added_during_assembly": sorted(set(r["module"] for r in records) - set(r["module"] for r in state["compiled"])),
          "freshness_command": command, "freshness_exit_code": code, "freshness_log_sha256": sha(log),
          "configuration_sha256": configuration,
          "palomar_interface_build_sha256": sha(EVIDENCE / "palomar-interface-lake.json"),
          "sources": records, "axiom_checks": queries, "axiom_query_count": sum(q["queries"] for q in queries),
          "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}
(EVIDENCE / "VALIDATION.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
print(json.dumps({k: result[k] for k in ("status", "source_commit", "current_modules", "axiom_query_count", "modules_added_during_assembly")}))
