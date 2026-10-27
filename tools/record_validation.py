"""Freeze a successful local migration run and its fresh endpoint checks."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import itertools
import json
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
state = json.loads((ROOT / "migration/build/state.json").read_text())
audit = json.loads((ROOT / "migration/source-audit.json").read_text())
verified = json.loads((ROOT / "migration/build/verified.json").read_text())
assert state["state"] == "PASS" and state["checked"] == state["required"]
assert not any(audit[key] for key in (
    "deleted_original_sources", "signature_text_differences", "active_flags"))
sources = sorted(path for top in ("RequestProject", "checks")
                 for path in (ROOT / top).rglob("*.lean"))
assert len(sources) == state["required"]
records = []
metadata_notes = []
for path in sources:
    rel = path.relative_to(ROOT)
    module = rel.with_suffix("").as_posix().replace("/", ".")
    imports = re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)",
                         path.read_text(encoding="utf-8"), re.M)
    fingerprint = hashlib.sha256(json.dumps(dict(source=sha(path), imports={
        name: verified[name] if name.startswith(("RequestProject.", "checks."))
        else "PINNED_" + state["mathlib_commit"] for name in imports
    }), sort_keys=True).encode()).hexdigest()
    events = [event for event in state["compiled"] if event["module"] == module]
    if events:
        assert len(events) == 1 and events[0]["exit_code"] == 0, module
        assert events[0]["source_sha256"] == sha(path), module
    if verified[module] != fingerprint:
        # A source edited during an early running job added a Mathlib import.
        # Its successful retry compiled the current bytes, but the old runner
        # retained that job's import list for its cache fingerprint. Preserve
        # this discrepancy explicitly; never rewrite the historical evidence.
        external = [name for name in imports if name.startswith("Mathlib.")]
        missing = None
        for count in range(1, len(external) + 1):
            for removed in itertools.combinations(external, count):
                legacy = dict(source=sha(path), imports={name:
                    verified[name] if name.startswith(("RequestProject.", "checks."))
                    else "PINNED_" + state["mathlib_commit"]
                    for name in imports if name not in removed})
                if hashlib.sha256(json.dumps(legacy, sort_keys=True).encode()).hexdigest() == verified[module]:
                    missing = list(removed)
                    break
            if missing:
                break
        assert events and missing, module
        metadata_notes.append(dict(module=module, external_imports_omitted_from_runner_fingerprint=missing,
            current_source_compiled=True, same_pinned_mathlib=True))
    artifact = ROOT / ".lake/build/lib/lean" / rel.with_suffix(".olean")
    records.append(dict(source=rel.as_posix(), source_sha256=sha(path),
                        runner_fingerprint=verified[module], audited_fingerprint=fingerprint,
                        olean_sha256=sha(artifact)))

outdir = ROOT / "migration/rc3-checks"
outdir.mkdir(exist_ok=True)
axioms = []
for path in sorted((ROOT / "checks").rglob("*.lean")):
    module = path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
    events = [event for event in state["compiled"] if event["module"] == module]
    assert len(events) == 1 and events[0]["exit_code"] == 0, module
    log = ROOT / events[0]["log"]
    text = log.read_text(encoding="utf-8")
    found = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", text)
    independent = re.findall(r"'([^'\n]+)' does not depend on any axioms", text)
    assert len(found) + len(independent) == len(re.findall(
        r"^\s*#print\s+axioms\s+", path.read_text(encoding="utf-8"), re.M)), module
    for name, names in found:
        used = [item.strip() for item in names.split(",") if item.strip()]
        assert set(used) <= {"propext", "Classical.choice", "Quot.sound"}, (name, used)
        axioms.append(dict(theorem=name, axioms=used, check=module))
    axioms.extend(dict(theorem=name, axioms=[], check=module) for name in independent)
    shutil.copyfile(log, outdir / (path.stem + ".log"))

result = dict(checked_utc=datetime.now(timezone.utc).isoformat(),
              verification="Full source compilation with pinned read-only dependencies; separate from a clean Lake build.",
              lean=state["lean_version"], mathlib=state["mathlib_commit"],
              sources_checked=len(records), original_sources=audit["original_lean_sources"],
              check_modules=8, source_audit="source-audit.json", sources=records, axiom_checks=axioms,
              runner_metadata_notes=metadata_notes)
(ROOT / "migration/VALIDATION.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(dict(sources=len(records), axiom_checks=len(axioms), status="PASS")))
