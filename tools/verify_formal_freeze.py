"""Verify the recorded formal freeze without running Lean.

This checks integrity and source correspondence, not independent proof replay.
Use a fresh Lake build or Palomar for further mechanical verification.
"""
from pathlib import Path
import hashlib
import json
import re
import tarfile

ROOT = Path(__file__).resolve().parents[1]
sha = lambda data: hashlib.sha256(data).hexdigest()


def main():
    freeze = json.loads((ROOT / "publication/formal-freeze/FREEZE.json").read_text())
    validation_path = ROOT / "publication/assembly/VALIDATION.json"
    validation = json.loads(validation_path.read_text())
    assert freeze["status"] == validation["status"] == "PASS"
    assert sha(validation_path.read_bytes()) == freeze["validation_sha256"]
    assert freeze["source_commit"] == validation["source_commit"]
    archive_path = ROOT / freeze["archive"]
    assert sha(archive_path.read_bytes()) == freeze["sha256"]
    prefix = "refined-absorption-formal-v1.0/"
    expected = {item["source"]: item["source_sha256"] for item in validation["sources"]}
    expected.update(validation["configuration_sha256"])
    with tarfile.open(archive_path, "r:gz") as archive:
        names = archive.getnames()
        assert len(names) == len(set(names)), "Duplicate archive entries."
        for path, digest in expected.items():
            assert sha((ROOT / path).read_bytes()) == digest, path
            assert sha(archive.extractfile(prefix + path).read()) == digest, path
        assert sha(archive.extractfile(prefix + "publication/assembly/VALIDATION.json").read()) == freeze["validation_sha256"]
    queries = 0
    for check in validation["axiom_checks"]:
        data = (ROOT / check["log"]).read_bytes()
        assert sha(data) == check["sha256"]
        messages = re.findall(r"depends on axioms:\s*\[(.*?)\]|does not depend on any axioms", data.decode(), re.S)
        assert len(messages) == check["queries"]
        for message in messages:
            axioms = {a.strip() for a in message.split(",") if a.strip()}
            assert axioms <= {"propext", "Classical.choice", "Quot.sound"}
        queries += len(messages)
    assert queries == freeze["axiom_queries"] == validation["axiom_query_count"]
    baseline = json.loads((ROOT / "provenance/source-baseline.json").read_text())
    with tarfile.open(ROOT / "provenance/original-lean-sources.tar.gz", "r:gz") as archive:
        for path, digest in baseline.items():
            assert sha(archive.extractfile(path).read()) == digest
    print(json.dumps({"status": "PASS_RECORDED_FREEZE_INTEGRITY", "source_commit": freeze["source_commit"],
                      "local_lean_sources": len(validation["sources"]), "axiom_queries": queries,
                      "original_sources": len(baseline), "lean_executed": False,
                      "scope": "Recorded evidence, archived source bytes and current source correspondence; not independent proof replay."}))


if __name__ == "__main__":
    main()
