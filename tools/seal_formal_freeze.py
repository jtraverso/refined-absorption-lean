"""Seal the proved source commit together with its actual local build evidence.

This formal source archive precedes manuscript drafting. It is distinct from
the later document release archive and is never rewritten for editorial edits.
"""
from pathlib import Path
import gzip
import hashlib
import io
import json
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "publication/formal-freeze"
validation_path = ROOT / "publication/assembly/VALIDATION.json"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    validation = json.loads(validation_path.read_text())
    assert validation["status"] == "PASS"
    for item in validation["sources"]:
        assert sha(ROOT / item["source"]) == item["source_sha256"]
    for path, digest in validation["configuration_sha256"].items():
        assert sha(ROOT / path) == digest
    commit = validation["source_commit"]
    prefix = "refined-absorption-formal-v1.0/"
    OUT.mkdir(exist_ok=True)
    target = OUT / ("formal-v1.0-" + commit[:12] + ".tar.gz")
    assert not target.exists(), "The formal freeze is immutable; do not replace it."
    snapshot = subprocess.check_output(["git", "archive", "--format=tar", commit], cwd=ROOT)
    source_names = set()
    with target.open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0, filename="") as compressed:
            with tarfile.open(fileobj=compressed, mode="w|") as archive:
                with tarfile.open(fileobj=io.BytesIO(snapshot)) as original:
                    for member in original:
                        if not member.isfile():
                            continue
                        assert not member.name.startswith("publication/assembly/"), "Do not include unfinished build evidence in the source commit."
                        data = original.extractfile(member).read()
                        source_names.add(member.name)
                        item = tarfile.TarInfo(prefix + member.name)
                        item.size, item.mode, item.mtime = len(data), member.mode, 0
                        archive.addfile(item, io.BytesIO(data))
                evidence = ROOT / "publication/assembly"
                for path in sorted(p for p in evidence.rglob("*") if p.is_file()):
                    relative = path.relative_to(ROOT).as_posix()
                    assert relative not in source_names
                    data = path.read_bytes()
                    item = tarfile.TarInfo(prefix + relative)
                    item.size, item.mode, item.mtime = len(data), 0o644, 0
                    archive.addfile(item, io.BytesIO(data))
    digest = sha(target)
    with tarfile.open(target, "r:gz") as archive:
        for item in validation["sources"]:
            data = archive.extractfile(prefix + item["source"]).read()
            assert hashlib.sha256(data).hexdigest() == item["source_sha256"]
        assert hashlib.sha256(archive.extractfile(prefix + "publication/assembly/VALIDATION.json").read()).hexdigest() == sha(validation_path)
    target.with_suffix(target.suffix + ".sha256").write_text(digest + "  " + target.name + "\n", encoding="utf-8", newline="\n")
    receipt = {"status": "PASS", "source_commit": commit,
               "archive": target.relative_to(ROOT).as_posix(), "sha256": digest,
               "validation_sha256": sha(validation_path), "local_lean_modules": validation["current_modules"],
               "axiom_queries": validation["axiom_query_count"],
               "scope": "Immutable formal-source and local-build-evidence freeze, before manuscript drafting. Not a Palomar certificate or a document release archive."}
    (OUT / "FREEZE.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
