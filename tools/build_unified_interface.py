"""Check the additive single-entry Challenge without altering the formal freeze."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "publication/palomar/unified-build"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    frozen = json.loads((ROOT / "publication/assembly/VALIDATION.json").read_text())
    assert frozen["status"] == "PASS"
    expected = {x["source"]: x["source_sha256"] for x in frozen["sources"]}
    expected.update(frozen["configuration_sha256"])
    for path, digest in expected.items():
        assert sha(ROOT / path) == digest, path
    source = ROOT / "Palomar/UnifiedChallenge.lean"
    config = json.loads((ROOT / "Palomar/Unified.comparator.json").read_text())
    selected = {name for entry in ("Article2024", "Survey2025", "ResearchNote")
                for name in json.loads((ROOT / f"Palomar/{entry}.comparator.json").read_text())["theorem_names"]}
    assert set(config["theorem_names"]) == selected and len(selected) == 18
    assert config["solution_module"] == "RefinedAbsorption"
    digest = sha(source)
    base = ["lake", "--quiet"]
    if (ROOT / ".lake/local-packages.json").is_file():
        base += ["--packages=.lake/local-packages.json"]
    result = {"status": "RUNNING", "started_utc": datetime.now(timezone.utc).isoformat(),
              "frozen_formal_source_commit": frozen["source_commit"],
              "retained_frozen_sources": len(frozen["sources"]),
              "new_challenge": source.relative_to(ROOT).as_posix(),
              "new_challenge_sha256": digest, "selected_theorems": 18,
              "solution_module": "RefinedAbsorption", "commands": [],
              "scope": "Additive comparison interface. All 316 frozen sources and the configuration remain byte-identical. The new Challenge deliberately has statement placeholders. This is local Lake evidence, not an official Comparator pass."}
    for name, command in [
        ("challenge", base + ["build", "+Palomar.UnifiedChallenge:olean"]),
        ("default", base + ["build"]),
    ]:
        log = OUT / (name + ".log")
        started = time.monotonic()
        with log.open("w", encoding="utf-8", newline="\n") as stream:
            stream.write("COMMAND " + json.dumps(command) + "\n")
            stream.flush()
            code = subprocess.run(command, cwd=ROOT, env={**os.environ, "LEAN_NUM_THREADS": "2"},
                                  stdout=stream, stderr=subprocess.STDOUT).returncode
        item = {"command": command, "exit_code": code,
                "seconds": round(time.monotonic() - started, 2),
                "log": log.relative_to(ROOT).as_posix(), "log_sha256": sha(log)}
        result["commands"].append(item)
        if code:
            result["status"] = "FAIL"
        (OUT / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n",
                                       encoding="utf-8", newline="\n")
        print(json.dumps(item), flush=True)
        assert code == 0, log
    for path, frozen_digest in expected.items():
        assert sha(ROOT / path) == frozen_digest, path
    assert sha(source) == digest
    trace = ROOT / ".lake/build/lib/lean/Palomar/UnifiedChallenge.trace"
    assert trace.is_file()
    result.update(status="PASS", finished_utc=datetime.now(timezone.utc).isoformat(),
                  trace_sha256=sha(trace), current_local_sources=317)
    (OUT / "UnifiedChallenge.trace.json").write_bytes(trace.read_bytes())
    (OUT / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n",
                                   encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"], "selected_theorems": 18,
                      "current_local_sources": 317}), flush=True)


if __name__ == "__main__":
    main()
