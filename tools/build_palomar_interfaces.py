"""Build the six standalone interfaces sequentially, then the default targets.

This is a local Lake compilation record, not the official Comparator preflight.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "publication/assembly"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    prior = json.loads((OUT / "lake-state.json").read_text())
    assert prior["status"] == "PASS"
    configuration = (ROOT / "lakefile.toml").read_text()
    assert 'name = "Palomar"' in configuration and '"Palomar"' in configuration.split("defaultTargets = ")[1].splitlines()[0]
    base = ["lake", "--quiet"]
    if (ROOT / ".lake/local-packages.json").is_file():
        base += ["--packages=.lake/local-packages.json"]
    env = {**os.environ, "LEAN_NUM_THREADS": "2"}
    result = {"status": "RUNNING", "started_utc": datetime.now(timezone.utc).isoformat(),
              "configuration_sha256": sha(ROOT / "lakefile.toml"), "modules": []}
    report = OUT / "palomar-interface-lake.json"
    for source in sorted((ROOT / "Palomar").glob("*.lean")):
        name = "Palomar." + source.stem
        digest = sha(source)
        command = base + ["build", "+" + name + ":olean"]
        log = OUT / (name + ".log")
        start = time.monotonic()
        with log.open("w", encoding="utf-8", newline="\n") as output:
            output.write("COMMAND " + json.dumps(command) + "\n"); output.flush()
            code = subprocess.run(command, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT).returncode
        assert sha(source) == digest
        item = {"module": name, "source_sha256": digest, "exit_code": code,
                "seconds": round(time.monotonic() - start, 2), "log": log.relative_to(ROOT).as_posix()}
        result["modules"].append(item)
        if code:
            result["status"] = "FAILED"
        report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(json.dumps(item), flush=True)
        assert code == 0, log
    assert len(result["modules"]) == 6
    command = base + ["build"]
    with (OUT / "lake-build-with-palomar.log").open("w", encoding="utf-8", newline="\n") as output:
        output.write("COMMAND " + json.dumps(command) + "\n"); output.flush()
        code = subprocess.run(command, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT).returncode
    result.update(status="PASS" if code == 0 else "FAILED", final_command=command,
                  final_exit_code=code, finished_utc=datetime.now(timezone.utc).isoformat())
    report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"], "modules": len(result["modules"])}), flush=True)
    assert code == 0


if __name__ == "__main__":
    main()
