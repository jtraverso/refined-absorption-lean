"""Local syntax gate only; Palomar's Comparator and preflight remain separate."""
from pathlib import Path
import json
import hashlib
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
setup = json.loads((ROOT / "migration/local-environment.json").read_text())
paths = [str(Path(p["path"]) / ".lake/build/lib/lean") for p in setup["dependencies"]]
env = {**os.environ, "LEAN_PATH": os.pathsep.join(paths)}
record_path = ROOT / "publication/assembly/challenge-syntax.json"
prior = {r["module"]: r for r in json.loads(record_path.read_text())} if record_path.exists() else {}
results = []
for path in sorted((ROOT / "Palomar").glob("*Challenge.lean")):
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    previous = prior.get("Palomar." + path.stem)
    if previous and previous["exit_code"] == 0 and previous.get("source_sha256") == digest:
        results.append(previous)
        continue
    command = [setup["lean"], "--root=" + str(ROOT), "-j1", "-M4096", str(path)]
    log = ROOT / "publication/assembly" / (path.stem + "-syntax.log")
    clock = time.monotonic()
    with log.open("w", encoding="utf-8") as out:
        out.write("COMMAND " + json.dumps(command) + "\n"); out.flush()
        code = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT, timeout=600).returncode
    assert hashlib.sha256(path.read_bytes()).hexdigest() == digest
    results.append({"module": "Palomar." + path.stem, "exit_code": code,
                    "source_sha256": digest,
                    "seconds": round(time.monotonic() - clock, 2), "log": log.relative_to(ROOT).as_posix()})
    print(json.dumps(results[-1]), flush=True)
record_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
raise SystemExit(any(r["exit_code"] for r in results))
