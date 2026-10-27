"""Build all local modules with Lake, bounding memory on this Windows host.

The clean start is recorded before ExternalProofs was built. Dependencies may
use their existing pinned caches. Lake, not this scheduler, owns all traces.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--jobs", type=int, default=3)
args = parser.parse_args()
evidence = ROOT / "publication/assembly"
start = json.loads((evidence / "clean-build-start.json").read_text())
assert start["project_build_directory_initially_absent"]
sources = {path.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): path
           for top in ("RefinedAbsorption", "checks") for path in (ROOT / top).rglob("*.lean")}
sources["RefinedAbsorption"] = ROOT / "RefinedAbsorption.lean"
imports = lambda path: re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)", path.read_text(encoding="utf-8"), re.M)
deps = {name: [item for item in imports(path) if item in sources] for name, path in sources.items()}
heavy = lambda name: name.startswith("RefinedAbsorption.Upstream.") or name in {
    "RefinedAbsorption", "RefinedAbsorption.ExternalProofs", "RefinedAbsorption.Assembly", "checks.AssemblyAxioms"}
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
run = evidence / ("lake-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
run.mkdir()
env = {**os.environ, "LEAN_NUM_THREADS": "2"}
state = dict(status="RUNNING", required=len(sources), started_utc=datetime.now(timezone.utc).isoformat(),
             run=run.relative_to(ROOT).as_posix(), compiled=[], failed={}, current=[])
pending = set(sources)
done = set()
running = {}

def save():
    state["checked"] = len(done)
    state["current"] = sorted(running.values())
    state["updated_utc"] = datetime.now(timezone.utc).isoformat()
    (evidence / "lake-state.json").write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8", newline="\n")

def build(name):
    path = sources[name]
    digest = sha(path)
    command = ["lake", "--quiet", "--packages=.lake/local-packages.json", "build", "+" + name + ":olean"]
    log = run / (name + ".log")
    clock = time.monotonic()
    with log.open("w", encoding="utf-8") as output:
        output.write("COMMAND " + json.dumps(command) + "\n"); output.flush()
        try:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT, timeout=2400)
            code = result.returncode
        except subprocess.TimeoutExpired:
            output.write("\nTIMEOUT after 2400 seconds\n"); code = 124
    assert sha(path) == digest, "Source changed during Lake build: " + name
    return dict(module=name, source_sha256=digest, exit_code=code, seconds=round(time.monotonic()-clock, 2), log=log.relative_to(ROOT).as_posix())

with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    while pending or running:
        for name in sorted(pending):
            if len(running) >= args.jobs or any(heavy(item) for item in running.values()):
                break
            if not all(item in done for item in deps[name]):
                continue
            if heavy(name) and running:
                continue
            pending.remove(name)
            running[pool.submit(build, name)] = name
            if heavy(name):
                break
        save()
        if not running:
            raise RuntimeError("Blocked local import graph: " + repr(sorted(pending)))
        completed, _ = wait(running, timeout=10, return_when=FIRST_COMPLETED)
        for future in completed:
            name = running.pop(future)
            record = future.result()
            if record["exit_code"]:
                state["failed"][name] = record
            else:
                done.add(name); state["compiled"].append(record)
            print(json.dumps(record), flush=True)
        save()
        if state["failed"]:
            state["status"] = "FAILED"; save()
            raise SystemExit(1)
command = ["lake", "--quiet", "--packages=.lake/local-packages.json", "build"]
with (evidence / "lake-build-final.log").open("w", encoding="utf-8") as output:
    output.write("COMMAND " + json.dumps(command) + "\n"); output.flush()
    code = subprocess.run(command, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT).returncode
state.update(status="PASS" if code == 0 else "FAILED", final_command=command, final_exit_code=code,
             finished_utc=datetime.now(timezone.utc).isoformat())
save()
print(json.dumps(dict(status=state["status"], checked=len(done), required=len(sources))), flush=True)
raise SystemExit(code)
