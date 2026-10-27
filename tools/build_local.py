"""Compile every project source against pinned read-only local dependencies.

This offline migration runner writes no shared cache and never downloads packages.
The portable public configuration remains lakefile.toml plus lake-manifest.json.
Successful local compilation is recorded separately from a standard Lake/CI run.
"""
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument("--jobs",type=int,default=2)
args=parser.parse_args()
setup=json.loads((ROOT/"migration/local-environment.json").read_text(encoding="utf-8"))
lean=setup["lean"]
dep_paths=[Path(p["path"]) for p in setup["dependencies"]]
lib=ROOT/".lake/build/lib/lean"
lib.mkdir(parents=True,exist_ok=True)
env={**os.environ,"LEAN_PATH":os.pathsep.join(str(p) for p in [lib]+[d/".lake/build/lib/lean" for d in dep_paths])}
stamp=datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
run=ROOT/"migration/build"/stamp
run.mkdir(parents=True)
statepath=ROOT/"migration/build/state.json"
verifiedpath=ROOT/"migration/build/verified.json"
verified=json.loads(verifiedpath.read_text()) if verifiedpath.exists() else {}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources={p.relative_to(ROOT).with_suffix("").as_posix().replace("/","."):p
    for top in ("RequestProject","checks") for p in (ROOT/top).rglob("*.lean")}
deps={n:re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)",
                 p.read_text(encoding="utf-8"),re.M) for n,p in sources.items()}
for n, imports in deps.items():
    for child in imports:
        if child.startswith(("RequestProject.","checks.")):
            assert child in sources,(n,child)
state=dict(state="RUNNING",pid=os.getpid(),started_utc=datetime.now(timezone.utc).isoformat(),
    lean_version=subprocess.check_output([lean,"--version"],text=True).strip(),
    mathlib_commit=setup["mathlib_commit"],required=len(sources),jobs=args.jobs,
    compiled=[],reused=[],failed={},blocked=[],current=[],run=str(run.relative_to(ROOT)))
done={}
pending=set(sources)
running={}

def save():
    state["updated_utc"]=datetime.now(timezone.utc).isoformat()
    state["current"]=sorted(running.values())
    statepath.write_text(json.dumps(state,indent=2)+"\n",encoding="utf-8")
    verifiedpath.write_text(json.dumps(verified,indent=2)+"\n",encoding="utf-8")

def fingerprint(n):
    return hashlib.sha256(json.dumps(dict(source=sha(sources[n]),
       imports={c:done.get(c,"PINNED_"+setup["mathlib_commit"]) for c in deps[n]}),sort_keys=True).encode()).hexdigest()

def compile_one(n,digest):
    p=sources[n]
    obj=lib/p.relative_to(ROOT).with_suffix(".olean")
    obj.parent.mkdir(parents=True,exist_ok=True)
    log=run/(n+".log")
    cmd=[lean,"--root="+str(ROOT),"-j1","-M4096","-DmaxHeartbeats=1600000",
         "-DmaxRecDepth=8192","-o",str(obj),"-i",str(obj.with_suffix(".ilean")),str(p)]
    start=time.monotonic()
    with log.open("w",encoding="utf-8") as out:
        out.write("COMMAND "+json.dumps(cmd)+"\n");out.flush()
        try:
            code=subprocess.run(cmd,cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=1800).returncode
        except subprocess.TimeoutExpired:
            out.write("\nTIMEOUT after 1800 seconds\n");code=124
    return dict(module=n,exit_code=code,seconds=round(time.monotonic()-start,2),
                fingerprint=digest,log=str(log.relative_to(ROOT)),source_sha256=sha(p))

save()
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    while pending or running:
        for n in sorted(list(pending)):
            if any(c in state["failed"] or c in state["blocked"] for c in deps[n]):
                pending.remove(n);state["blocked"].append(n)
                continue
            if len(running)>=args.jobs:
                break
            if any(c in sources and c not in done for c in deps[n]):
                continue
            digest=fingerprint(n)
            obj=lib/sources[n].relative_to(ROOT).with_suffix(".olean")
            pending.remove(n)
            if verified.get(n)==digest and obj.exists():
                done[n]=digest;state["reused"].append(n)
                continue
            future=pool.submit(compile_one,n,digest)
            running[future]=n
        save()
        if not running:
            if pending:
                state["blocked"].extend(sorted(pending));pending.clear()
            break
        completed,_=wait(running,return_when=FIRST_COMPLETED,timeout=10)
        for future in completed:
            n=running.pop(future)
            event=future.result()
            if event["exit_code"]:
                state["failed"][n]=event
            else:
                done[n]=event["fingerprint"];verified[n]=event["fingerprint"]
                state["compiled"].append(event)
            print(json.dumps(event),flush=True)
        save()
state.update(state="PASS" if not state["failed"] and not state["blocked"] else "FAILED",
             finished_utc=datetime.now(timezone.utc).isoformat(),checked=len(done))
save()
print(json.dumps(dict(state=state["state"],checked=len(done),required=len(sources),failed=list(state["failed"]))))
raise SystemExit(0 if state["state"]=="PASS" else 1)
