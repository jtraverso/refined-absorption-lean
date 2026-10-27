"""Audit source preservation and declaration signatures against the original archive."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument("--original",type=Path,default=Path(r"C:\nw\aristotle-refined-extension-return-review-20261026\source"))
parser.add_argument("--output",type=Path,default=Path("migration/source-audit.json"))
args=parser.parse_args()

def strip(text):
    out=[];i=depth=0;quoted=False
    while i<len(text):
        if depth:
            if text[i:i+2]=="/-":depth+=1;i+=2
            elif text[i:i+2]=="-/":depth-=1;i+=2
            else:
                if text[i]=="\n":out.append("\n")
                i+=1
        elif quoted:
            if text[i]=="\\":i+=2
            elif text[i]=='"':quoted=False;i+=1
            else:i+=1
        elif text[i:i+2]=="/-":depth=1;i+=2
        elif text[i:i+2]=="--":
            end=text.find("\n",i);i=len(text) if end<0 else end
        elif text[i]=='"':quoted=True;i+=1
        else:out.append(text[i]);i+=1
    return "".join(out)

decl=re.compile(r"^\s*(?:(?:public|private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([^\s:({]+)",re.M)

def signatures(text):
    code=strip(text)
    found=list(decl.finditer(code));result=[]
    for j,m in enumerate(found):
        end=found[j+1].start() if j+1<len(found) else len(code)
        snippet=code[m.start():end]
        assignment=snippet.find(":=")
        where=re.search(r"\bwhere\b",snippet)
        cuts=[x for x in [assignment,where.start() if where else -1] if x>=0]
        header=snippet[:min(cuts)] if cuts else snippet
        result.append((m.group(1),m.group(2),re.sub(r"\s+"," ",header).strip()))
    return result

baseline=json.loads((ROOT/"provenance/source-baseline.json").read_text(encoding="utf-8"))
changes=[];signature_diffs=[];deleted=[];flags=[]
output=ROOT/args.output
output.parent.mkdir(parents=True,exist_ok=True)
diffdir=output.parent/"source-diffs";diffdir.mkdir(exist_ok=True)
relocations=[]
for rel,digest in baseline.items():
    old=args.original/rel
    relocated=rel.replace("RequestProject/", "RefinedAbsorption/", 1) if rel.startswith("RequestProject/") else rel
    if relocated!=rel:relocations.append(dict(original=rel,current=relocated))
    new=ROOT/relocated
    assert hashlib.sha256(old.read_bytes()).hexdigest()==digest,rel
    if not new.exists():deleted.append(rel);continue
    before=old.read_text(encoding="utf-8");after=new.read_text(encoding="utf-8")
    current=hashlib.sha256(new.read_bytes()).hexdigest()
    if current!=digest:
        changes.append(dict(file=rel,current_file=relocated,before=digest,after=current))
        (diffdir/(rel.replace("/","_")+".diff")).write_text("".join(difflib.unified_diff(
            before.splitlines(True),after.splitlines(True),fromfile="original/"+rel,tofile="current/"+relocated)),encoding="utf-8")
        if signatures(before)!=signatures(after):signature_diffs.append(rel)
for top in ("RefinedAbsorption","checks"):
    for path in (ROOT/top).rglob("*.lean"):
        code=strip(path.read_text(encoding="utf-8"))
        for i,line in enumerate(code.splitlines(),1):
            if re.search(r"\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|extern)\b",line):
                flags.append(dict(file=path.relative_to(ROOT).as_posix(),line=i,text=line.strip()))
result=dict(original_lean_sources=len(baseline),deleted_original_sources=deleted,relocations=relocations,
    changed_sources=changes,signature_text_differences=signature_diffs,active_flags=flags,
    signature_audit_scope="Textual declaration-header comparison, not cross-version kernel equivalence.")
output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
print(json.dumps(dict(original_sources=len(baseline),changed=len(changes),deleted=deleted,
                     signature_differences=signature_diffs,active_flags=flags)))
