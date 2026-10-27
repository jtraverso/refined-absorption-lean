"""Measure the transitive Mathlib source scope of the migration import module."""
from pathlib import Path
import json
import re
import ast

ROOT=Path(__file__).resolve().parents[1]
setup=json.loads((ROOT/"migration/local-environment.json").read_text(encoding="utf-8"))
mathlib=next(Path(d["path"]) for d in setup["dependencies"] if d["name"]=="mathlib")
tree=ast.parse((ROOT/"tools/audit_migration.py").read_text(encoding="utf-8"))
fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="strip")
scope={}
exec(compile(ast.Module(body=[fn],type_ignores=[]),"strip-comments","exec"),scope)
imports=lambda p:re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)",scope["strip"](p.read_text(encoding="utf-8")),re.M)
seen=set();pending=imports(ROOT/"RequestProject/MathlibImports.lean")
while pending:
    name=pending.pop()
    if name in seen or not name.startswith("Mathlib"):
        continue
    seen.add(name)
    p=mathlib/(name.replace(".","/")+".lean")
    if p.exists():
        pending.extend(imports(p))
record=dict(selected_mathlib_modules=len(seen),
            total_mathlib_modules=sum(1 for _ in (mathlib/"Mathlib").rglob("*.lean")),
            imports_whole_mathlib="Mathlib" in seen,
            selected_modules=sorted(seen))
(ROOT/"migration/import-scope.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
print(json.dumps({k:v for k,v in record.items() if k!="selected_modules"}))
