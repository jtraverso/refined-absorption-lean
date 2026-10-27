"""Seal the audited document package; never changes the historical release."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,zipfile
R=Path(__file__).resolve().parents[3]
B=R/'preprints/RESEARCH_NOTE_v1.0.1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
audit=json.loads((B/'02_validation/RELEASE_AUDIT.json').read_text())
assert audit['status']=='PASS'
for d in audit['documents']:
    source=R/d['source']
    assert sha(source)==d['source_sha256']
    assert sha(source.with_suffix('.pdf'))==d['pdf_sha256']
I=B/'04_integrity';I.mkdir(exist_ok=True)
files=[p for p in sorted(B.rglob('*')) if p.is_file() and not {'_render','__pycache__','04_integrity'} & set(p.relative_to(B).parts)]
manifest=[{'path':p.relative_to(B).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size} for p in files]
(I/'MANIFEST.json').write_text(json.dumps({'version':'1.0.1','files':manifest},indent=2)+'\n',encoding='utf-8',newline='\n')
(I/'SHA256SUMS.txt').write_text(''.join(f"{x['sha256']}  {x['path']}\n" for x in manifest)+f"{sha(I/'MANIFEST.json')}  04_integrity/MANIFEST.json\n",encoding='utf-8',newline='\n')
out=R/'publication/document-release/v1.0.1';out.mkdir(parents=True,exist_ok=True)
archive=out/'refined-absorption-preprint-v1.0.1.zip'
packed=files+[I/'MANIFEST.json',I/'SHA256SUMS.txt']
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in packed:z.write(p,'RESEARCH_NOTE_v1.0.1/'+p.relative_to(B).as_posix())
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None and len(z.namelist())==len(packed)
    for p in packed:assert hashlib.sha256(z.read('RESEARCH_NOTE_v1.0.1/'+p.relative_to(B).as_posix())).hexdigest()==sha(p)
(out/(archive.name+'.sha256')).write_text(f'{sha(archive)}  {archive.name}\n',encoding='utf-8',newline='\n')
receipt={'status':'PASS_SEALED_DOCUMENT_PACKAGE','version':'1.0.1','doi':'10.5281/zenodo.23715622',
         'sealed_utc':datetime.now(timezone.utc).isoformat(),'archive':archive.relative_to(R).as_posix(),
         'archive_sha256':sha(archive),'files':len(packed),'manifest_sha256':sha(I/'MANIFEST.json'),
         'audit_sha256':sha(B/'02_validation/RELEASE_AUDIT.json'),'formal_source_commit':'5428ee9b772e67dd7ec6da443199b36a003b72d4',
         'scope':'Document package; public upload outcomes recorded separately.'}
(out/'RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(receipt))
