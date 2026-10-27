"""Check the editorial release against its preserved semantic and repository baselines.

Does not run Lean. Human/agent visual and mathematical review is separately recorded.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,subprocess,sys,difflib
import pymupdf,yaml
from audit_preprints import math_spans
R=Path(__file__).resolve().parents[3]
B=R/'preprints/RESEARCH_NOTE_v1.0.1'
Q=B/'02_validation'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda p,x:p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
allowed={'.gitignore','README.md','CITATION.cff','PUBLICATION_INDEX.md','publication/AUDIT.md',
         *[f'Palomar/{s}/formalization.yaml' for s in ['Unified','Article2024','Survey2025','ResearchNote']]}
baseline=json.loads((Q/'BASELINE.json').read_text())
preserved=[];changed=[]
for item in baseline:
    p=R/item['path']; ok=p.is_file() and sha(p)==item['sha256']
    assert ok or item['path'] in allowed,item['path']
    (preserved if ok else changed).append(item['path'])
lean=[x for x in baseline if x['path'].endswith('.lean')]
assert len(lean)==317
assert all(sha(R/x['path'])==x['sha256'] for x in lean)
for name in ('lean-toolchain','lakefile.toml','lake-manifest.json'):
    assert name in preserved,name
freeze=subprocess.run([sys.executable,'tools/verify_formal_freeze.py'],cwd=R,capture_output=True,text=True,check=True)
frozen=json.loads(freeze.stdout)
assert frozen['status']=='PASS_RECORDED_FREEZE_INTEGRITY'
write(Q/'FORMAL_PRESERVATION.json',{'checked_utc':datetime.now(timezone.utc).isoformat(),
      'status':'PASS','lean_sources_unchanged':317,'baseline_files_unchanged':len(preserved),
      'allowed_metadata_files_changed':changed,'formal_freeze_check':frozen,'new_lean_run':False})
documents=[];protected=[]
for source in sorted(B.glob('*/*preprint_v1.0.1_*.md')):
    lang=source.stem[-2:]; old=Q/'baseline'/source.name
    a,b=old.read_text(encoding='utf-8'),source.read_text(encoding='utf-8')
    assert math_spans(a)==math_spans(b),source
    heading='## Abstract' if lang=='en' else '## Resumen'
    if source.parent.name=='01_manuscript':
        end='## 8. Code and data availability' if lang=='en' else '## 8. Disponibilidad del código y los datos'
        assert a[a.index(heading):a.index(end)]==b[b.index(heading):b.index(end)]
    else:
        aa=a[a.index(heading):].replace('### 2.3. Research note','### 2.3. Nota de investigación') if lang=='es' else a[a.index(heading):]
        if lang=='es':aa=aa.replace('lemas de packings finitos','lemas de empaquetamientos finitos')
        assert aa==b[b.index(heading):]
    ack='## Acknowledgements' if lang=='en' else '## Agradecimientos'
    assert a[a.index(ack):]==b[b.index(ack):]
    assert '**Version 1.0.1 DOI:**' in b or '**DOI de la versión 1.0.1:**' in b
    assert '10.5281/zenodo.23715622' in b
    assert 'unpublished' not in b and 'sin publicar' not in b
    with pymupdf.open(source.with_suffix('.pdf')) as pdf:
        assert pdf.metadata['title']==re.search(r"^title: '(.*)'$",b,re.M)[1]
    documents.append({'source':source.relative_to(R).as_posix(),'baseline_sha256':sha(old),
                      'source_sha256':sha(source),'pdf_sha256':sha(source.with_suffix('.pdf')),
                      'equations_identical':True,'proofs_identical_to_reviewed_baseline':True,
                      'acknowledgements_disclosure_bibliography_identical':True,
                      'diff':list(difflib.unified_diff(a.splitlines(),b.splitlines(),fromfile='reviewed baseline',tofile='release',lineterm=''))})
    protected.extend({'source':source.relative_to(R).as_posix(),'element':i,'type':'math span',
                      'sha256':hashlib.sha256(s.encode()).hexdigest(),'allowed_edit':'none'}
                     for i,s in enumerate(math_spans(b),1))
assert len(documents)==4
write(Q/'SEMANTIC_INTEGRITY.json',{'status':'PASS','documents':documents,'mathematical_changes_since_reviewed_baseline':False})
write(Q/'PROTECTED_ELEMENT_INDEX.json',protected)
cff=yaml.safe_load((R/'CITATION.cff').read_text(encoding='utf-8'))
assert cff['version']=='1.0.1' and cff['doi']=='10.5281/zenodo.23715622'
for name in ('Unified','Article2024','Survey2025','ResearchNote'):
    path=R/f'Palomar/{name}/formalization.yaml'
    metadata=yaml.safe_load(path.read_text(encoding='utf-8'))
    row=next(x for x in metadata['sources'] if x['id']=='doi:10.5281/zenodo.23715622')
    assert row['title']==cff['title'] and '1.0.1' in row['location']
for name in ['README.md','PUBLICATION_INDEX.md','CHANGELOG.md']:
    s=(R/name).read_text(encoding='utf-8');assert '1.0.1' in s and '23715622' in s
assert json.loads((Q/'AUDIT_RESULT.json').read_text())['status']=='PASS_LOCAL_DOCUMENT_CHECKS'
visual=json.loads((Q/'VISUAL_QA.json').read_text())
assert visual['status']=='PASS'
for d in visual['documents']:assert sha(R/d['pdf'])==d['pdf_sha256']
for name in ('RELEASE_AUDIT.md','SEMANTIC_INTEGRITY.md'):
    assert 'EDITORIALLY_READY' in (Q/name).read_text(encoding='utf-8')
result={'status':'PASS','version':'1.0.1','checked_utc':datetime.now(timezone.utc).isoformat(),
        'editorial_verdict':'EDITORIALLY_READY','document_count':4,'pages':sum(x['page_count'] for x in visual['documents']),
        'lean_sources_unchanged':317,'baseline_files_unchanged':len(preserved),'allowed_metadata_changes':changed,
        'selected_endpoint_queries':18,'recorded_axiom_queries':360,'fresh_lean_build':False,
        'scope':'Internal editorial, semantic-preservation, bilingual, visual, metadata and recorded-formal-evidence audit. Not certification of complete source-paper coverage, new kernel replay or independent human peer review.',
        'unresolved_publication_blockers':[],'documents':[{k:v for k,v in d.items() if k!='diff'} for d in documents]}
write(Q/'RELEASE_AUDIT.json',result)
print(json.dumps({k:v for k,v in result.items() if k not in ['documents','scope','allowed_metadata_changes']}))
