"""Preserve the original Lean sources without redistributing the source papers."""
from pathlib import Path
import gzip
import hashlib
import io
import json
import tarfile

ROOT=Path(__file__).resolve().parents[1]
SOURCE=Path(r"C:\nw\aristotle-refined-extension-return-review-20261026\source")
baseline=json.loads((ROOT/"provenance/source-baseline.json").read_text(encoding="utf-8"))
archive=ROOT/"provenance/original-lean-sources.tar.gz"
with archive.open("wb") as raw:
    with gzip.GzipFile(fileobj=raw,mode="wb",mtime=0,filename="") as compressed:
        with tarfile.open(fileobj=compressed,mode="w|") as tar:
            for rel,digest in sorted(baseline.items()):
                data=(SOURCE/rel).read_bytes()
                assert hashlib.sha256(data).hexdigest()==digest
                info=tarfile.TarInfo(rel)
                info.size=len(data);info.mtime=0;info.mode=0o644
                tar.addfile(info,io.BytesIO(data))
print(json.dumps(dict(archive=archive.relative_to(ROOT).as_posix(),sources=len(baseline),
                     sha256=hashlib.sha256(archive.read_bytes()).hexdigest())))
