from pathlib import Path
import hashlib,json,zipfile
root=Path(__file__).resolve().parents[1]
papers=root/'papers'
manifest=json.loads((papers/'package-manifest.json').read_text())
assert set(manifest['files'])=={p.name for p in papers.iterdir() if p.is_file() and p.name!='package-manifest.json'}
for name,digest in manifest['files'].items():
    assert hashlib.sha256((papers/name).read_bytes()).hexdigest()==digest,name
for path in papers.glob('*tex.zip'):
    with zipfile.ZipFile(path) as z:
        assert z.testzip() is None
        assert 'main.tex' in z.namelist()
        assert not any(Path(n).suffix in ('.lean','.aux','.log','.out','.pyc') for n in z.namelist())
        for n in z.namelist():
            assert not n.startswith('/') and '..' not in Path(n).parts
print('Current package hashes and TeX archive verified.')
