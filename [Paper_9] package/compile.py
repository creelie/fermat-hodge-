from pathlib import Path
import os, subprocess, time, json, sys

root = Path(__file__).resolve().parent
env = dict(os.environ)
env['LEAN_PATH'] = str(root / 'lean') + ';' + Path(
    r'C:\CLAUDE PAPERS\closure-followup-2026-10-25\lean-path.txt').read_text().strip()
start = time.monotonic()
run = subprocess.run([
    r'C:\Users\user\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe',
    '-o', 'AffineReduction.olean', 'AffineReduction.lean'],
    cwd=root / 'lean', env=env, capture_output=True,
    text=True, encoding='utf8', errors='replace')
log = run.stdout + run.stderr
(root / 'lean-compile.log').write_text(log, encoding='utf8')
ok = run.returncode == 0 and all(x not in log for x in ['sorryAx', 'ofReduceBool', 'warning:'])
report = {'status': 'PASS' if ok else 'FAIL', 'exit_code': run.returncode,
          'seconds': round(time.monotonic() - start, 3), 'auxiliary_theorems': 3,
          'geometric_reduction_formalised': False, 'Hodge_conjecture_proved': False}
(root / 'lean-build.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf8')
print(log)
print(json.dumps(report))
sys.exit(not ok)
