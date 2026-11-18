"""Replay every numerical diagnostic and both interval implementations.

No manuscript or Lean build is required. See README for the limited Lean scope.
Each child runs sequentially; receipts include its exit status and log hash.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT/'reproduced')
    args = parser.parse_args()
    args.out = args.out.resolve()
    args.out.mkdir(parents=True, exist_ok=True)
    pins = json.loads((ROOT/'certificates/source-sha256.json').read_text())
    mismatches = [name for name, expected in pins.items()
                  if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != expected]
    (args.out/'source-pins.json').write_text(
        json.dumps({'checked': len(pins), 'mismatches': mismatches}, indent=2)+'\n')
    if mismatches:
        print('Source pin mismatch: '+', '.join(mismatches), file=sys.stderr)
        return 1
    print(f'Source pins: {len(pins)} verified', flush=True)
    jobs = [(p.stem, [sys.executable, str(p)]) for p in sorted((ROOT/'scripts').glob('t[1-9]_*.py'))]
    jobs.append(('independent', [sys.executable, str(ROOT/'scripts/rigor_independent.py'), '--mutant', '--out', str(args.out/'independent.json')]))
    env = os.environ.copy()
    for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
        env[key] = '2'
    receipts=[]
    for name, command in jobs:
        log=args.out/(name+'.log')
        with log.open('w',encoding='utf-8') as stream:
            code=subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
        receipt={'name':name,'exit_code':code,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
        receipts.append(receipt)
        print(f'{name}: exit {code}',flush=True)
    result={'utc':datetime.now(timezone.utc).isoformat(),'python':sys.version,
            'dependencies':{p:importlib.metadata.version(p) for p in ['numpy','scipy','mpmath','python-flint','sympy']},
            'children':receipts,'exit_code':int(any(r['exit_code'] for r in receipts))}
    (args.out/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    return result['exit_code']

if __name__=='__main__':
    sys.exit(main())
