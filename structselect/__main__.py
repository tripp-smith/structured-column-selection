"""Sample a rational Parseval frame supplied as a JSON list of rows."""
from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction
import hashlib
import json
import sys
from pathlib import Path

from structselect import volume_sample
import structselect.volume_sampling as implementation


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('frame', type=Path)
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--max-proposals', type=int, default=1000000)
    parser.add_argument('--columns', type=int, default=None, help='column count for an empty-row frame')
    args = parser.parse_args()
    try:
        raw = args.frame.read_bytes()
        rows = json.loads(raw)
        implementation_before = Path(implementation.__file__).read_bytes()
        result = volume_sample(rows,seed=args.seed,max_proposals=args.max_proposals,n_columns=args.columns)
    except (OSError, ValueError, TypeError) as error:
        parser.error(str(error))
    implementation_after = Path(implementation.__file__).read_bytes()
    if implementation_before != implementation_after:
        parser.error('implementation changed during sampling; result is not certified')
    record = {'python_version':sys.version.split()[0], 'input_sha256' :hashlib.sha256(raw).hexdigest(),
              'implementation_sha256':hashlib.sha256(implementation_before).hexdigest(),
              'seed':args.seed,'max_proposals':args.max_proposals,
              'result':asdict(result)}
    print(json.dumps(record,sort_keys=True,default=lambda v:str(v) if isinstance(v,Fraction) else v))
    return 0 if result.ok else 2


if __name__ == '__main__':
    raise SystemExit(main())
