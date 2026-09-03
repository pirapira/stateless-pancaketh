#!/usr/bin/env python3
"""gen_fp384_vectors.py OUT_INPUT OUT_ORACLE.py [--count N] [--seed S]
Vectors for guest/test/t_fp384.pnk (see its header for the record layout).
Pure-int oracle: canonical modular arithmetic mod the BLS12-381 prime."""
import argparse, os, struct, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blsref import P

ap = argparse.ArgumentParser()
ap.add_argument("inp"); ap.add_argument("oracle")
ap.add_argument("--count", type=int, default=12); ap.add_argument("--seed", type=int, default=7)
a = ap.parse_args()
import random
rnd = random.Random(a.seed)
def limbs48(x): return b"".join(struct.pack("<Q", (x >> (64 * i)) & (2**64 - 1)) for i in range(6))
cases = [(0, 0), (1, 1), (P - 1, P - 1), (P - 1, 1), (2, (P - 1) // 2), (0, 5), ((P + 1) // 2, 3)]
while len(cases) < a.count:
    cases.append((rnd.randrange(P), rnd.randrange(P)))
blob = b"".join(limbs48(x) + limbs48(y) for x, y in cases)
exp = b""
for x, y in cases:
    inv = pow(x, P - 2, P) if x else 0
    s = (x & 1) | ((1 if x > (P - 1) // 2 else 0) << 1) | ((1 if x == y else 0) << 2)
    exp += b"".join(limbs48(v) for v in [x * y % P, (x + y) % P, (x - y) % P, inv, (-x) % P, pow(x, (P + 1) // 4, P), x]) + struct.pack("<Q", s)
open(a.inp, "wb").write(struct.pack("<Q", len(blob)) + blob + b"\0" * (-len(blob) % 8))
open(a.oracle, "w").write(f"def expected(blob):\n    return {exp.hex()!r}\n")
print(f"{len(cases)} cases, {len(exp)} expected bytes")
