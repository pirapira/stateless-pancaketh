#!/usr/bin/env python3
"""gen_bn254_vectors.py [--seed S] [--pairings N] [--only TYPES] OUT_INPUT OUT_EXPECTED
Test vectors for guest/test/t_bn254.pnk (alt_bn128 ECADD / ECMUL / ECPAIRING,
lib/bn254.pnk).  Oracle: py_ecc.optimized_bn128 exactly as
execution-specs alt_bn128.py uses it, so run under
  uv run --directory evm-asm/execution-specs python tools/gen_bn254_vectors.py ...
`expected(blob)` (also imported by guest/test/exp_bn254.py for tools/unit.py)
evaluates a whole input blob.

Record framing (both directions): [8 type LE][8 len LE][payload padded to 8].
  1 ECADD    call data -> [8 err][64 result or zeros]   (err 1 = invalid point)
  2 ECMUL    call data -> [8 err][64]
  3 PAIRING  call data -> [8 status] 0 false / 1 true / 2 invalid / 3 bad length
  4 FQMUL    [32 a][32 b] -> [32 a*b mod p]
  5 PAIR_RAW valid 192-byte pair -> [384 pairing(q, p) coefficients BE]
  6 F12MUL   [384][384] -> [384]
  7 F12INV   [384] -> [384]
  8 FROB     [384] -> [384 a^p]
--only lists the record types to emit (e.g. --only 1,2,4)."""
import argparse, random, struct, sys

from py_ecc.optimized_bn128 import optimized_curve as C
from py_ecc.optimized_bn128 import optimized_pairing as PR
from py_ecc.fields import optimized_bn128_FQ as FQ, optimized_bn128_FQ2 as FQ2, optimized_bn128_FQ12 as FQ12

P = C.field_modulus
R = C.curve_order
G1, G2 = C.G1, C.G2
INF1 = (FQ.one(), FQ.one(), FQ.zero())


def be32(x):
    return int(x).to_bytes(32, "big")


def g1_bytes(pt):
    if C.is_inf(pt):
        return bytes(64)
    x, y = C.normalize(pt)
    return be32(x.n) + be32(y.n)


def g2_bytes(pt):
    if C.is_inf(pt):
        return bytes(128)
    x, y = C.normalize(pt)
    return be32(x.coeffs[1]) + be32(x.coeffs[0]) + be32(y.coeffs[1]) + be32(y.coeffs[0])


def fq12_bytes(f):
    return b"".join(be32(c) for c in f.coeffs)


def fq12_from_bytes(b):
    return FQ12([int.from_bytes(b[i * 32:(i + 1) * 32], "big") for i in range(12)])


def buffer_read(data, start, size):
    out = data[start:start + size]
    return out + bytes(size - len(out))


class Invalid(Exception):
    pass


def bytes_to_g1(data):
    x = int.from_bytes(data[:32], "big")
    y = int.from_bytes(data[32:64], "big")
    if x >= P or y >= P:
        raise Invalid("field")
    z = 0 if (x == 0 and y == 0) else 1
    pt = (FQ(x), FQ(y), FQ(z))
    if not C.is_on_curve(pt, C.b):
        raise Invalid("curve")
    return pt


def bytes_to_g2(data):
    x0 = int.from_bytes(data[:32], "big")
    x1 = int.from_bytes(data[32:64], "big")
    y0 = int.from_bytes(data[64:96], "big")
    y1 = int.from_bytes(data[96:128], "big")
    if x0 >= P or x1 >= P or y0 >= P or y1 >= P:
        raise Invalid("field")
    x = FQ2((x1, x0))
    y = FQ2((y1, y0))
    z = (0, 0) if (x == FQ2((0, 0)) and y == FQ2((0, 0))) else (1, 0)
    pt = (x, y, FQ2(z))
    if not C.is_on_curve(pt, C.b2):
        raise Invalid("curve")
    return pt


def ecadd(data):
    try:
        p0 = bytes_to_g1(buffer_read(data, 0, 64))
        p1 = bytes_to_g1(buffer_read(data, 64, 64))
    except Invalid:
        return struct.pack("<Q", 1) + bytes(64)
    return struct.pack("<Q", 0) + g1_bytes(C.add(p0, p1))


def ecmul(data):
    try:
        p0 = bytes_to_g1(buffer_read(data, 0, 64))
    except Invalid:
        return struct.pack("<Q", 1) + bytes(64)
    n = int.from_bytes(buffer_read(data, 64, 32), "big")
    return struct.pack("<Q", 0) + g1_bytes(C.multiply(p0, n))


def pairing_check(data):
    if len(data) % 192 != 0:
        return struct.pack("<Q", 3)
    result = FQ12.one()
    for i in range(len(data) // 192):
        try:
            p = bytes_to_g1(buffer_read(data, 192 * i, 64))
            q = bytes_to_g2(buffer_read(data, 192 * i + 64, 128))
        except Invalid:
            return struct.pack("<Q", 2)
        if not C.is_inf(C.multiply(p, R)):
            return struct.pack("<Q", 2)
        if not C.is_inf(C.multiply(q, R)):
            return struct.pack("<Q", 2)
        result *= PR.pairing(q, p)
    return struct.pack("<Q", 1 if result == FQ12.one() else 0)


def eval_record(ty, payload):
    if ty == 1:
        return ecadd(payload)
    if ty == 2:
        return ecmul(payload)
    if ty == 3:
        return pairing_check(payload)
    if ty == 4:
        a = int.from_bytes(payload[:32], "big")
        b = int.from_bytes(payload[32:64], "big")
        return be32(a * b % P)
    if ty == 5:
        p = bytes_to_g1(payload[:64])
        q = bytes_to_g2(payload[64:192])
        return fq12_bytes(PR.pairing(q, p))
    if ty == 6:
        return fq12_bytes(fq12_from_bytes(payload[:384]) * fq12_from_bytes(payload[384:768]))
    if ty == 7:
        return fq12_bytes(fq12_from_bytes(payload[:384]).inv())
    if ty == 8:
        return fq12_bytes(fq12_from_bytes(payload[:384]) ** P)
    raise ValueError(ty)


def pad8(b):
    return b + bytes((-len(b)) % 8)


def frame(ty, payload):
    return struct.pack("<QQ", ty, len(payload)) + pad8(payload)


def expected(blob):
    out = b""
    pos = 0
    while pos < len(blob):
        ty, n = struct.unpack("<QQ", blob[pos:pos + 16])
        payload = blob[pos + 16:pos + 16 + n]
        out += frame(ty, eval_record(ty, payload))
        pos += 16 + ((n + 7) & ~7)
    return out


# ---- FQ2 square root (Tonelli-Shanks) to build twist points outside the subgroup ----
def fq2_sqrt(a):
    one = FQ2.one()
    order = P * P - 1
    if a ** (order // 2) != one:
        return None
    q, s = order, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = FQ2([2, 1])
    while z ** (order // 2) == one:
        z = FQ2([z.coeffs[0] + 1, z.coeffs[1]])
    m, c, t, r = s, z ** q, a ** q, a ** ((q + 1) // 2)
    while t != one:
        i, tt = 0, t
        while tt != one:
            tt = tt * tt
            i += 1
        b = c ** (2 ** (m - i - 1))
        m, c, t, r = i, b * b, t * b * b, r * b
    return r


def non_subgroup_g2(rng):
    while True:
        x = FQ2([rng.randrange(P), rng.randrange(P)])
        y = fq2_sqrt(x ** 3 + C.b2)
        if y is None:
            continue
        pt = (x, y, FQ2.one())
        assert C.is_on_curve(pt, C.b2)
        if not C.is_inf(C.multiply(pt, R)):
            return pt


def neg_bytes_g1(b):
    x, y = b[:32], int.from_bytes(b[32:], "big")
    return x + be32((P - y) % P)


def make_cases(rng, n_pairings):
    recs = []
    m1 = lambda k: C.multiply(G1, k)
    m2 = lambda k: C.multiply(G2, k)
    # 4: field multiply
    for a, b in [(0, 5), (1, P - 1), (P - 1, P - 1), (2, 3), (P - 1, 1)] + \
                [(rng.randrange(P), rng.randrange(P)) for _ in range(6)]:
        recs.append((4, be32(a) + be32(b)))
    # 1: ECADD
    g = g1_bytes(G1)
    recs += [(1, g + g), (1, g + g1_bytes(m1(2))), (1, g + bytes(64)), (1, bytes(128)),
             (1, g + neg_bytes_g1(g)), (1, b""), (1, g), (1, g + g + b"\x11" * 40),
             (1, be32(P) + be32(2) + g), (1, g + be32(1) + be32(2 ** 256 - 1)),
             (1, be32(1) + be32(3) + g), (1, g + g[:36])]
    for _ in range(6):
        a, b = m1(rng.randrange(1, R)), m1(rng.randrange(1, R))
        recs.append((1, g1_bytes(a) + g1_bytes(b)))
    recs.append((1, g1_bytes(m1(7)) + g1_bytes(m1(7))))
    # 2: ECMUL
    recs += [(2, g + be32(0)), (2, g + be32(1)), (2, g + be32(2)), (2, g + be32(R)),
             (2, g + be32(R + 1)), (2, g + be32(2 ** 256 - 1)), (2, bytes(64) + be32(5)),
             (2, be32(1) + be32(3) + be32(2)), (2, g), (2, g + be32(rng.randrange(2 ** 256))[:16]),
             (2, be32(P) + be32(2) + be32(1))]
    for _ in range(4):
        recs.append((2, g1_bytes(m1(rng.randrange(1, R))) + be32(rng.randrange(2 ** 256))))
    # 3: pairing checks
    q = g2_bytes(G2)
    a, b = rng.randrange(1, R), rng.randrange(1, R)
    pairings = [
        (b"", "empty"),
        (g + q + neg_bytes_g1(g) + q, "e(G,Q) e(-G,Q)"),
        (g1_bytes(m1(a)) + g2_bytes(m2(b)) + neg_bytes_g1(g1_bytes(m1(a * b % R))) + q, "e(aG,bQ) e(-abG,Q)"),
        (g1_bytes(m1(a)) + g2_bytes(m2(b)) + g1_bytes(m1(b)) + g2_bytes(C.neg(m2(a))), "e(aG,bQ) e(bG,-aQ)"),
        (g + q, "e(G,Q) alone -> false"),
        (g + q + g + q + neg_bytes_g1(g1_bytes(m1(2))) + q, "3 pairs true"),
        (g1_bytes(m1(3)) + q + neg_bytes_g1(g) + q, "false"),
        (bytes(64) + q, "inf G1 -> true"),
        (g + bytes(128), "inf G2 -> true"),
        (be32(1) + be32(3) + q, "G1 off curve"),
        (g + be32(P) + q[32:], "G2 coord = p"),
        (g + q[32:64] + q[:32] + q[64:], "G2 swapped re/im"),
        (g + g2_bytes(non_subgroup_g2(rng)), "G2 not in subgroup"),
        (bytes(64) + g2_bytes(non_subgroup_g2(rng)), "inf G1, G2 not in subgroup"),
        ((g + q)[:191], "191 bytes"),
        (g + q + b"\x00", "193 bytes"),
    ]
    for data, _ in pairings[:n_pairings] if n_pairings >= 0 else pairings:
        recs.append((3, data))
    # 5: raw pairings
    recs.append((5, g + q))
    recs.append((5, g1_bytes(m1(2)) + g2_bytes(m2(rng.randrange(1, R)))))
    # 6/7/8: FQ12 algebra
    for _ in range(3):
        fa = [rng.randrange(P) for _ in range(12)]
        fb = [rng.randrange(P) for _ in range(12)]
        recs.append((6, fq12_bytes(FQ12(fa)) + fq12_bytes(FQ12(fb))))
        recs.append((7, fq12_bytes(FQ12(fa))))
        recs.append((8, fq12_bytes(FQ12(fa))))
    recs.append((7, fq12_bytes(FQ12([1] + [0] * 11))))
    recs.append((7, fq12_bytes(FQ12([0, 1] + [0] * 10))))
    return recs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--pairings", type=int, default=-1, help="how many pairing-check cases (default all)")
    ap.add_argument("--only", default="", help="comma separated record types to keep")
    ap.add_argument("out_input")
    ap.add_argument("out_expected")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    recs = make_cases(rng, args.pairings)
    if args.only:
        keep = {int(t) for t in args.only.split(",")}
        recs = [r for r in recs if r[0] in keep]
    blob = b"".join(frame(ty, pl) for ty, pl in recs)
    exp = expected(blob)
    with open(args.out_input, "wb") as f:
        f.write(struct.pack("<Q", len(blob)) + pad8(blob))
    with open(args.out_expected, "wb") as f:
        f.write(exp)
    from collections import Counter
    print(f"{len(recs)} records {dict(sorted(Counter(t for t, _ in recs).items()))}, "
          f"input {len(blob)} bytes, expected {len(exp)} bytes")


if __name__ == "__main__":
    main()
