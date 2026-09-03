#!/usr/bin/env python3
"""Generate vectors for guest/test/t_bls12381.pnk.

The guest test uses the same 8-byte type/length framing as the other curve
tests.  Point encodings follow EIP-2537: coordinates occupy 64-byte
big-endian field elements (G2 is c0 || c1 for each coordinate).  The oracle
uses py_ecc, the reference used by the Amsterdam execution specs.
"""
import argparse
import random
import struct

from py_ecc.bls.hash_to_curve import (
    clear_cofactor_G1,
    clear_cofactor_G2,
    map_to_curve_G1,
    map_to_curve_G2,
)
from py_ecc.optimized_bls12_381 import FQ, FQ2
from py_ecc.optimized_bls12_381 import optimized_curve as C
from py_ecc.optimized_bls12_381 import optimized_pairing as PR

P = C.field_modulus
R = C.curve_order
G1 = C.G1
G2 = C.G2


def be48(x):
    return int(x).to_bytes(48, "big")


def be64(x):
    return int(x).to_bytes(64, "big")


def be32(x):
    return int(x).to_bytes(32, "big")


def fq2_bytes(x):
    return be64(x.coeffs[0]) + be64(x.coeffs[1])


def g1_bytes(point):
    if C.is_inf(point):
        return bytes(128)
    x, y = C.normalize(point)
    return be64(x) + be64(y)


def g2_bytes(point):
    if C.is_inf(point):
        return bytes(256)
    x, y = C.normalize(point)
    return fq2_bytes(x) + fq2_bytes(y)


def frame(ty, payload):
    padded = payload + bytes((-len(payload)) % 8)
    return struct.pack("<QQ", ty, len(payload)) + padded


def read_point_g1(data, subgroup=False):
    if len(data) != 128:
        raise ValueError("G1 length")
    x = int.from_bytes(data[:64], "big")
    y = int.from_bytes(data[64:], "big")
    if x >= P or y >= P:
        raise ValueError("G1 field")
    z = 0 if x == 0 and y == 0 else 1
    point = (FQ(x), FQ(y), FQ(z))
    if not C.is_on_curve(point, C.b):
        raise ValueError("G1 curve")
    if subgroup and not C.is_inf(C.multiply(point, R)):
        raise ValueError("G1 subgroup")
    return point


def read_point_g2(data, subgroup=False):
    if len(data) != 256:
        raise ValueError("G2 length")
    x0 = int.from_bytes(data[:64], "big")
    x1 = int.from_bytes(data[64:128], "big")
    y0 = int.from_bytes(data[128:192], "big")
    y1 = int.from_bytes(data[192:], "big")
    if max(x0, x1, y0, y1) >= P:
        raise ValueError("G2 field")
    x = FQ2((x0, x1))
    y = FQ2((y0, y1))
    z = FQ2.zero() if x == FQ2.zero() and y == FQ2.zero() else FQ2.one()
    point = (x, y, z)
    if not C.is_on_curve(point, C.b2):
        raise ValueError("G2 curve")
    if subgroup and not C.is_inf(C.multiply(point, R)):
        raise ValueError("G2 subgroup")
    return point


def point_result(size, operation):
    try:
        return struct.pack("<Q", 0) + operation()
    except Exception:
        return struct.pack("<Q", 1) + bytes(size)


def eval_record(ty, payload):
    if ty == 1:  # Fp multiplication, 48-byte canonical values
        a = int.from_bytes(payload[:48], "big")
        b = int.from_bytes(payload[48:96], "big")
        return be48(a * b % P)
    if ty == 2:  # Fp2 multiplication, c0 || c1 for each operand
        a = FQ2((int.from_bytes(payload[:48], "big"), int.from_bytes(payload[48:96], "big")))
        b = FQ2((int.from_bytes(payload[96:144], "big"), int.from_bytes(payload[144:192], "big")))
        r = a * b
        return be48(r.coeffs[0]) + be48(r.coeffs[1])
    if ty == 3:  # G1 add
        return point_result(128, lambda: g1_bytes(C.add(read_point_g1(payload[:128]), read_point_g1(payload[128:]))))
    if ty == 4:  # G1 scalar multiplication
        return point_result(128, lambda: g1_bytes(C.multiply(
            read_point_g1(payload[:128]), int.from_bytes(payload[128:160], "big"))))
    if ty == 5:  # G1 MSM
        if len(payload) == 0 or len(payload) % 160:
            return struct.pack("<Q", 1) + bytes(128)
        def msm_g1():
            result = None
            for pos in range(0, len(payload), 160):
                p = read_point_g1(payload[pos:pos + 128], subgroup=True)
                q = C.multiply(p, int.from_bytes(payload[pos + 128:pos + 160], "big"))
                result = q if result is None else C.add(result, q)
            return g1_bytes(result)
        return point_result(128, msm_g1)
    if ty == 6:  # G2 add
        return point_result(256, lambda: g2_bytes(C.add(read_point_g2(payload[:256]), read_point_g2(payload[256:]))))
    if ty == 7:  # G2 scalar multiplication
        return point_result(256, lambda: g2_bytes(C.multiply(
            read_point_g2(payload[:256]), int.from_bytes(payload[256:288], "big"))))
    if ty == 8:  # G2 MSM
        if len(payload) == 0 or len(payload) % 288:
            return struct.pack("<Q", 1) + bytes(256)
        def msm_g2():
            result = None
            for pos in range(0, len(payload), 288):
                p = read_point_g2(payload[pos:pos + 256], subgroup=True)
                q = C.multiply(p, int.from_bytes(payload[pos + 256:pos + 288], "big"))
                result = q if result is None else C.add(result, q)
            return g2_bytes(result)
        return point_result(256, msm_g2)
    if ty == 9:  # map Fp to G1
        x = int.from_bytes(payload, "big")
        if len(payload) != 64 or x >= P:
            return struct.pack("<Q", 1) + bytes(128)
        return struct.pack("<Q", 0) + g1_bytes(clear_cofactor_G1(map_to_curve_G1(FQ(x))))
    if ty == 10:  # map Fp2 to G2
        if len(payload) != 128:
            return struct.pack("<Q", 1) + bytes(256)
        x0 = int.from_bytes(payload[:64], "big")
        x1 = int.from_bytes(payload[64:], "big")
        if max(x0, x1) >= P:
            return struct.pack("<Q", 1) + bytes(256)
        return struct.pack("<Q", 0) + g2_bytes(clear_cofactor_G2(map_to_curve_G2(FQ2((x0, x1)))))
    if ty == 11:  # pairing product check
        if len(payload) == 0 or len(payload) % 384:
            return struct.pack("<Q", 3)
        result = PR.FQ12.one()
        try:
            for pos in range(0, len(payload), 384):
                p = read_point_g1(payload[pos:pos + 128], subgroup=True)
                q = read_point_g2(payload[pos + 128:pos + 384], subgroup=True)
                result *= PR.pairing(q, p)
        except Exception:
            return struct.pack("<Q", 2)
        return struct.pack("<Q", 1 if result == PR.FQ12.one() else 0)
    raise ValueError(ty)


def expected(blob):
    out = bytearray()
    pos = 0
    while pos < len(blob):
        ty, length = struct.unpack("<QQ", blob[pos:pos + 16])
        payload = blob[pos + 16:pos + 16 + length]
        out += frame(ty, eval_record(ty, payload))
        pos += 16 + ((length + 7) & ~7)
    return bytes(out)


def make_cases(rng):
    g = g1_bytes(G1)
    q = g2_bytes(G2)
    g2 = g1_bytes(C.multiply(G1, 2))
    q2 = g2_bytes(C.multiply(G2, 2))
    ng = g1_bytes(C.neg(G1))

    recs = []
    for a, b in [(0, 5), (1, P - 1), (P - 1, P - 1),
                 (rng.randrange(P), rng.randrange(P))]:
        recs.append((1, be48(a) + be48(b)))
    f2_values = [((0, 0), (1, 0)), ((1, 2), (P - 3, 5)),
                 ((P - 1, P - 2), (P - 5, P - 7)),
                 ((rng.randrange(P), rng.randrange(P)),
                  (rng.randrange(P), rng.randrange(P)))]
    for (a0, a1), (b0, b1) in f2_values:
        recs.append((2, be48(a0) + be48(a1) + be48(b0) + be48(b1)))

    recs += [(3, g + g), (3, g + bytes(128)), (3, g + ng),
             (3, be64(1) + be64(3) + g)]
    for k in (0, 1, 2, R - 1):
        recs.append((4, g + be32(k)))
    recs.append((5, g + be32(3)))
    recs.append((5, g + be32(2) + g2 + be32(5)))

    recs += [(6, q + q), (6, q + bytes(256)), (6, q + g2_bytes(C.multiply(G2, 3)))]
    for k in (0, 1, 2):
        recs.append((7, q + be32(k)))
    recs.append((8, q + be32(3)))
    recs.append((8, q + be32(2) + q2 + be32(5)))

    for x in (0, 1, rng.randrange(P)):
        recs.append((9, be64(x)))
    for x in ((0, 0), (1, 0), (rng.randrange(P), rng.randrange(P))):
        recs.append((10, be64(x[0]) + be64(x[1])))

    recs += [(11, g + q),
             (11, g + q + ng + q),
             (11, g + q + g + q),
             (11, bytes(128) + q)]
    return recs


def pad8(data):
    return data + bytes((-len(data)) % 8)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--only", default="", help="comma-separated record types")
    ap.add_argument("out_input")
    ap.add_argument("out_expected")
    args = ap.parse_args()
    recs = make_cases(random.Random(args.seed))
    if args.only:
        wanted = {int(x) for x in args.only.split(",")}
        recs = [r for r in recs if r[0] in wanted]
    blob = b"".join(frame(ty, payload) for ty, payload in recs)
    with open(args.out_input, "wb") as f:
        f.write(struct.pack("<Q", len(blob)) + pad8(blob))
    with open(args.out_expected, "wb") as f:
        f.write(expected(blob))
    from collections import Counter
    print(f"{len(recs)} records {dict(sorted(Counter(t for t, _ in recs).items()))}, "
          f"input {len(blob)} bytes, expected {len(expected(blob))} bytes")


if __name__ == "__main__":
    main()
