#!/usr/bin/env python3
"""gen_u256_vectors.py [--count N] [--seed S] OUT_INPUT OUT_EXPECTED
Test vectors for guest/test/t_u256.pnk.  The input (ziskemu framing: 8-byte LE
length, blob, zero pad to 8) holds N cases of a, b, m as 32-byte big-endian
words; the expected file holds, per case, NRES 32-byte big-endian results:
  0 add(a,b)   1 sub(a,b)   2 mul(a,b)   3 div(a,b)   4 mod(a,b)
  5 sdiv(a,b)  6 smod(a,b)  7 addmod(a,b,m)  8 mulmod(a,b,m)
  9 exp(a, b & 511)  10 shl(a, b & 511)  11 shr(a, b & 511)  12 sar(a, b & 511)
  13 signextend(b & 63, a)  14 byte(b & 63, a)
  15 flags: lt | gt<<1 | slt<<2 | sgt<<3 | eq<<4 | cmp<<5 | is_zero(a)<<7
            | fits_word(a)<<8 | add_carry<<9 | from_be(to_be_min(a))==a<<10
            | from_word(low(a))==a<<11 | is_zero(a-a)<<12 | neg(neg(a))==a<<13
  16 bit_length(a) | byte_length(a)<<16 | to_be_min_len(a)<<32
  17 a & b   18 a | ~b   19 (-a) ^ b   20 high 256 bits of a*b
  21 from_be(first min(m & 63, 32) bytes of a)
All EVM semantics (division by zero gives 0, SDIV/SMOD truncate toward zero)."""
import argparse, random, struct, sys

NRES = 22
M256 = (1 << 256) - 1
SIGN = 1 << 255


def to_signed(x):
    return x - (1 << 256) if x & SIGN else x


def sdiv(a, b):
    if b == 0:
        return 0
    sa, sb = to_signed(a), to_signed(b)
    q = abs(sa) // abs(sb)
    if (sa < 0) != (sb < 0):
        q = -q
    return q & M256


def smod(a, b):
    if b == 0:
        return 0
    sa, sb = to_signed(a), to_signed(b)
    r = abs(sa) % abs(sb)
    if sa < 0:
        r = -r
    return r & M256


def sar(a, n):
    if n >= 256:
        return M256 if a & SIGN else 0
    return (to_signed(a) >> n) & M256


def signextend(b, x):
    if b >= 31:
        return x
    t = 8 * b + 7
    if (x >> t) & 1:
        return x | (M256 ^ ((1 << (t + 1)) - 1))
    return x & ((1 << (t + 1)) - 1)


def byte(i, x):
    if i >= 32:
        return 0
    return (x >> (8 * (31 - i))) & 255


def bit_length(a):
    return a.bit_length()


def byte_length(a):
    return (a.bit_length() + 7) // 8


def results(a, b, m, a_bytes):
    sh = b & 511
    sa, sb = to_signed(a), to_signed(b)
    lt, gt, eq = int(a < b), int(a > b), int(a == b)
    cmp = 0 if a < b else (1 if a == b else 2)
    flags = (lt | (gt << 1) | (int(sa < sb) << 2) | (int(sa > sb) << 3) | (eq << 4)
             | (cmp << 5) | (int(a == 0) << 7) | (int(a < (1 << 64)) << 8)
             | (int(a + b > M256) << 9) | (1 << 10) | (int(a < (1 << 64)) << 11)
             | (1 << 12) | (1 << 13))
    fn = min(m & 63, 32)
    return [
        (a + b) & M256,
        (a - b) & M256,
        (a * b) & M256,
        a // b if b else 0,
        a % b if b else 0,
        sdiv(a, b),
        smod(a, b),
        (a + b) % m if m else 0,
        (a * b) % m if m else 0,
        pow(a, sh, 1 << 256),
        (a << sh) & M256 if sh < 256 else 0,
        a >> sh if sh < 256 else 0,
        sar(a, sh),
        signextend(b & 63, a),
        byte(b & 63, a),
        flags,
        bit_length(a) | (byte_length(a) << 16) | (byte_length(a) << 32),
        a & b,
        a | (b ^ M256),
        ((-a) & M256) ^ b,
        (a * b) >> 256,
        int.from_bytes(a_bytes[:fn], "big") if fn else 0,
    ]


EDGES = [0, 1, 2, 3, 7, 255, 256, (1 << 32) - 1, 1 << 32, (1 << 64) - 1, 1 << 64,
         (1 << 64) + 1, (1 << 128) - 1, 1 << 128, (1 << 128) + 1, (1 << 192) - 1,
         1 << 192, (1 << 255) - 1, 1 << 255, (1 << 255) + 1, M256, M256 - 1,
         M256 - 2, (1 << 256) - (1 << 64), (1 << 256) - (1 << 128), 1 << 191,
         (1 << 65) - 1, (1 << 127) - 1, (1 << 129) - 1]


def rand_val(rng):
    k = rng.random()
    if k < 0.35:
        return rng.choice(EDGES)
    bits = rng.choice([8, 32, 63, 64, 65, 96, 127, 128, 129, 191, 192, 200, 250, 255, 256])
    v = rng.getrandbits(bits)
    if rng.random() < 0.15:
        v = (-v) & M256
    return v


FIXED = [
    (1 << 255, M256, 0),            # MIN / -1
    (1 << 255, 1 << 255, M256),
    (M256, M256, M256),
    (M256, 1, 2),
    (0, 0, 0),
    (0, 5, 7),
    (5, 0, 7),
    (M256, M256, (1 << 128) + 3),
    ((1 << 64) - 1, (1 << 64) - 1, (1 << 64) - 1),
    ((1 << 64) - 1, (1 << 64) + 1, 1 << 64),
    (M256, M256, 1),
    (12345, 67890, 1 << 255),
    (1 << 255, 3, 1 << 200),
    (M256 - 5, 1 << 128, M256),
    ((1 << 256) - (1 << 128), (1 << 128) - 1, (1 << 128) - 1),
    (2, 255 + 256, 17),             # exp(2, 511 & 511) = 2^511 mod 2^256 = 0, shl by 511
    (3, 200, 1000003),
    ((1 << 64) + 1, (1 << 64) + 1, (1 << 64) + 1),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("out_input")
    ap.add_argument("out_expected")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    cases = list(FIXED)
    while len(cases) < args.count:
        a, b = rand_val(rng), rand_val(rng)
        m = rand_val(rng)
        if rng.random() < 0.3 and m:
            m = rng.getrandbits(rng.choice([1, 8, 63, 64, 65, 128, 200, 256])) | 1
        cases.append((a, b, m))
    cases = cases[:args.count]
    blob = b""
    exp = b""
    for a, b, m in cases:
        ab = a.to_bytes(32, "big")
        blob += ab + b.to_bytes(32, "big") + m.to_bytes(32, "big")
        for r in results(a, b, m, ab):
            exp += (r & M256).to_bytes(32, "big")
    pad = (-(8 + len(blob))) % 8
    with open(args.out_input, "wb") as f:
        f.write(struct.pack("<Q", len(blob)) + blob + b"\x00" * pad)
    with open(args.out_expected, "wb") as f:
        f.write(exp)
    print(f"{len(cases)} cases, input {len(blob)} bytes, expected {len(exp)} bytes")


if __name__ == "__main__":
    main()
