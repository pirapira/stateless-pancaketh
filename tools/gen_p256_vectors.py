#!/usr/bin/env python3
"""gen_p256_vectors.py [--count N] [--seed S] OUT_INPUT OUT_EXPECTED
Test vectors for guest/test/t_p256.pnk (secp256r1 / NIST P-256 ECDSA
verification, lib/p256.pnk, the P256VERIFY precompile of EIP-7951).

Oracle: a from-scratch pure-Python port of the checks in
evm-asm/execution-specs/src/ethereum/forks/amsterdam/vm/precompiled_contracts/p256verify.py
(`0 < r,s < n`, `qx,qy < p`, `(qx,qy) != (0,0)`, `is_on_curve_secp256r1`) and
textbook ECDSA verification (`secp256r1_verify` delegates to `cryptography`):
u1 = e s^-1, u2 = r s^-1 (mod n), R = u1 G + u2 Q, R != O, R.x mod n == r.
Plain `int` + `pow`, affine chord/tangent formulas.  When `cryptography` is
importable (an execution-specs dependency) every case that passes the range
and curve checks is cross-checked against `EllipticCurvePublicKey.verify`
(Prehashed SHA-256), i.e. against the very library the Python spec calls; a
mismatch aborts.  Run under `uv run --directory evm-asm/execution-specs python
...` to get the cross-check (tools/check_p256.sh does).

Input (ziskemu framing: 8-byte LE length, blob, zero pad to 8): N cases of
160 bytes, exactly the precompile call data [32 hash][32 r][32 s][32 qx][32 qy]
(big-endian).  Expected output per case: 8 bytes LE, 1 if the signature
verifies else 0 (the precompile then returns 32 bytes ending in 0x01, or empty
output)."""
import argparse, hashlib, os, random, struct, sys

# ---- curve parameters (FIPS 186-4 D.1.2.3; ethereum/crypto/elliptic_curve.py) ----
P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
A = P - 3
B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
G = (GX, GY)


def curve_add(x1, y1, x2, y2):
    lam = (y2 - y1) * pow(x2 - x1, P - 2, P) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def curve_dbl(x1, y1):
    lam = (3 * x1 * x1 + A) * pow(2 * y1, P - 2, P) % P
    x3 = (lam * lam - 2 * x1) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def point_add(p1, p2):
    """Group law on Option Point (None = identity)."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2:
        if (y1 + y2) % P == 0:
            return None
        return curve_dbl(x1, y1)
    return curve_add(x1, y1, x2, y2)


def scalar_mul(k, pt):
    acc = None
    while k > 0:
        if k & 1:
            acc = point_add(acc, pt)
        pt = point_add(pt, pt)
        k >>= 1
    return acc


def is_on_curve(x, y):
    """ethereum.crypto.elliptic_curve.is_on_curve_secp256r1."""
    return (y * y) % P == (x * x * x + A * x + B) % P


def verify(hash32, r, s, qx, qy):
    """p256verify.py after the length check: True iff the output is 1."""
    if r <= 0 or r >= N:
        return False
    if s <= 0 or s >= N:
        return False
    if qx >= P or qy >= P:
        return False
    if qx == 0 and qy == 0:
        return False
    if not is_on_curve(qx, qy):
        return False
    e = int.from_bytes(hash32, "big")
    sinv = pow(s, N - 2, N)
    u1 = e * sinv % N
    u2 = r * sinv % N
    R = point_add(scalar_mul(u1, G), scalar_mul(u2, (qx, qy)))
    if R is None:
        return False
    return R[0] % N == r


def sign(d, e, k):
    """Textbook ECDSA with explicit nonce; None if r or s == 0."""
    R = scalar_mul(k, G)
    if R is None:
        return None
    r = R[0] % N
    s = pow(k, N - 2, N) * (e + r * d) % N
    if r == 0 or s == 0:
        return None
    return r, s


def pubkey(d):
    return scalar_mul(d, G)


# ---- optional cross-check against `cryptography` (what the Python spec uses) ----
try:
    from cryptography.hazmat.primitives import hashes  # type: ignore
    from cryptography.hazmat.primitives.asymmetric import ec  # type: ignore
    from cryptography.hazmat.primitives.asymmetric.utils import Prehashed, encode_dss_signature  # type: ignore
    from cryptography.exceptions import InvalidSignature  # type: ignore
    HAVE_CRYPTO = True
except Exception:  # pragma: no cover
    HAVE_CRYPTO = False


def cross_check(hash32, r, s, qx, qy, result):
    if not HAVE_CRYPTO:
        return
    if not (0 < r < N and 0 < s < N and qx < P and qy < P and is_on_curve(qx, qy)):
        return  # rejected by the spec before the library is consulted
    pub = ec.EllipticCurvePublicNumbers(qx, qy, ec.SECP256R1()).public_key()
    try:
        pub.verify(encode_dss_signature(r, s), hash32, ec.ECDSA(Prehashed(hashes.SHA256())))
        got = True
    except InvalidSignature:
        got = False
    if got != result:
        sys.exit(f"cryptography disagrees: hash={hash32.hex()} r={r:#x} s={s:#x} "
                 f"qx={qx:#x} qy={qy:#x} ours={result} lib={got}")


def _h(x):
    return x.to_bytes(32, "big")


def fixed_cases():
    """KATs and edge cases: (hash32, r, s, qx, qy, want) with want in {True, False, None}."""
    cases = []
    # EIP-7951 reference vector (Wycheproof ecdsa_secp256r1_sha256_p1363 tc 1 style, from the EIP).
    cases.append((bytes.fromhex("bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023"),
                  0x2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18,
                  0x4cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd76,
                  0x2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838,
                  0xc7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e, True))
    # Test key: d = 12345 (deterministic), a few signatures with fixed nonces.
    d = 12345
    qx, qy = pubkey(d)
    h1 = hashlib.sha256(b"p256 pancake").digest()
    e1 = int.from_bytes(h1, "big")
    r, s = sign(d, e1, 0x1F00D)
    cases.append((h1, r, s, qx, qy, True))                 # valid
    cases.append((h1, r, N - s, qx, qy, True))             # s -> n - s is also valid (malleable)
    cases.append((h1, r, s, qx, P - qy, False))            # negated public key
    cases.append((h1, s, r, qx, qy, False))                # swapped r, s
    cases.append((_h(e1 ^ 1), r, s, qx, qy, False))        # different hash
    cases.append((h1, r + 1, s, qx, qy, False))            # r off by one
    # r / s range gates
    cases.append((h1, 0, s, qx, qy, False))
    cases.append((h1, N, s, qx, qy, False))
    cases.append((h1, N + 1, s, qx, qy, False))
    cases.append((h1, 2**256 - 1, s, qx, qy, False))
    cases.append((h1, r, 0, qx, qy, False))
    cases.append((h1, r, N, qx, qy, False))
    cases.append((h1, r, N + r if N + r < 2**256 else N + 2, qx, qy, False))
    cases.append((h1, r, 2**256 - 1, qx, qy, False))
    # public key gates: coordinates >= p (including qx + p, which is "the same" residue)
    cases.append((h1, r, s, qx + P if qx + P < 2**256 else P, qy, False))
    cases.append((h1, r, s, qx, qy + P if qy + P < 2**256 else P, False))
    cases.append((h1, r, s, P, qy, False))
    cases.append((h1, r, s, qx, P, False))
    cases.append((h1, r, s, 2**256 - 1, qy, False))
    cases.append((h1, r, s, qx, 2**256 - 1, False))
    # point at infinity encoding and points off the curve
    cases.append((h1, r, s, 0, 0, False))
    cases.append((h1, r, s, qx, 0, False))
    cases.append((h1, r, s, 0, qy, False))
    cases.append((h1, r, s, qx, (qy + 1) % P, False))
    cases.append((h1, r, s, GX, GY + 1, False))
    cases.append((h1, r, s, 1, 1, False))
    # hash = 0 (u1 = 0: R = u2 Q), and hash >= n (e reduced mod n implicitly)
    r0, s0 = sign(d, 0, 0xABCDEF)
    cases.append((_h(0), r0, s0, qx, qy, True))
    ebig = N + 987654321
    rb, sb = sign(d, ebig % N, 0x5EED)
    cases.append((_h(ebig), rb, sb, qx, qy, True))
    cases.append((_h(2**256 - 1), rb, sb, qx, qy, False))
    rmax, smax = sign(d, (2**256 - 1) % N, 0x7777)
    cases.append((_h(2**256 - 1), rmax, smax, qx, qy, True))
    cases.append((_h(N), rmax, smax, qx, qy, False))
    r_n, s_n = sign(d, 0, 0x424242)                        # e = n reduces to 0
    cases.append((_h(N), r_n, s_n, qx, qy, True))
    # generator as public key (d = 1), tiny d, and d = n - 1 (Q = -G)
    for dd in (1, 2, 3, N - 1, N - 2):
        px, py = pubkey(dd)
        hh = hashlib.sha256(bytes([dd & 255])).digest()
        rr, ss = sign(dd, int.from_bytes(hh, "big"), 0x1234567 + dd % 1000)
        cases.append((hh, rr, ss, px, py, True))
        cases.append((hh, rr, ss, px, P - py, False))
    # r = 1 and s = 1 with a public key chosen to make them verify:
    # pick k = 1 (R = G, r = GX mod n); then Q = (s k - e) r^-1 G.
    e = int.from_bytes(h1, "big")
    rG = GX % N
    for s_small in (1, 2, N - 1):
        dq = (s_small * 1 - e) * pow(rG, N - 2, N) % N
        px, py = pubkey(dq)
        cases.append((h1, rG, s_small, px, py, True))
    # x = r + n (R.x >= n) has probability ~2^-32 per signature and is not reachable
    # by construction here; the branch is covered negatively: r + n fails the range gate.
    cases.append((h1, min(rG + N, 2**256 - 1), 1, *pubkey((1 - e) * pow(rG, N - 2, N) % N), False))
    return cases


def gen_random(rng, count):
    cases = []
    i = 0
    while len(cases) < count:
        i += 1
        d = rng.randrange(1, N)
        qx, qy = pubkey(d)
        msg = rng.getrandbits(256).to_bytes(32, "big")
        kind = i % 10
        if kind == 8:
            msg = bytes(32)
        if kind == 9:
            msg = (N + rng.randrange(1, 2**256 - N)).to_bytes(32, "big")
        e = int.from_bytes(msg, "big") % N
        while True:
            k = rng.randrange(1, N)
            sig = sign(d, e, k)
            if sig:
                break
        r, s = sig
        want = True
        if kind == 3:
            s = N - s                      # still valid
        if kind == 4:
            r = rng.randrange(1, N); want = False
        if kind == 5:
            s = rng.randrange(1, N); want = False
        if kind == 6:
            qy = P - qy; want = False      # -Q
        if kind == 7:
            msg = rng.getrandbits(256).to_bytes(32, "big"); want = None
        cases.append((msg, r, s, qx, qy, want))
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("out_input")
    ap.add_argument("out_expected")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    cases = fixed_cases()
    if args.count > len(cases):
        cases += gen_random(rng, args.count - len(cases))
    cases = cases[:args.count]
    blob = b""
    exp = b""
    nok = 0
    for hash32, r, s, qx, qy, want in cases:
        res = verify(hash32, r, s, qx, qy)
        if want is not None and res != want:
            sys.exit(f"KAT mismatch: hash={hash32.hex()} r={r:#x} s={s:#x} qx={qx:#x} qy={qy:#x}: "
                     f"got {res}, want {want}")
        cross_check(hash32, r, s, qx, qy, res)
        blob += hash32 + r.to_bytes(32, "big") + s.to_bytes(32, "big") + qx.to_bytes(32, "big") + qy.to_bytes(32, "big")
        exp += struct.pack("<Q", 1 if res else 0)
        nok += res
    pad = (-(8 + len(blob))) % 8
    with open(args.out_input, "wb") as f:
        f.write(struct.pack("<Q", len(blob)) + blob + b"\x00" * pad)
    with open(args.out_expected, "wb") as f:
        f.write(exp)
    print(f"{len(cases)} cases ({nok} valid signatures), input {len(blob)} bytes, "
          f"expected {len(exp)} bytes, cryptography cross-check: {'yes' if HAVE_CRYPTO else 'NO'}")


if __name__ == "__main__":
    main()
