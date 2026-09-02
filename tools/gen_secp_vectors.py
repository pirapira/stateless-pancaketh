#!/usr/bin/env python3
"""gen_secp_vectors.py [--count N] [--seed S] OUT_INPUT OUT_EXPECTED
Test vectors for guest/test/t_secp256k1.pnk (secp256k1 ECDSA public-key
recovery, lib/secp256k1.pnk).

Oracle: a from-scratch pure-Python port of
evm-asm/EvmAsm/Stateless/SpecRef/Secp256k1Recover.lean (`recover`,
`decompressR`, `pointAdd`, `scalarMul`, `addressOfPoint`, `ecrecoverAddress`),
plain `int` + `pow`, affine chord/tangent formulas.  When `coincurve`
(libsecp256k1, an execution-specs dependency) is importable every successful
recovery is cross-checked against `PublicKey.from_signature_and_message`, and
every failure is confirmed to make coincurve raise; a mismatch aborts.  Run it
under `uv run --directory evm-asm/execution-specs python ...` to get the
cross-check (tools/check_secp256k1.sh does).

Input (ziskemu framing: 8-byte LE length, blob, zero pad to 8): N cases of
104 bytes = [32 msg_hash][32 r][32 s][8 recid LE].
Expected output per case, 112 bytes:
  [8 ok LE][64 point x||y BE, zeros if !ok]
  [8 ok2 LE][20 address, zeros if !ok2][12 zero pad]
where ok/point = secp256k1_recover(hash, r, s, recid) and ok2/address =
secp256k1_ecrecover(hash, v = recid + 27, r, s) (so recid 2/3 exercise the
v gate)."""
import argparse, hashlib, os, random, struct, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pyref import keccak256  # noqa: E402

# ---- curve parameters (SEC 2 §2.4.1; Secp256k1Recover.lean) ----
P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
B = 7
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (GX, GY)


def curve_add(x1, y1, x2, y2):
    """Accel.curveAdd: chord rule, x1 != x2."""
    lam = (y2 - y1) * pow(x2 - x1, P - 2, P) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def curve_dbl(x1, y1):
    """Accel.curveDbl: tangent rule (a = 0)."""
    lam = 3 * x1 * x1 * pow(2 * y1, P - 2, P) % P
    x3 = (lam * lam - 2 * x1) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def point_add(p1, p2):
    """Secp256k1.pointAdd on Option Point (None = identity)."""
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
    """Secp256k1.scalarMul: LSB-first double-and-add, fuel 256."""
    acc = None
    for _ in range(256):
        if k == 0:
            break
        if k % 2 == 1:
            acc = point_add(acc, pt)
        pt = point_add(pt, pt)
        k //= 2
    return acc


def sqrt_cand(a):
    return pow(a, (P + 1) // 4, P)


def decompress_r(r, recid):
    """Secp256k1.decompressR; returns (x, y) or an error string."""
    x = r + (N if (recid // 2) % 2 == 1 else 0)
    if x >= P:
        return "xOutOfRange"
    rhs = (x * x % P * x + B) % P
    y0 = sqrt_cand(rhs)
    if y0 * y0 % P != rhs:
        return "xNotSquare"
    y = y0 if y0 % 2 == recid % 2 else (P - y0) % P
    return (x, y)


def recover(e, r, s, recid):
    """Secp256k1.recover; returns (x, y) or an error string."""
    if r == 0 or r >= N:
        return "rOutOfRange"
    if s == 0 or s >= N:
        return "sOutOfRange"
    rpt = decompress_r(r, recid)
    if isinstance(rpt, str):
        return rpt
    rinv = pow(r, N - 2, N)
    u1 = (N - e % N) % N * rinv % N
    u2 = s % N * rinv % N
    q = point_add(scalar_mul(u1, G), scalar_mul(u2, rpt))
    if q is None:
        return "atInfinity"
    return q


def address_of_point(q):
    return keccak256(q[0].to_bytes(32, "big") + q[1].to_bytes(32, "big"))[12:]


def ecrecover_address(h, v, r, s):
    if v == 27 or v == 28:
        q = recover(h, r, s, v - 27)
        if isinstance(q, str):
            return None
        return address_of_point(q)
    return None


# ---- signing helper (textbook ECDSA with an explicit nonce) ----
def sign(d, e, k):
    """Returns (r, s, recid) or None if r or s is 0 (retry with another k)."""
    R = scalar_mul(k, G)
    if R is None:
        return None
    r = R[0] % N
    s = pow(k, N - 2, N) * (e + r * d) % N
    if r == 0 or s == 0:
        return None
    recid = (R[1] & 1) | (2 if R[0] >= N else 0)
    return r, s, recid


def pubkey(d):
    return scalar_mul(d, G)


# ---- optional cross-check against libsecp256k1 ----
try:
    import coincurve  # type: ignore
except Exception:  # pragma: no cover
    coincurve = None
try:
    from ethereum.crypto.elliptic_curve import secp256k1_recover as es_recover  # type: ignore
    from ethereum.crypto.hash import Hash32 as ESHash32  # type: ignore
    from ethereum_types.numeric import U256 as ESU256  # type: ignore
except Exception:  # pragma: no cover
    es_recover = None


def cross_check(hash32, r, s, recid, result):
    if coincurve is None:
        return
    if r >= N or s >= N or recid > 3:
        return  # coincurve's parser rejects these before any recovery logic
    sig = r.to_bytes(32, "big") + s.to_bytes(32, "big") + bytes([recid])
    try:
        pk = coincurve.PublicKey.from_signature_and_message(sig, hash32, hasher=None)
        got = pk.format(compressed=False)[1:]
    except Exception:
        got = None
    exp = None if isinstance(result, str) else result[0].to_bytes(32, "big") + result[1].to_bytes(32, "big")
    if got != exp:
        sys.exit(f"coincurve disagrees: recid={recid} r={r:#x} s={s:#x} hash={hash32.hex()} "
                 f"ours={result if isinstance(result, str) else exp.hex()} lib={got and got.hex()}")
    if es_recover is not None and recid <= 1 and not isinstance(result, str):
        got2 = bytes(es_recover(ESU256(r), ESU256(s), ESU256(recid), ESHash32(hash32)))
        if got2 != exp:
            sys.exit("execution-specs secp256k1_recover disagrees")


# ---- fixed vectors (Secp256k1Recover.lean KATs and Transactions.lean sanity) ----
def _h(x):
    return x.to_bytes(32, "big")


FIXED = [
    # recover_eest_valid_signature_1 (v = 28)
    (_h(0x18C547E4F7B0F325AD1E56F57E26C745B09A3E503D86E00E5255FF7F715D3D1C),
     0x73B1693892219D736CABA55BDB67216E485557EA6B6AF75F37096C9AA6A5A75F,
     0xEEB940B1D03B21E36B0E47E79769F095FE2AB855BD91E3A38756B7D75A9C4549, 1,
     (0x3A514176466FA815ED481FFAD09110A2D344F6C9B78C1D14AFC351C3A51BE33D,
      0x8072E77939DC03BA44790779B7A1025BAF3003F6732430E20CD9B76D953391B3),
     bytes.fromhex("a94f5374fce5edbc8e2a8697c15331677e6ebf0b")),
    # recover_real_backend_probe (priv = 1 -> G)
    (_h(0x8268970637E7EC5E5732A57C1516B9BC08E10C97C69B43573EE8FCB5DB289440),
     0x0F5D436BB1EE6278117F772990A5671A75E0A179467ED1D8C612FEC86BFE7FF8,
     0x3F447738ECD57BC8B22B54E23AFCF109DB1D86CA8D17F60AD45E98F4526E71AF, 0, G, None),
    # recover_independent_vector
    (_h(0x11231FE21C44D87DD72EE6456267066DF8226784CA912B1D3020C7348E851959),
     0xBB50E2D89A4ED70663D080659FE0AD4B9BC3E06C17A227433966CB59CEEE020D,
     0x5AA713217EAFF6BF62AFEA8B901AB3C6B77BC5FF1A466AF565A4D6250ED8C586, 0,
     (0xC03457AEBB04B5343EE14B08F89A57BD842A7F6F1D39EC63A8CACC95CDEEA779,
      0x9BCD9CA350448E320E418C2F44B64087CE652A86004586E9A2D6C9661E74DF60), None),
    # recover_at_infinity: recover 1 gx 1 0
    (_h(1), GX, 1, 0, "atInfinity", None),
    # Transactions.lean vTx1Signed (privkey 0x0101..01, chain id 1, v = 38 -> parity 1)
    (_h(0x65c3ae64d466f2a8ffeab9ea674e0275cd4428e6df077c3d786b5d7a5d8984db),
     0x1518619670d02fb8bf8f6f78b6b0885aae6820737cfdd8080a6d829e2f9cb327,
     0x6cb5e9483bb48d9ddc77f9ae18296e8df37e00a99d5ea4b927e2b54c41492eec, 1,
     (0x1b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f,
      0x70beaf8f588b541507fed6a642c5ab42dfdf8120a7f639de5122d47a69a8e8d1),
     bytes.fromhex("1a642f0e3c3af545e7acbd38b07251b3990914f1")),
    # decompress_gen_parity1 turned into a recovery: R = (gx, p - gy)
    (_h(2), GX, 3, 1, None, None),
    # decompress_gen_parity0 with e != s: R = G, Q = (s - e) r^-1 G
    (_h(5), GX, 7, 0, None, None),
    # decompress_non_residue: r = 5
    (_h(1), 5, 1, 0, "xNotSquare", None),
    # xOutOfRange via recid 2: r = n - 1 (x = 2n - 1 >= p), r = p - n (x = p)
    (_h(1), N - 1, 1, 2, "xOutOfRange", None),
    (_h(1), P - N, 1, 2, "xOutOfRange", None),
    (_h(1), P - N, 1, 3, "xOutOfRange", None),
    # recid 2 with x = p - 1 (in range; residue-ness decided by the oracle)
    (_h(1), P - N - 1, 1, 2, None, None),
    # gates: r
    (_h(1), 0, 1, 0, "rOutOfRange", None),
    (_h(1), N, 1, 0, "rOutOfRange", None),
    (_h(1), N + 1, 1, 1, "rOutOfRange", None),
    (_h(1), 2**256 - 1, 1, 0, "rOutOfRange", None),
    (_h(1), P - 1, 1, 2, "rOutOfRange", None),   # decompress_out_of_range KAT input, gated earlier by r >= n
    # gates: s
    (_h(1), GX, 0, 0, "sOutOfRange", None),
    (_h(1), GX, N, 0, "sOutOfRange", None),
    (_h(1), GX, 2**256 - 1, 1, "sOutOfRange", None),
    # tiny values everywhere
    (_h(0), 1, 1, 0, None, None),
    (_h(0), 1, 1, 1, None, None),
    (_h(0), 1, 1, 2, None, None),          # x = 1 + n < p (oracle decides)
    # e >= n (hash above the group order: exercises the e mod n reduction), r = 1
    (_h(N + 12345), 1, N - 1, 1, None, None),
    (_h(2**256 - 1), 2, 2, 0, None, None),
]


def gen_random(rng, count):
    cases = []
    i = 0
    while len(cases) < count:
        i += 1
        d = rng.randrange(1, N)
        msg = rng.getrandbits(256).to_bytes(32, "big")
        kind = i % 8
        if kind == 6:
            # e = 0 (u1 = 0: Q = u2 * R only)
            msg = bytes(32)
        if kind == 7:
            # e in [n, 2^256): reduction mod n is exercised
            msg = (N + rng.randrange(1, 2**256 - N)).to_bytes(32, "big")
        e = int.from_bytes(msg, "big")
        while True:
            k = rng.randrange(1, N)
            sig = sign(d, e % N, k)
            if sig:
                break
        r, s, recid = sig
        if kind == 3:
            s = N - s  # flip s: the recovered key is a different valid point
        if kind == 4:
            recid ^= 1  # flipped parity: valid but different point
        if kind == 5:
            recid |= 2  # x = r + n, almost surely >= p
        pk = pubkey(d) if kind in (0, 1, 2, 6, 7) else None
        cases.append((msg, r, s, recid, pk, None))
    # non-square x: smallest few r with r^3 + 7 a non-residue, recid 0
    r = 1
    found = 0
    while found < 2:
        rhs = (r * r * r + B) % P
        if pow(rhs, (P - 1) // 2, P) != 1:
            cases.append((_h(9), r, 3, found, "xNotSquare", None))
            found += 1
        r += 1
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=44)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("out_input")
    ap.add_argument("out_expected")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    cases = list(FIXED)
    if args.count > len(cases) + 2:
        cases += gen_random(rng, args.count - len(cases) - 2)
    cases = cases[:args.count]
    blob = b""
    exp = b""
    nok = 0
    for hash32, r, s, recid, want, want_addr in cases:
        e = int.from_bytes(hash32, "big")
        res = recover(e, r, s, recid)
        if want is not None and res != want:
            sys.exit(f"KAT mismatch: r={r:#x} recid={recid}: got {res}, want {want}")
        cross_check(hash32, r, s, recid, res)
        addr = ecrecover_address(e, recid + 27, r, s)
        if want_addr is not None and addr != want_addr:
            sys.exit(f"address KAT mismatch: {addr and addr.hex()} vs {want_addr.hex()}")
        blob += hash32 + r.to_bytes(32, "big") + s.to_bytes(32, "big") + struct.pack("<Q", recid)
        if isinstance(res, str):
            exp += struct.pack("<Q", 0) + bytes(64)
        else:
            nok += 1
            exp += struct.pack("<Q", 1) + res[0].to_bytes(32, "big") + res[1].to_bytes(32, "big")
        if addr is None:
            exp += struct.pack("<Q", 0) + bytes(32)
        else:
            exp += struct.pack("<Q", 1) + addr + bytes(12)
    pad = (-(8 + len(blob))) % 8
    with open(args.out_input, "wb") as f:
        f.write(struct.pack("<Q", len(blob)) + blob + b"\x00" * pad)
    with open(args.out_expected, "wb") as f:
        f.write(exp)
    print(f"{len(cases)} cases ({nok} successful recoveries), input {len(blob)} bytes, "
          f"expected {len(exp)} bytes, coincurve cross-check: {'yes' if coincurve else 'NO'}"
          f"{', execution-specs cross-check: yes' if es_recover else ''}")


if __name__ == "__main__":
    main()
