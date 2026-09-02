#!/usr/bin/env python3
"""gen_pre_vectors.py OUT_DIR
Writes ziskemu-framed ([8-byte LE length][blob][zero pad to 8]) unit-test
inputs for the precompile libraries:
  blake2f.in : 213-byte records (EIP-152 vectors 4-7 + random rounds<=64)
  modexp.in  : records [4B BE blen][4B elen][4B mlen][base][exp][mod]
Oracles: guest/test/exp_blake2f.py, guest/test/exp_modexp.py."""
import os, random, struct, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pyref

BODY = ("48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b"
        "6bbd41fbabd9831f79217e1319cde05b616263" + "00" * 125 + "03" + "00" * 15)
EIP152 = [  # (rounds, f, expected)
    (0, 1, "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b"),
    (12, 1, "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"),
    (12, 0, "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d2875298743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735"),
    (1, 1, "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fba551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421"),
]


def frame(blob):
    return struct.pack("<Q", len(blob)) + blob + b"\0" * (-len(blob) % 8)


def blake2f_blob(rng):
    recs = []
    for rounds, f, exp in EIP152:
        rec = struct.pack(">I", rounds) + bytes.fromhex(BODY) + bytes([f])
        assert len(rec) == 213 and pyref.blake2f(rec).hex() == exp, "pyref blake2f mismatch"
        recs.append(rec)
    for _ in range(12):
        recs.append(struct.pack(">I", rng.randrange(65)) + rng.randbytes(208) + bytes([rng.randrange(2)]))
    return b"".join(recs)


def modexp_blob(rng):
    def rec(b, e, m):
        return struct.pack(">III", len(b), len(e), len(m)) + b + e + m
    rb = lambda n: rng.randbytes(n)
    ib = lambda v, n: v.to_bytes(n, "big")
    cases = [
        rec(b"", b"", b""),                          # all empty
        rec(b"\x03", b"\x02", b""),                  # m length 0
        rec(b"\x03", b"\x02", b"\x00\x00"),          # m = 0 -> zeros
        rec(b"\x03", b"\x02", b"\x01"),              # m = 1 -> 0
        rec(b"\x03", b"\x00", ib(7, 4)),             # exp 0 -> 1
        rec(b"", b"\x00", ib(1, 3)),                 # exp 0, m = 1 -> 0
        rec(b"", b"", ib(5, 1)),                     # base 0 exp 0 -> 1
        rec(ib(0, 3), b"\x05", ib(5, 1)),            # 0^5 mod 5 = 0
        rec(ib(12345, 4), ib(3, 1), ib(10, 1)),      # base > mod
        rec(ib(2, 1), ib(10, 1), ib(1024, 2)),       # even modulus, power of two
        rec(ib(3, 1), ib(0xffff, 2), ib(0xfffffffe, 4)),  # even modulus
        rec(rb(32), rb(32), ib(2**255 + 1, 32)),     # 256-bit
        rec(rb(64), rb(32), rb(64)),                 # 512-bit
        rec(rb(5), rb(1), b"\x00\x00" + rb(4)),      # leading zero modulus bytes
        rec(rb(300), rb(2), rb(200)),                # base longer than mod
        rec(rb(31), rb(33), rb(31)),                 # 33-byte exponent
        rec(rb(1024), rb(3), rb(1024)),              # max lengths, tiny exponent
        rec(rb(1024), rb(1), b"\x01" + b"\x00" * 1023),  # mod = 2^8184
        rec(rb(1), rb(1024), b"\xff" + rb(7)),       # 1024-byte exponent, small mod
        rec(rb(200), b"\x00" * 100, rb(200)),        # long zero exponent
    ]
    for _ in range(20):
        nb, ne, nm = rng.randrange(0, 70), rng.randrange(0, 40), rng.randrange(1, 70)
        cases.append(rec(rb(nb), rb(ne), rb(nm)))
    cases.append(rec(rb(512), rb(32), rb(512)))      # heavy: 4096-bit, 256-bit exponent
    return b"".join(cases)


if __name__ == "__main__":
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    rng = random.Random(7)
    open(os.path.join(out, "blake2f.in"), "wb").write(frame(blake2f_blob(rng)))
    open(os.path.join(out, "modexp.in"), "wb").write(frame(modexp_blob(rng)))
    print("wrote", out)
