#!/usr/bin/env python3
"""Generate framed records for guest/test/t_precompiles.pnk.

Each record is [idx:u8][gas:u64 LE][data_len:u32 LE][call data]. The whole
record blob is wrapped in the ziskemu input format used by input_blob().
"""
import argparse
import os
import struct
import sys

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)

from gen_p256_vectors import fixed_cases  # noqa: E402
from gen_pre_vectors import BODY, EIP152  # noqa: E402
from gen_secp_vectors import FIXED, ecrecover_address  # noqa: E402


def frame(blob):
    return struct.pack("<Q", len(blob)) + blob + b"\0" * (-len(blob) % 8)


def record(idx, gas, data):
    return struct.pack("<BQI", idx, gas, len(data)) + data


def blake2f_data(rounds, flag):
    data = struct.pack(">I", rounds) + bytes.fromhex(BODY) + bytes([flag])
    assert len(data) == 213
    return data


def modexp_data(base, exponent, modulus):
    header = b"".join(n.to_bytes(32, "big")
                       for n in (len(base), len(exponent), len(modulus)))
    return header + base + exponent + modulus


def modexp_header(blen, elen, mlen):
    return b"".join(n.to_bytes(32, "big") for n in (blen, elen, mlen))


def p256_data(case):
    h, r, s, qx, qy, _ = case
    return h + b"".join(x.to_bytes(32, "big") for x in (r, s, qx, qy))


def build_blob():
    recs = []

    # Identity: exact gas, multi-byte output, and out-of-gas.
    recs += [
        record(4, 100, b""),
        record(4, 100, b"hello precompile"),
        record(4, 14, b""),
    ]

    # SHA-256: empty input has the 60-gas base cost; also test a word and OOG.
    recs += [
        record(2, 60, b""),
        record(2, 100, b"abc"),
        record(2, 59, b""),
    ]

    # RIPEMD-160: 20-byte digest left-padded to the wrapper's 32-byte output.
    recs += [
        record(3, 720, b"abc"),
        record(3, 719, b"abc"),
    ]

    # ECRECOVER known KAT, invalid v, short zero-padded input, and OOG.
    h, r, s, recid, _, _ = FIXED[0]
    ecrecover_body = (h + (recid + 27).to_bytes(32, "big") +
                      r.to_bytes(32, "big") + s.to_bytes(32, "big"))
    assert ecrecover_address(int.from_bytes(h, "big"), recid + 27, r, s)
    invalid_v = h + (29).to_bytes(32, "big") + r.to_bytes(32, "big") + s.to_bytes(32, "big")
    recs += [
        record(1, 3000, ecrecover_body),
        record(1, 3000, invalid_v),
        record(1, 3000, b""),
        record(1, 2999, ecrecover_body),
    ]

    # EIP-152 vectors, bad length/flag, and out-of-gas after the rounds charge.
    for rounds, flag, _ in EIP152:
        recs.append(record(9, rounds, blake2f_data(rounds, flag)))
    recs += [
        record(9, 100, b""),
        record(9, 12, blake2f_data(12, 2)),
        record(9, 11, blake2f_data(12, 1)),
    ]

    # Modexp: empty modulus, a basic result, EIP-7883 complexity boundaries,
    # the exponent-length surcharge, and the 1024-byte length limit.
    basic = modexp_data(b"\x03", b"\x02", b"\x05")
    cplx = modexp_data(b"\x01", b"\x08\x00", b"\x01" * 33)
    long_exp = modexp_data(b"\x02", b"\0" * 31 + b"\x02\x00", b"\x01" * 33)
    recs += [
        record(5, 500, modexp_data(b"", b"", b"")),
        record(5, 500, basic),
        record(5, 499, basic),
        record(5, 549, cplx),
        record(5, 550, cplx),
        record(5, 849, long_exp),
        record(5, 850, long_exp),
        record(5, 0, modexp_header(1025, 0, 0)),
    ]

    # P256VERIFY: EIP vector, bad signature, wrong length, and OOG.
    cases = fixed_cases()
    valid = p256_data(cases[0])
    bad = p256_data((cases[0][0], cases[0][1] + 1, cases[0][2], cases[0][3], cases[0][4], False))
    recs += [
        record(18, 6900, valid),
        record(18, 6900, bad),
        record(18, 6900, valid[:-1]),
        record(18, 6899, valid),
    ]
    return b"".join(recs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out_input")
    args = ap.parse_args()
    blob = build_blob()
    os.makedirs(os.path.dirname(os.path.abspath(args.out_input)), exist_ok=True)
    with open(args.out_input, "wb") as f:
        f.write(frame(blob))
    print(f"wrote {args.out_input}: {len(blob)} bytes, {sum(1 for _ in iter_records(blob))} records")


def iter_records(blob):
    off = 0
    while off + 13 <= len(blob):
        n = struct.unpack_from("<I", blob, off + 9)[0]
        end = off + 13 + n
        if end > len(blob):
            break
        yield blob[off:end]
        off = end


if __name__ == "__main__":
    main()
