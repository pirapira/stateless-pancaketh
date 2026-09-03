#!/usr/bin/env python3
"""Generate KZG point-evaluation vectors and an execution-specs oracle.

The canonical valid cases are taken from execution-specs' KZG vectors.  Every
case is passed through ``verify_kzg_proof`` in that checkout, including the
negative mutations, so this test does not duplicate the reference verdict.
"""
import argparse
import hashlib
import json
import os
import struct

from ethereum.crypto.kzg import BLS_MODULUS, verify_kzg_proof
from ethereum_types.bytes import Bytes32, Bytes48


INF_POINT = b"\xc0" + b"\0" * 47
VECTOR_FILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "..",
    "evm-asm",
    "execution-specs",
    "tests",
    "cancun",
    "eip4844_blobs",
    "point_evaluation_vectors",
    "go_kzg_4844_verify_kzg_proof.json",
)


def frame(ty, payload):
    return struct.pack("<QQ", ty, len(payload)) + payload + b"\0" * (-len(payload) % 8)


def versioned_hash(commitment):
    return b"\x01" + hashlib.sha256(commitment).digest()[1:]


def verify(data):
    if len(data) != 192:
        return False
    try:
        return bool(verify_kzg_proof(
            Bytes48(data[96:144]),
            Bytes32(data[32:64]),
            Bytes32(data[64:96]),
            Bytes48(data[144:192]),
        ))
    except Exception:
        return False


def point_evaluation_verdict(data):
    """Apply the precompile hash guard and the execution-specs proof check."""
    if len(data) != 192 or data[:32] != versioned_hash(data[96:144]):
        return False
    return verify(data)


def canonical_finite_case():
    with open(VECTOR_FILE, encoding="utf-8") as vf:
        vectors = json.load(vf)
    for item in vectors:
        if not item.get("output"):
            continue
        inp = item["input"]
        commitment = bytes.fromhex(inp["commitment"][2:])
        proof = bytes.fromhex(inp["proof"][2:])
        if commitment != INF_POINT and proof == INF_POINT:
            return (
                bytes.fromhex(inp["z"][2:]),
                bytes.fromhex(inp["y"][2:]),
                commitment,
                proof,
            )
    raise RuntimeError("no finite commitment/infinity proof in canonical KZG vectors")


def make_cases():
    zero = INF_POINT
    z = (2).to_bytes(32, "big")
    y = bytes(32)
    valid_zero = versioned_hash(zero) + z + y + zero + zero

    finite_z, finite_y, finite_commitment, finite_proof = canonical_finite_case()
    valid_finite = (versioned_hash(finite_commitment) + finite_z + finite_y
                    + finite_commitment + finite_proof)

    wrong_y = bytearray(valid_zero)
    wrong_y[95] = 1

    wrong_hash = bytearray(valid_zero)
    wrong_hash[0] ^= 1

    out_of_range_z = bytearray(valid_zero)
    out_of_range_z[32:64] = int(BLS_MODULUS).to_bytes(32, "big")

    invalid_commitment = bytes(48)
    invalid_point = versioned_hash(invalid_commitment) + z + y + invalid_commitment + zero

    return [
        (1, valid_zero),
        (2, valid_finite),
        (3, bytes(wrong_y)),
        (4, bytes(wrong_hash)),
        (5, bytes(out_of_range_z)),
        (6, invalid_point),
        (7, valid_zero[:-1]),
    ]


def expected(blob):
    out = bytearray()
    pos = 0
    while pos + 16 <= len(blob):
        ty, length = struct.unpack_from("<QQ", blob, pos)
        end = pos + 16 + ((length + 7) & ~7)
        if end > len(blob):
            break
        payload = blob[pos + 16:pos + 16 + length]
        err = 0 if point_evaluation_verdict(payload) else 1
        result = (bytes(30) + b"\x10\0" + int(BLS_MODULUS).to_bytes(32, "big")) if err == 0 else bytes(64)
        out += frame(ty, struct.pack("<Q", err) + result)
        pos = end
    return bytes(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out_input")
    ap.add_argument("out_expected")
    args = ap.parse_args()
    records = make_cases()
    blob = b"".join(frame(ty, payload) for ty, payload in records)
    os.makedirs(os.path.dirname(os.path.abspath(args.out_input)), exist_ok=True)
    with open(args.out_input, "wb") as f:
        f.write(struct.pack("<Q", len(blob)) + blob + b"\0" * (-len(blob) % 8))
    with open(args.out_expected, "wb") as f:
        f.write(expected(blob))
    print(f"wrote {args.out_input}: {len(records)} records, {len(blob)} bytes")
    for ty, payload in records:
        if len(payload) == 192:
            print(f"case {ty}: {'valid' if point_evaluation_verdict(payload) else 'invalid'}")
        else:
            print(f"case {ty}: invalid length {len(payload)}")


if __name__ == "__main__":
    main()
