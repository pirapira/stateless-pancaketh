"""Oracle for guest/test/t_precompiles.pnk.

Input records are [idx:u8][gas:u64 LE][len:u32 LE][data]. Output records are
[status:u8][gas_used:u64 LE][out_len:u32 LE][out bytes].
"""
import hashlib
import os
import struct
import sys

TOOLS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools")
sys.path.insert(0, TOOLS)

import pyref  # noqa: E402
from gen_p256_vectors import verify as p256_verify  # noqa: E402
from gen_precompile_vectors import kzg_data  # noqa: E402
from gen_secp_vectors import ecrecover_address  # noqa: E402

E_OUT_OF_GAS = 4
E_INVALID_PARAMETER = 10
E_KZG_PROOF = 13


def read_padded(data, off, n):
    return data[off:off + n].ljust(n, b"\0")


def modexp_cost(blen, mlen, elen, head):
    maxlen = max(blen, mlen)
    words = (maxlen + 7) // 8
    complexity = 16 if maxlen <= 32 else 2 * words * words
    hbits = max(head.bit_length() - 1, 0)
    count = hbits if elen <= 32 else 16 * (elen - 32) + hbits
    return max(500, complexity * max(count, 1))


def run_modexp(gas, data):
    hdr = data[:96].ljust(96, b"\0")
    blen, elen, mlen = (int.from_bytes(hdr[32 * i:32 * (i + 1)], "big") for i in range(3))
    if blen > 1024 or elen > 1024 or mlen > 1024:
        return E_OUT_OF_GAS, 0, b""
    exp_start = 96 + blen
    head = int.from_bytes(read_padded(data, exp_start, min(32, elen)), "big")
    cost = modexp_cost(blen, mlen, elen, head)
    if gas < cost:
        return E_OUT_OF_GAS, 0, b""
    base = int.from_bytes(read_padded(data, 96, blen), "big")
    exponent = int.from_bytes(read_padded(data, exp_start, elen), "big")
    modulus = int.from_bytes(read_padded(data, exp_start + elen, mlen), "big")
    result = (pow(base, exponent, modulus) if modulus else 0).to_bytes(mlen, "big")
    return 0, cost, result


def run_one(idx, gas, data):
    if idx == 4:
        cost = 15 + 3 * ((len(data) + 31) // 32)
        return (E_OUT_OF_GAS, 0, b"") if gas < cost else (0, cost, data)

    if idx == 2:
        cost = 60 + 12 * ((len(data) + 31) // 32)
        return (E_OUT_OF_GAS, 0, b"") if gas < cost else (0, cost, hashlib.sha256(data).digest())

    if idx == 3:
        cost = 600 + 120 * ((len(data) + 31) // 32)
        digest = hashlib.new("ripemd160", data).digest()
        return (E_OUT_OF_GAS, 0, b"") if gas < cost else (0, cost, b"\0" * 12 + digest)

    if idx == 1:
        cost = 3000
        if gas < cost:
            return E_OUT_OF_GAS, 0, b""
        padded = data[:128].ljust(128, b"\0")
        h = int.from_bytes(padded[:32], "big")
        v = int.from_bytes(padded[32:64], "big")
        r = int.from_bytes(padded[64:96], "big")
        s = int.from_bytes(padded[96:128], "big")
        addr = ecrecover_address(h, v, r, s)
        return 0, cost, b"\0" * 12 + addr if addr else b""

    if idx == 9:
        if len(data) != 213:
            return E_INVALID_PARAMETER, 0, b""
        rounds = int.from_bytes(data[:4], "big")
        if gas < rounds:
            return E_OUT_OF_GAS, 0, b""
        if data[212] > 1:
            return E_INVALID_PARAMETER, rounds, b""
        return 0, rounds, pyref.blake2f(data)

    if idx == 5:
        return run_modexp(gas, data)

    if idx == 18:
        cost = 6900
        if gas < cost:
            return E_OUT_OF_GAS, 0, b""
        if len(data) != 160:
            return 0, cost, b""
        h = data[:32]
        r, s, qx, qy = (int.from_bytes(data[32 * i:32 * (i + 1)], "big") for i in range(1, 5))
        result = b"\0" * 31 + b"\1" if p256_verify(h, r, s, qx, qy) else b""
        return 0, cost, result

    if idx == 10:
        cost = 50000
        if len(data) != 192:
            return E_KZG_PROOF, 0, b""
        if gas < cost:
            return E_OUT_OF_GAS, 0, b""
        # gen_precompile_vectors.py keeps wrapper cases to the inexpensive
        # zero-polynomial proof; the standalone KZG test covers wrong-y's
        # full pairing path against execution-specs.
        if data == kzg_data():
            return 0, cost, bytes(30) + b"\x10\0" + bytes.fromhex(
                "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
            )
        return E_KZG_PROOF, cost, b""

    raise AssertionError(f"unsupported test index {idx}")


def expected(blob):
    out = bytearray()
    off = 0
    while off + 13 <= len(blob):
        idx = blob[off]
        gas = struct.unpack_from("<Q", blob, off + 1)[0]
        n = struct.unpack_from("<I", blob, off + 9)[0]
        data_start = off + 13
        data_end = data_start + n
        if data_end > len(blob):
            break
        status, used, result = run_one(idx, gas, blob[data_start:data_end])
        out += bytes([status]) + struct.pack("<Q", used) + struct.pack("<I", len(result)) + result
        off = data_end
    return bytes(out)
