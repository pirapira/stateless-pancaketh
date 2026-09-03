"""Oracle for t_recover.pnk.

StatelessInput carries one uncompressed SEC1 public key per payload
transaction.  The guest verifies each key by recovering it from the
transaction signature; once that equality is established, the sender
address is simply keccak256(public_key[1:])[12:].  This oracle therefore
does not duplicate secp256k1 arithmetic.  Malformed or missing keys model
the zeroed output used for a TxErr path.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "tools"))
import pyref


PUBKEY_SIZE = 65
PAYLOAD_FIXED = 540
PAYLOAD_TXS_OFFSET = 504
PAYLOAD_WITHDRAWALS_OFFSET = 508
NPR_FIXED = 44
SI_FIXED = 16


def u32(data, offset):
    end = offset + 4
    if offset < 0 or end > len(data):
        raise ValueError("truncated SSZ uint32")
    return int.from_bytes(data[offset:end], "little")


def checked_offsets(offsets, fixed, length):
    if any(offset < fixed or offset > length for offset in offsets):
        raise ValueError("invalid SSZ container offset")
    if offsets != sorted(offsets) or offsets[0] != fixed:
        raise ValueError("invalid SSZ container offset order")


def transaction_count(body, new_payload_offset, new_payload_end):
    npr = body[new_payload_offset:new_payload_end]
    if len(npr) < NPR_FIXED:
        raise ValueError("truncated NewPayloadRequest")
    payload_offset = u32(npr, 0)
    versioned_hashes_offset = u32(npr, 4)
    requests_offset = u32(npr, 40)
    checked_offsets(
        [payload_offset, versioned_hashes_offset, requests_offset],
        NPR_FIXED,
        len(npr),
    )
    payload = npr[payload_offset:versioned_hashes_offset]
    if len(payload) < PAYLOAD_FIXED:
        raise ValueError("truncated ExecutionPayload")
    txs_offset = u32(payload, PAYLOAD_TXS_OFFSET)
    withdrawals_offset = u32(payload, PAYLOAD_WITHDRAWALS_OFFSET)
    if not PAYLOAD_FIXED <= txs_offset <= withdrawals_offset <= len(payload):
        raise ValueError("invalid ExecutionPayload offsets")
    txs = payload[txs_offset:withdrawals_offset]
    if not txs:
        return 0
    first_offset = u32(txs, 0)
    if first_offset == 0 or first_offset % 4:
        raise ValueError("invalid transaction list offset")
    return first_offset // 4


def expected(blob):
    if len(blob) < 2 or blob[:2] != b"\x15\x01":
        raise ValueError("missing Amsterdam stateless-input schema id")
    body = blob[2:]
    if len(body) < SI_FIXED:
        raise ValueError("truncated StatelessInput")
    offsets = [u32(body, i * 4) for i in range(4)]
    checked_offsets(offsets, SI_FIXED, len(body))
    npr_offset, witness_offset, chain_config_offset, public_keys_offset = offsets
    count = transaction_count(body, npr_offset, witness_offset)
    public_keys = [
        body[i : i + PUBKEY_SIZE]
        for i in range(public_keys_offset, len(body), PUBKEY_SIZE)
    ]
    if len(body[public_keys_offset:]) % PUBKEY_SIZE:
        raise ValueError("public-key list is not a multiple of 65 bytes")

    output = bytearray()
    for i in range(count):
        if i >= len(public_keys) or len(public_keys[i]) != PUBKEY_SIZE:
            output.extend(b"\x00" * 20)
            continue
        public_key = public_keys[i]
        if public_key[0] != 4:
            output.extend(b"\x00" * 20)
            continue
        output.extend(pyref.keccak256(public_key[1:])[12:])
    return bytes(output)
