#!/usr/bin/env python3
"""ssz-inputs.py -- generate SSZ StatelessInput blobs for the differential
check of Guest.InputDecode against the guest itself.

    tools/ssz-inputs.py OUTDIR [--fuzz]

Writes guest inputs in the ziskemu packing `[8B LE len][blob][pad]`, the same
form `tools/make-inputs.sh` produces, so `lake exe run-guest` and
`lake exe input-decode-check` both accept them. Without a fixture corpus this
is the only way to get inputs that actually decode.

Cases: a minimal well-formed StatelessInput; variants with non-empty extra
data, transactions, withdrawals, block access list, witness lists, public keys
and fork activations; the gas limit at 1, 200M and 2^64-1; single-byte
mutations; truncations. With --fuzz, also every SSZ offset field of two base
inputs set to each of eight boundary values -- the bytes a hand-written mirror
of the decoder is most likely to disagree on.
"""
import os
import random
import struct
import sys


def u32(x):
    return struct.pack('<I', x)


def u64(x):
    return struct.pack('<Q', x)


def container(fixed_parts, var_parts):
    """An SSZ container. `None` in fixed_parts is an offset placeholder, filled
    in order from var_parts."""
    fixed_len = sum(4 if part is None else len(part) for part in fixed_parts)
    out, offset, tail, index = b'', fixed_len, b'', 0
    for part in fixed_parts:
        if part is None:
            out += u32(offset)
            offset += len(var_parts[index])
            tail += var_parts[index]
            index += 1
        else:
            out += part
    assert index == len(var_parts), 'offset placeholders do not match var_parts'
    return out + tail


def var_list(elements):
    """List[variable, n]: the element offsets, then the elements."""
    elements = list(elements)
    if not elements:
        return b''
    offset, out = 4 * len(elements), b''
    for element in elements:
        out += u32(offset)
        offset += len(element)
    return out + b''.join(elements)


def payload(gas_limit=200_000_000, gas_used=0, number=0, timestamp=0, extra=b'',
            txs=(), withdrawals=b'', bal=b'', slot=0, blob_gas_used=0,
            excess_blob_gas=0):
    """SszExecutionPayload; the fixed part is PL_FIXED = 540 bytes, with the
    four variable offsets at PLO_EXTRA_OFF, PLO_TXS_OFF, PLO_WD_OFF and
    PLO_BAL_OFF (guest/src/types.h)."""
    fixed = [
        bytes(32),               # parent_hash
        bytes(20),               # fee_recipient
        bytes(32),               # state_root
        bytes(32),               # receipts_root
        bytes(256),              # logs_bloom
        bytes(32),               # prev_randao
        u64(number),
        u64(gas_limit),
        u64(gas_used),
        u64(timestamp),
        None,                    # extra_data offset (436)
        bytes(32),               # base_fee_per_gas
        bytes(32),               # block_hash
        None,                    # transactions offset (504)
        None,                    # withdrawals offset (508)
        u64(blob_gas_used),
        u64(excess_blob_gas),
        None,                    # block_access_list offset (528)
        u64(slot),
    ]
    return container(fixed, [extra, var_list(txs), withdrawals, bal])


def requests():
    return container([None] * 5, [b''] * 5)


def new_payload_request(pl, versioned_hashes=b'', reqs=None):
    return container([None, None, bytes(32), None],
                     [pl, versioned_hashes, requests() if reqs is None else reqs])


def witness(state=(), codes=(), headers=()):
    return container([None, None, None],
                     [var_list(state), var_list(codes), var_list(headers)])


def chain_config(chain_id=1, bn=None, ts=None):
    activation = container([None, None],
                           [b'' if bn is None else u64(bn),
                            b'' if ts is None else u64(ts)])
    return container([u64(chain_id), None], [container([None], [activation])])


def stateless_input(pl=None, wit=None, cc=None, pubkeys=b''):
    body = container([None] * 4,
                     [new_payload_request(pl if pl is not None else payload()),
                      wit if wit is not None else witness(),
                      cc if cc is not None else chain_config(),
                      pubkeys])
    return bytes([21, 1]) + body     # schema id, then the SSZ body


def pack(blob):
    return u64(len(blob)) + blob + bytes((-len(blob)) % 8)


def offset_positions(blob):
    """Byte positions of the u32 offset fields, by walking the layout."""
    positions, body = {}, 2
    for index in range(4):
        positions[f'si{index}'] = body + index * 4
    o_npr, o_wit, o_cc, _o_pk = (
        struct.unpack_from('<I', blob, body + index * 4)[0] for index in range(4))
    npr = body + o_npr
    for name, delta in (('npr_pl', 0), ('npr_vh', 4), ('npr_rq', 40)):
        positions[name] = npr + delta
    pl = npr + struct.unpack_from('<I', blob, npr)[0]
    for name, delta in (('pl_extra', 436), ('pl_txs', 504), ('pl_wd', 508),
                        ('pl_bal', 528), ('pl_gas_limit', 412)):
        positions[name] = pl + delta
    rq = npr + struct.unpack_from('<I', blob, npr + 40)[0]
    for index in range(5):
        positions[f'rq{index}'] = rq + index * 4
    wit = body + o_wit
    for index in range(3):
        positions[f'wit{index}'] = wit + index * 4
    cc = body + o_cc
    positions['cc_fork'] = cc + 8
    positions['fork_act'] = cc + 12
    positions['act0'] = cc + 16
    positions['act1'] = cc + 20
    return positions


def base_cases():
    cases = {
        'minimal': stateless_input(),
        'gas200m': stateless_input(payload(gas_limit=200_000_000)),
        'gas1': stateless_input(payload(gas_limit=1)),
        'gasmax': stateless_input(payload(gas_limit=2 ** 64 - 1)),
        'bal1k': stateless_input(payload(bal=bytes(range(256)) * 4)),
        'extra32': stateless_input(payload(extra=bytes(32))),
        'tx2': stateless_input(payload(txs=[bytes(10), bytes(20)])),
        'wd1': stateless_input(payload(withdrawals=bytes(44))),
        'wit3': stateless_input(wit=witness(state=[bytes(5), bytes(1024)],
                                            codes=[bytes(3)], headers=[bytes(7)])),
        'chain7': stateless_input(cc=chain_config(chain_id=7, bn=99, ts=1234)),
        'pk2': stateless_input(pubkeys=bytes(130)),
    }
    base = cases['minimal']
    rng = random.Random(20260909)
    for k in range(24):
        at, delta = rng.randrange(len(base)), rng.randrange(1, 256)
        mutated = bytearray(base)
        mutated[at] = (mutated[at] + delta) & 0xff
        cases[f'mut{k:02d}_at{at}'] = bytes(mutated)
    for k, n in enumerate([0, 1, 2, 3, 15, 16, 17, 60, len(base) // 2, len(base) - 1]):
        cases[f'trunc{k:02d}_{n}'] = base[:n]
    return cases


def fuzz_cases():
    """Every SSZ offset field of two base inputs, at eight boundary values.
    The 'lite' base keeps every list non-empty but small: the model is
    quadratic in the store count, so a large witness code does not finish."""
    bases = {
        'min': stateless_input(),
        'lite': stateless_input(
            pl=payload(gas_limit=123456789, gas_used=7, number=9, timestamp=11,
                       extra=bytes(12), txs=[bytes(3), bytes(70), bytes(1)],
                       withdrawals=bytes(88), bal=bytes(96), slot=5),
            wit=witness(state=[bytes(2), bytes(33)], codes=[bytes(1), bytes(40)],
                        headers=[bytes(64)]),
            cc=chain_config(chain_id=11155111, bn=1, ts=2),
            pubkeys=bytes(65 * 3)),
    }
    cases = {}
    for base_name, blob in bases.items():
        cases[f'{base_name}_base'] = blob
        n = len(blob)
        for field, at in sorted(offset_positions(blob).items()):
            current = struct.unpack_from('<I', blob, at)[0]
            for label, value in [('0', 0), ('m1', max(current - 1, 0)),
                                 ('p1', current + 1), ('p4', current + 4),
                                 ('len', n), ('lenp1', n + 1),
                                 ('big', 0xffffffff), ('half', n // 2)]:
                mutated = bytearray(blob)
                struct.pack_into('<I', mutated, at, value & 0xffffffff)
                cases[f'{base_name}_{field}_{label}'] = bytes(mutated)
    return cases


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if len(args) != 1:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    outdir = args[0]
    os.makedirs(outdir, exist_ok=True)
    cases = base_cases()
    if '--fuzz' in sys.argv[1:]:
        cases.update(fuzz_cases())
    for name, blob in cases.items():
        with open(os.path.join(outdir, name + '.bin'), 'wb') as handle:
            handle.write(pack(blob))
    print(f'wrote {len(cases)} inputs to {outdir}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
