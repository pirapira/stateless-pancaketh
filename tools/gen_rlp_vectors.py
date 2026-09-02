#!/usr/bin/env python3
"""gen_rlp_vectors.py OUT_DIR
Writes OUT_DIR/rlp.input (ziskemu framing: u64 LE len, blob, zero pad to 8)
containing a sequence of [u32 LE len][rlp bytes] items, and
OUT_DIR/rlp.expected: one 32-byte record per item as produced by
guest/test/t_rlp.pnk.

Record layout (all unused bytes 0):
  0      status: 0 = rlp_decode_fully ok, 1 = RlpErr
  1      kind (0 bytes / 1 list)
  2..5   payload_len u32 LE
  6..9   total_len u32 LE
  10..13 list item count u32 LE (lists)
  14..21 rlp_bytes_to_word u64 LE, or 8 x 0xFF if it threw (strings)
  22     1 iff rlp_encode_bytes(payload) == original (strings)
  23     1 iff rlp_encode_list_header(payload_len) == original header (lists)
  24     1 iff rlp_bytes_encoded_len / rlp_list_header_len + payload == total
  25     1 iff rlp_encode_word(word) == original and rlp_word_encoded_len ok
  26     rlp_check_uint_bytes(payload, 0) status (strings)
  27     rlp_check_uint_bytes(payload, 4) status (strings)
  28     1 iff rlp_list_to_slices agrees with count/lengths/rlp_item (lists)
  29     rlp_item (prefix decode, trailing allowed) status
The Python oracle mirrors EvmAsm/EL/RLP/Decode.lean and is cross-checked
against execution-specs' ethereum_rlp when importable (run under
`uv run --directory evm-asm/execution-specs python`)."""
import os, random, struct, sys

try:
    import ethereum_rlp
    from ethereum_rlp.exceptions import DecodingError
except ImportError:  # oracle still works, just without the cross-check
    ethereum_rlp = None


class Err(Exception):
    pass


# ---- reference encoder (Basic.lean encodeBytes / encode) -------------------

def be(n):
    out = b""
    while n:
        out = bytes([n & 255]) + out
        n >>= 8
    return out


def header(base, n):
    if n <= 55:
        return bytes([base + n])
    lb = be(n)
    return bytes([base + 55 + len(lb)]) + lb


def enc_bytes(b):
    if len(b) == 1 and b[0] < 0x80:
        return b
    return header(0x80, len(b)) + b


def enc(item):
    if isinstance(item, (bytes, bytearray)):
        return enc_bytes(bytes(item))
    payload = b"".join(enc(x) for x in item)
    return header(0xC0, len(payload)) + payload


# ---- reference strict decoder (Decode.lean decodeAux) ---------------------

def read_length(bs, n):
    if len(bs) < n:
        raise Err("truncated")
    if n > 1 and bs[0] == 0:
        raise Err("leading zero")
    return int.from_bytes(bs[:n], "big")


def item(bs):
    """-> (kind, payload_off, payload_len, total_len); raises Err."""
    if len(bs) == 0:
        raise Err("empty")
    b = bs[0]
    if b < 0x80:
        return (0, 0, 1, 1)
    if b <= 0xB7:
        n = b - 0x80
        if len(bs) - 1 < n:
            raise Err("truncated")
        if n == 1 and bs[1] < 0x80:
            raise Err("single byte")
        return (0, 1, n, 1 + n)
    if b <= 0xBF:
        ll = b - 0xB7
        n = read_length(bs[1:], ll)
        if n <= 55:
            raise Err("short form")
        if len(bs) - 1 - ll < n:
            raise Err("truncated")
        return (0, 1 + ll, n, 1 + ll + n)
    if b <= 0xF7:
        n = b - 0xC0
        if len(bs) - 1 < n:
            raise Err("truncated")
        list_count(bs[1:1 + n])
        return (1, 1, n, 1 + n)
    ll = b - 0xF7
    n = read_length(bs[1:], ll)
    if n <= 55:
        raise Err("short form")
    if len(bs) - 1 - ll < n:
        raise Err("truncated")
    list_count(bs[1 + ll:1 + ll + n])
    return (1, 1 + ll, n, 1 + ll + n)


def list_count(payload):
    off = 0
    count = 0
    while off < len(payload):
        it = item(payload[off:])
        off += it[3]
        count += 1
    return count


def record(bs):
    rec = bytearray(32)
    try:
        item(bs)
    except Err:
        rec[29] = 1
    try:
        kind, po, pl, tl = item(bs)
        if tl != len(bs):
            raise Err("trailing")
    except Err:
        rec[0] = 1
        return bytes(rec)
    rec[1] = kind
    rec[2:6] = struct.pack("<I", pl)
    rec[6:10] = struct.pack("<I", tl)
    payload = bs[po:po + pl]
    if kind == 0:
        if pl > 8 or (pl > 0 and payload[0] == 0):
            rec[14:22] = b"\xff" * 8
        else:
            w = int.from_bytes(payload, "big")
            rec[14:22] = struct.pack("<Q", w)
            # encode_word: 0 -> 0x80, <128 -> byte, else 0x80+len ++ be
            if w == 0:
                ew = b"\x80"
            elif w < 128:
                ew = bytes([w])
            else:
                ew = bytes([0x80 + len(be(w))]) + be(w)
            rec[25] = 1 if ew == bs else 0
        rec[22] = 1 if enc_bytes(payload) == bs else 0
        rec[24] = 1 if len(enc_bytes(payload)) == tl else 0
        rec[26] = 1 if (pl > 0 and payload[0] == 0) else 0
        rec[27] = 1 if (pl > 0 and payload[0] == 0) or pl > 4 else 0
    else:
        rec[10:14] = struct.pack("<I", list_count(payload))
        rec[23] = 1 if header(0xC0, pl) == bs[:po] else 0
        rec[24] = 1 if len(header(0xC0, pl)) + pl == tl else 0
        rec[28] = 1
    return bytes(rec)


def cross_check(bs, rec):
    if ethereum_rlp is None:
        return
    try:
        ethereum_rlp.decode(bs)
        ok = True
    except DecodingError:
        ok = False
    except RecursionError:
        return
    assert ok == (rec[0] == 0), (bs[:16].hex(), len(bs), ok, rec[0])


def vectors():
    rnd = random.Random(12345)
    v = []
    # basic valid
    v += [b"\x80", b"\xc0", b"\x00", b"\x7f", b"\x81\x80", b"\x81\xff"]
    v += [enc_bytes(b"dog"), enc_bytes(b"\x00\x01"), enc_bytes(b"\x01\x00")]
    v += [enc_bytes(bytes(range(1, 56))), enc_bytes(bytes(range(1, 57)))]
    v += [enc_bytes(bytes(255 - (i & 255) for i in range(256)))]
    v += [enc_bytes(bytes((i * 7) & 255 for i in range(300)))]
    v += [enc_bytes(bytes((i * 13 + 1) & 255 for i in range(65536)))]
    v += [enc_bytes(bytes((i * 3 + 5) & 255 for i in range(70000)))]
    # words
    for w in [1, 127, 128, 255, 256, 65535, 2**32, 2**56 - 1, 2**63, 2**64 - 1]:
        v.append(enc_bytes(be(w)))
    v += [enc_bytes(be(2**64)), enc_bytes(b"\x00" * 8), enc_bytes(b"\x00\x01"),
          enc_bytes(b"\x01\x02\x03\x04"), enc_bytes(b"\x01\x02\x03\x04\x05")]
    # invalid strings
    v += [b"\x81\x05", b"\x81\x7f", b"\x81\x00", b"\x81",
          b"\xb8\x37" + bytes(55), b"\xb8\x00", b"\xb9\x00\x38" + bytes(56),
          b"\xb9\x00\x00" + bytes(56),
          b"\x83\x01\x02", b"\xb8\x38" + bytes(10), b"\xb8", b"\xb9\x01",
          b"", b"\xbf" + b"\xff" * 8, b"\xbf" + b"\x80" + b"\x00" * 7,
          b"\xbf\x01" + b"\x00" * 7 + bytes(64),
          b"\xbe\x01" + b"\x00" * 6 + bytes(64)]
    # trailing garbage
    v += [b"\x80\x00", b"\xc0\x00", b"\x01\x02", enc_bytes(b"dog") + b"\x00",
          enc([b"a"]) + b"\xc0"]
    # lists
    v += [enc([b"\x01", b"\x02", b"\x03"]), enc([[]]), enc([[[]]]),
          enc([b"abc", [b"de", []]]), enc([b"", b"", b""]),
          enc([bytes(range(1, 30)), bytes(range(1, 30))]),   # payload 60
          enc([b"x" * 200, b"y" * 100]),                      # payload > 256
          enc([bytes(60) for _ in range(1200)]),              # payload > 65536
          enc([[b"\x01"] * 20] * 3)]
    deep = []
    for _ in range(100):
        deep = [deep]
    v.append(enc(deep))
    deep = b"\x01"
    for _ in range(60):
        deep = [deep, b"\x02"]
    v.append(enc(deep))
    # invalid lists
    v += [b"\xc2\x81\x05", b"\xc2\x82\x01", b"\xc3\x01\x02", b"\xf8\x03\x01\x02\x03",
          b"\xf9\x00\x38" + bytes(56), b"\xf8\x38" + bytes(10), b"\xf8",
          b"\xc1\xc1", b"\xc4\xc2\x01\x02\xc1",
          b"\xf8\x38" + b"\x00" * 55 + b"\x81\x05" + b"\x00",
          enc([b"x" * 60])[:-1], enc([b"x" * 60]) + b"\x00",
          b"\xff" + b"\xff" * 8, b"\xff" + b"\x00" + b"\x01" * 7 + bytes(100)]
    # random structures (cross-checked with ethereum_rlp.encode)
    def rand_item(depth):
        if depth == 0 or rnd.random() < 0.5:
            n = rnd.choice([0, 1, 1, 2, 5, 30, 56, 100])
            return bytes(rnd.randrange(256) for _ in range(n))
        return [rand_item(depth - 1) for _ in range(rnd.randrange(6))]
    for _ in range(30):
        it = rand_item(4)
        e = enc(it)
        if ethereum_rlp is not None:
            assert ethereum_rlp.encode(it) == e
        v.append(e)
    # random mutations of valid encodings
    for _ in range(30):
        e = bytearray(rnd.choice(v[:60]))
        if not e:
            continue
        i = rnd.randrange(len(e))
        e[i] = rnd.randrange(256)
        v.append(bytes(e[:rnd.randrange(1, len(e) + 1)]))
    return v


def main():
    out_dir = sys.argv[1]
    os.makedirs(out_dir, exist_ok=True)
    blob = b""
    expected = b""
    n_ok = n_err = 0
    for bs in vectors():
        rec = record(bs)
        cross_check(bs, rec)
        blob += struct.pack("<I", len(bs)) + bs
        expected += rec
        if rec[0] == 0:
            n_ok += 1
        else:
            n_err += 1
    pad = (-(8 + len(blob))) % 8
    with open(os.path.join(out_dir, "rlp.input"), "wb") as f:
        f.write(struct.pack("<Q", len(blob)) + blob + b"\x00" * pad)
    with open(os.path.join(out_dir, "rlp.expected"), "wb") as f:
        f.write(expected)
    print(f"{n_ok + n_err} items ({n_ok} valid, {n_err} invalid), "
          f"blob {len(blob)} bytes, ethereum_rlp cross-check "
          f"{'on' if ethereum_rlp else 'OFF'}")


if __name__ == "__main__":
    main()
