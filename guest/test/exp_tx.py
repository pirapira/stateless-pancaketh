"""exp_tx.py -- oracle for t_tx.pnk: a pure-Python port of the same subset of
execution-specs transactions.py (via Transactions.lean) applied to every
transaction of a fixture input. Per transaction the record is 15 LE words
plus a 32-byte hash (152 bytes):
  [type][nonce low][gas][to flag][data len][access count][blob count]
  [auth count][signing hash 32][recid][intrinsic regular][calldata floor]
  [re-encode == raw][chain_id some][chain_id value][validate code]
A transaction that fails decode_transaction gives type = 2^64-1 and zeros.
"""
import struct, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'tools'))
import pyref

SECP256K1N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
TX_BASE = 12000; TX_CREATE = 32000; TX_VALUE_COST = 4244; TRANSFER_LOG_COST = 1756
TX_DATA_TOKEN_STANDARD = 4; TX_DATA_TOKEN_FLOOR = 16
COLD_ACCOUNT_ACCESS = 3000; COLD_STORAGE_ACCESS = 3000; ACCOUNT_WRITE = 8000
CREATE_ACCESS = ACCOUNT_WRITE + COLD_STORAGE_ACCESS; CODE_INIT_PER_WORD = 2
REGULAR_PER_AUTH_BASE_COST = 101 * 16 + 3000 + 3000 + 200
ACCESS_LIST_ADDRESS_FLOOR_TOKENS = 80; ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS = 128
TX_MAX_GAS_LIMIT = 16777216; MAX_INIT_CODE_SIZE = 2 * 0x10000

class TxErr(Exception): pass

# ---- strict RLP (ethereum_rlp semantics) --------------------------------
def rlp_item(b, off, end):
    if off >= end: raise TxErr("empty")
    x = b[off]
    if x < 0x80: return (bytes([x]), off + 1)
    if x <= 0xB7:
        n = x - 0x80
        if end - off - 1 < n: raise TxErr("short")
        if n == 1 and b[off + 1] < 0x80: raise TxErr("noncanon single")
        return (bytes(b[off + 1:off + 1 + n]), off + 1 + n)
    if x <= 0xBF:
        ll = x - 0xB7
        if end - off - 1 < ll: raise TxErr("short")
        lb = b[off + 1:off + 1 + ll]
        if lb[0] == 0: raise TxErr("noncanon len")
        n = int.from_bytes(lb, 'big')
        if n <= 55: raise TxErr("noncanon len")
        if end - off - 1 - ll < n: raise TxErr("short")
        s = off + 1 + ll
        return (bytes(b[s:s + n]), s + n)
    if x <= 0xF7:
        n = x - 0xC0
        if end - off - 1 < n: raise TxErr("short")
        return (rlp_list(b, off + 1, off + 1 + n), off + 1 + n)
    ll = x - 0xF7
    if end - off - 1 < ll: raise TxErr("short")
    lb = b[off + 1:off + 1 + ll]
    if lb[0] == 0: raise TxErr("noncanon len")
    n = int.from_bytes(lb, 'big')
    if n <= 55: raise TxErr("noncanon len")
    if end - off - 1 - ll < n: raise TxErr("short")
    s = off + 1 + ll
    return (rlp_list(b, s, s + n), s + n)

def rlp_list(b, off, end):
    out = []
    while off < end:
        it, off = rlp_item(b, off, end)
        out.append(it)
    return out

def rlp_decode_fully(b):
    it, end = rlp_item(b, 0, len(b))
    if end != len(b): raise TxErr("trailing")
    return it

def enc_bytes(b):
    if len(b) == 1 and b[0] < 0x80: return bytes(b)
    return enc_len(len(b), 0x80) + bytes(b)

def enc_len(n, base):
    if n <= 55: return bytes([base + n])
    lb = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    return bytes([base + 55 + len(lb)]) + lb

def enc_list(items):
    p = b''.join(items)
    return enc_len(len(p), 0xC0) + p

def scalar(n):
    return enc_bytes(n.to_bytes((n.bit_length() + 7) // 8, 'big') if n else b'')

# ---- decodeItem* -------------------------------------------------------
def d_scalar(it, maxb):
    if isinstance(it, list): raise TxErr("invalid uint")
    if it and it[0] == 0: raise TxErr("non-canonical integer")
    if maxb is not None and len(it) > maxb: raise TxErr("integer out of range")
    return int.from_bytes(it, 'big')

def d_bytes(it):
    if isinstance(it, list): raise TxErr("invalid bytes")
    return it

def d_fixed(it, w):
    if isinstance(it, list) or len(it) != w: raise TxErr("invalid fixed bytes")
    return it

def d_to(it):
    if isinstance(it, list): raise TxErr("invalid to")
    if len(it) == 0: return None
    if len(it) != 20: raise TxErr("invalid to")
    return it

def d_access(it):
    if not (isinstance(it, list) and len(it) == 2 and isinstance(it[1], list)):
        raise TxErr("invalid access-list entry")
    return (d_fixed(it[0], 20), [d_fixed(s, 32) for s in it[1]])

def d_auth(it):
    if not (isinstance(it, list) and len(it) == 6): raise TxErr("invalid authorization")
    cid, addr, nonce, yp, r, s = it
    return dict(chain_id=d_scalar(cid, 32), address=d_fixed(addr, 20),
                nonce=d_scalar(nonce, 8), y_parity=d_scalar(yp, 1),
                r=d_scalar(r, 32), s=d_scalar(s, 32))

def d_list(it):
    if not isinstance(it, list): raise TxErr("expected list")
    return it

def decode_transaction(raw):
    if len(raw) == 0: raise TxErr("empty transaction")
    b0 = raw[0]
    tx = {'raw': bytes(raw)}
    if 1 <= b0 <= 4:
        f = rlp_decode_fully(raw[1:])
        if not isinstance(f, list): raise TxErr("not a list")
        tx['type'] = b0
        if b0 == 1:
            if len(f) != 11: raise TxErr("AccessListTransaction needs 11 fields")
            cid, nonce, gp, gas, to, value, data, al, yp, r, s = f
            tx.update(chain_id=d_scalar(cid, 8), nonce=d_scalar(nonce, 32),
                      gas_price=d_scalar(gp, None), gas=d_scalar(gas, None), to=d_to(to))
        elif b0 == 2:
            if len(f) != 12: raise TxErr("FeeMarketTransaction needs 12 fields")
            cid, nonce, prio, mf, gas, to, value, data, al, yp, r, s = f
            tx.update(chain_id=d_scalar(cid, 8), nonce=d_scalar(nonce, 32),
                      max_priority_fee_per_gas=d_scalar(prio, None),
                      max_fee_per_gas=d_scalar(mf, None), gas=d_scalar(gas, None), to=d_to(to))
        elif b0 == 3:
            if len(f) != 14: raise TxErr("BlobTransaction needs 14 fields")
            cid, nonce, prio, mf, gas, to, value, data, al, bf, bvh, yp, r, s = f
            tx.update(chain_id=d_scalar(cid, 8), nonce=d_scalar(nonce, 32),
                      max_priority_fee_per_gas=d_scalar(prio, None),
                      max_fee_per_gas=d_scalar(mf, None), gas=d_scalar(gas, None),
                      to=d_fixed(to, 20))
        else:
            if len(f) != 13: raise TxErr("SetCodeTransaction needs 13 fields")
            cid, nonce, prio, mf, gas, to, value, data, al, auths, yp, r, s = f
            tx.update(chain_id=d_scalar(cid, 8), nonce=d_scalar(nonce, 8),
                      max_priority_fee_per_gas=d_scalar(prio, None),
                      max_fee_per_gas=d_scalar(mf, None), gas=d_scalar(gas, None),
                      to=d_fixed(to, 20))
        tx.update(value=d_scalar(value, 32), data=d_bytes(data),
                  access_list=[d_access(a) for a in d_list(al)])
        if b0 == 3:
            tx.update(max_fee_per_blob_gas=d_scalar(bf, 32),
                      blob_versioned_hashes=[d_fixed(h, 32) for h in d_list(bvh)])
        if b0 == 4:
            tx.update(authorizations=[d_auth(a) for a in d_list(auths)])
        tx.update(y_parity=d_scalar(yp, 32), r=d_scalar(r, 32), s=d_scalar(s, 32))
    elif 0xC0 <= b0 <= 0xFE:
        f = rlp_decode_fully(raw)
        if not isinstance(f, list) or len(f) != 9: raise TxErr("LegacyTransaction needs 9 fields")
        nonce, gp, gas, to, value, data, v, r, s = f
        tx.update(type=0, nonce=d_scalar(nonce, 32), gas_price=d_scalar(gp, None),
                  gas=d_scalar(gas, None), to=d_to(to), value=d_scalar(value, 32),
                  data=d_bytes(data), v=d_scalar(v, 32), r=d_scalar(r, 32), s=d_scalar(s, 32))
    else:
        raise TxErr("unknown transaction type")
    # guest envelope (tx.pnk): Uint fee fields <= 32 bytes, gas <= 8 bytes
    for k in ('gas_price', 'max_priority_fee_per_gas', 'max_fee_per_gas'):
        if k in tx and tx[k] >= 1 << 256: raise TxErr("envelope: fee > 32 bytes")
    if tx['gas'] >= 1 << 64: raise TxErr("envelope: gas > 8 bytes")
    return tx

# ---- encoding ------------------------------------------------------------
def access_item(a):
    return enc_list([enc_bytes(a[0]), enc_list([enc_bytes(s) for s in a[1]])])

def auth_item(a):
    return enc_list([scalar(a['chain_id']), enc_bytes(a['address']), scalar(a['nonce']),
                     scalar(a['y_parity']), scalar(a['r']), scalar(a['s'])])

def to_item(to):
    return enc_bytes(b'' if to is None else to)

def unsigned_fields(tx):
    t = tx['type']
    if t == 0:
        return [scalar(tx['nonce']), scalar(tx['gas_price']), scalar(tx['gas']),
                to_item(tx['to']), scalar(tx['value']), enc_bytes(tx['data'])]
    f = [scalar(tx['chain_id']), scalar(tx['nonce'])]
    if t == 1: f.append(scalar(tx['gas_price']))
    else: f += [scalar(tx['max_priority_fee_per_gas']), scalar(tx['max_fee_per_gas'])]
    f += [scalar(tx['gas']), to_item(tx['to']), scalar(tx['value']), enc_bytes(tx['data']),
          enc_list([access_item(a) for a in tx['access_list']])]
    if t == 3:
        f += [scalar(tx['max_fee_per_blob_gas']),
              enc_list([enc_bytes(h) for h in tx['blob_versioned_hashes']])]
    if t == 4:
        f.append(enc_list([auth_item(a) for a in tx['authorizations']]))
    return f

def encode_transaction(tx):
    f = unsigned_fields(tx)
    if tx['type'] == 0: f += [scalar(tx['v']), scalar(tx['r']), scalar(tx['s'])]
    else: f += [scalar(tx['y_parity']), scalar(tx['r']), scalar(tx['s'])]
    body = enc_list(f)
    return body if tx['type'] == 0 else bytes([tx['type']]) + body

def signing_hash(tx, chain_id):
    f = unsigned_fields(tx)
    if tx['type'] == 0:
        if tx['v'] not in (27, 28): f += [scalar(chain_id), scalar(0), scalar(0)]
        return pyref.keccak256(enc_list(f))
    return pyref.keccak256(bytes([tx['type']]) + enc_list(f))

def chain_id_of(tx):
    """Lean chain_id: (some, value); raises on legacy v < 35 (non 27/28)."""
    if tx['type'] != 0: return (1, tx['chain_id'])
    v = tx['v']
    if v in (27, 28): return (0, 0)
    if v < 35: raise TxErr("bad v")
    cid = (v - 35) >> 1
    if cid >= 1 << 64: raise TxErr("envelope: chain id > 64 bits")
    return (1, cid)

def signature_recovery_parameters(tx, chain_id):
    r, s = tx['r'], tx['s']
    if r == 0 or r >= SECP256K1N: raise TxErr("bad r")
    if s == 0 or s > SECP256K1N // 2: raise TxErr("bad s")
    if tx['type'] == 0:
        v = tx['v']
        if v in (27, 28): return (v - 27, signing_hash(tx, chain_id))
        if v != 35 + 2 * chain_id and v != 36 + 2 * chain_id: raise TxErr("bad v")
        return (v - 35 - 2 * chain_id, signing_hash(tx, chain_id))
    yp = tx['y_parity']
    if yp not in (0, 1): raise TxErr("bad y_parity")
    return (yp, signing_hash(tx, chain_id))

# ---- intrinsic gas -------------------------------------------------------
def count_tokens_in_data(data):
    z = data.count(0)
    return z + (len(data) - z) * 4

def calculate_intrinsic_cost(tx, sender):
    data = tx['data']
    data_cost = count_tokens_in_data(data) * TX_DATA_TOKEN_STANDARD
    is_create = tx['to'] is None
    is_self = tx['to'] == sender
    if is_create:
        rr = CREATE_ACCESS + (TRANSFER_LOG_COST if tx['value'] > 0 else 0)
        init = CODE_INIT_PER_WORD * ((len(data) + 31) // 32)
    elif not is_self:
        rr = COLD_ACCOUNT_ACCESS + (TRANSFER_LOG_COST + TX_VALUE_COST if tx['value'] > 0 else 0)
        init = 0
    else:
        rr, init = 0, 0
    alc, tok = 0, 0
    for a in tx.get('access_list', []) if tx['type'] != 0 else []:
        alc += COLD_ACCOUNT_ACCESS + len(a[1]) * COLD_STORAGE_ACCESS
        tok += ACCESS_LIST_ADDRESS_FLOOR_TOKENS + len(a[1]) * ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS
    alc += tok * TX_DATA_TOKEN_FLOOR
    auth = REGULAR_PER_AUTH_BASE_COST * len(tx['authorizations']) if tx['type'] == 4 else 0
    floor_tokens = len(data) * TX_DATA_TOKEN_STANDARD + tok
    base = TX_BASE + rr
    return (base + init + data_cost + alc + auth, 0, floor_tokens * TX_DATA_TOKEN_FLOOR + base)

def validate_transaction(tx, sender):
    """0 if valid else the tx.pnk rejection code (60..65)."""
    reg, st, fl = calculate_intrinsic_cost(tx, sender)
    if reg + st > tx['gas']: return 60
    if fl > tx['gas']: return 61
    if tx['to'] is None and len(tx['data']) > MAX_INIT_CODE_SIZE: return 62
    if reg > TX_MAX_GAS_LIMIT: return 63
    if fl > TX_MAX_GAS_LIMIT: return 64
    if tx['nonce'] >= (1 << 64) - 1: return 65
    return 0

# ---- fixture walking -----------------------------------------------------
def le32(b, o): return struct.unpack_from('<I', b, o)[0]

def var_list(b):
    if not b: return []
    first = le32(b, 0); n = first // 4
    offs = [le32(b, 4 * i) for i in range(n)] + [len(b)]
    return [b[offs[i]:offs[i + 1]] for i in range(n)]

def fixture_txs(blob):
    body = blob[2:]
    o = [le32(body, 4 * i) for i in range(4)]
    npr = body[o[0]:o[1]]
    pl_off = le32(npr, 0); vh_off = le32(npr, 4)
    payload = npr[pl_off:vh_off]
    txs_off = le32(payload, 504); wd_off = le32(payload, 508)
    return var_list(payload[txs_off:wd_off])

SENDER = bytes(20)
W = lambda x: struct.pack('<Q', x & ((1 << 64) - 1))

def tx_record(raw):
    try:
        tx = decode_transaction(raw)
    except TxErr:
        return W(-1) + bytes(152 - 8)
    out = W(tx['type']) + W(tx['nonce']) + W(tx['gas']) + W(0 if tx['to'] is None else 1)
    out += W(len(tx['data'])) + W(len(tx.get('access_list', [])))
    out += W(len(tx.get('blob_versioned_hashes', []))) + W(len(tx.get('authorizations', [])))
    try:
        some, cid = chain_id_of(tx)
        recid, h = signature_recovery_parameters(tx, cid)
    except TxErr:
        some, cid, recid, h = 0, 0, -1, bytes(32)
    reg, st, fl = calculate_intrinsic_cost(tx, SENDER)
    out += h + W(recid) + W(reg) + W(fl)
    out += W(1 if encode_transaction(tx) == tx['raw'] else 0)
    out += W(some) + W(cid) + W(validate_transaction(tx, SENDER))
    assert len(out) == 152
    return out

def expected(blob):
    return b''.join(tx_record(t) for t in fixture_txs(blob))

if __name__ == '__main__':
    # survey: python3 exp_tx.py INPUT... -> per input the tx types
    for path in sys.argv[1:]:
        packed = open(path, 'rb').read()
        n = struct.unpack('<Q', packed[:8])[0]; blob = packed[8:8 + n]
        types = []
        for t in fixture_txs(blob):
            try: types.append(decode_transaction(t)['type'])
            except TxErr as e: types.append('E:' + str(e))
        print(os.path.basename(path)[:60], types)
