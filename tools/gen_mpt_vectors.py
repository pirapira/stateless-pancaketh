#!/usr/bin/env python3
"""gen_mpt_vectors.py OUT_DIR [--seed S] [--fixture INPUT] [--bench-sets N] [--bench-keccak R]

Run with the execution-specs environment:
  uv run --directory evm-asm/execution-specs python tools/gen_mpt_vectors.py OUT_DIR

Writes OUT_DIR/mpt.input (ziskemu framing: u64 LE len, blob, zero pad to 8),
OUT_DIR/mpt.expected and OUT_DIR/mpt.mask (0xff = byte must match). The blob is
an op stream replayed by guest/test/t_mpt.pnk; every op yields a record
  [u8 status 0 ok / 1 MptErr][u8 code][6 zero] + payload:
  OP_NEW 1        [u8 secured]                                     -> (none)
  OP_SET 2        [u16 klen][key][u16 vlen][value]  (vlen 0 = delete) -> (none)
  OP_ROOT 3                                                        -> [32 root]
  OP_GET 4        [u16 klen][key]                                  -> value(40)
  OP_INDEXED 5    [u32 n] n x [u16 len][bytes]                     -> [32 root]
  OP_WITNESS 6    [u32 n] n x [u16 len][node] [32 root][u8 secured]-> (none)
  OP_LOOKUP_ACCT 7 [20 addr]                                       -> acct(112)
  OP_LOOKUP_SLOT 8 [20 addr][32 slot]                              -> value(40)
  OP_SET_ACCT 9   [20 addr][u8 present][u64 nonce][32 bal LE][32 root][32 code] -> (none)
  OP_DECODE_ACCT 10 [u16 len][leaf value]                          -> acct(112)
  OP_ENCODE_ACCT 11 [u64 nonce][32 bal LE][32 root][32 code]       -> value(40)
  OP_KECCAK 13    [u32 n][u32 reps]                                -> [32 hash]
value(40) = [found][0 0 0][u32 len][32: value zero-padded, or keccak256 if len > 32]
acct(112) = [found][0 x7][u64 nonce][32 balance LE limbs][32 storage_root][32 code_hash]
The MptErr code byte is masked out whenever Python raised (status 1)."""
import argparse, glob, os, random, struct, sys

from ethereum_rlp import rlp
from ethereum_rlp.exceptions import DecodingError
from ethereum_types.numeric import U256, Uint
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import EMPTY_TRIE_ROOT, Trie, root, trie_set
from ethereum.forks.amsterdam.fork_types import Account
from ethereum.forks.amsterdam.incremental_mpt import (
    HashedNode, IncrementalMPT, MutableBranchNode, MutableExtensionNode,
    _compute_node_hash_and_rlp, decode_witness_to_mpt, mpt_root, mpt_set,
)
from ethereum.forks.amsterdam.witness_state import (
    EMPTY_CODE_HASH, _decode_account_from_leaf, _trie_lookup, build_node_db,
)

OP_NEW, OP_SET, OP_ROOT, OP_GET, OP_INDEXED, OP_WITNESS = 1, 2, 3, 4, 5, 6
OP_LOOKUP_ACCT, OP_LOOKUP_SLOT, OP_SET_ACCT, OP_DECODE_ACCT, OP_ENCODE_ACCT = 7, 8, 9, 10, 11
OP_KECCAK = 13
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def items(lst):
    out = struct.pack("<I", len(lst))
    for b in lst:
        out += struct.pack("<H", len(b)) + b
    return out


class Gen:
    def __init__(self):
        self.inp = bytearray()
        self.exp = bytearray()
        self.mask = bytearray()
        self.m = None      # current IncrementalMPT
        self.db = None     # current node db
        self.nrec = 0

    # ---- record helpers -------------------------------------------------
    def status(self, st):
        self.exp += bytes([st]) + bytes(7)
        self.mask += b"\xff" + (b"\x00" if st else b"\xff") + b"\xff" * 6
        self.nrec += 1

    def payload(self, b):
        self.exp += b
        self.mask += b"\xff" * len(b)

    def value_rec(self, v):
        if v is None:
            return bytes(40)
        tail = v.ljust(32, b"\0") if len(v) <= 32 else keccak256(v)
        return b"\x01\0\0\0" + struct.pack("<I", len(v)) + tail

    def acct_rec(self, acc, sr):
        if acc is None:
            return bytes(112)
        return (b"\x01" + bytes(7) + struct.pack("<Q", int(acc.nonce))
                + int(acc.balance).to_bytes(32, "little") + bytes(sr) + bytes(acc.code_hash))

    def attempt(self, fn, size):
        """Run fn (Python reference): (ok, result); status 1 + zero payload on any spec error."""
        try:
            res = fn()
        except (AssertionError, KeyError, ValueError, IndexError, OverflowError, TypeError, DecodingError):
            self.status(1)
            self.payload(bytes(size))
            return (False, None)
        self.status(0)
        return (True, res)

    # ---- ops --------------------------------------------------------------
    def op_new(self, secured):
        self.inp += bytes([OP_NEW, secured])
        self.m = IncrementalMPT(secured=bool(secured), default=b"", root_node=None)
        self.status(0)

    def op_set(self, key, value):
        self.inp += bytes([OP_SET]) + struct.pack("<H", len(key)) + key + struct.pack("<H", len(value)) + value
        self.attempt(lambda: mpt_set(self.m, key, value), 0)

    def op_root(self):
        self.inp += bytes([OP_ROOT])
        ok, r = self.attempt(lambda: mpt_root(self.m), 32)
        if ok:
            self.payload(bytes(r))

    def op_get(self, key):
        self.inp += bytes([OP_GET]) + struct.pack("<H", len(key)) + key
        # mpt_get returns _data; the Pancake port walks the tree (raises on HashedNode)
        def f():
            nib = key_nibbles(key, self.m.secured)
            return _trie_lookup(self.m.root_node, nib)
        ok, v = self.attempt(f, 40)
        if ok:
            self.payload(self.value_rec(v))

    def op_indexed(self, values):
        self.inp += bytes([OP_INDEXED]) + items(values)
        t = Trie(secured=False, default=None)
        for i, v in enumerate(values):
            trie_set(t, rlp.encode(Uint(i)), v)
        self.status(0)
        self.payload(bytes(root(t)))

    def op_witness(self, nodes, root_hash, secured=1):
        self.inp += bytes([OP_WITNESS]) + items(nodes) + bytes(root_hash) + bytes([secured])
        self.db = build_node_db(tuple(nodes))
        def f():
            self.m = decode_witness_to_mpt(self.db, root_hash, bool(secured), None)
        ok, _ = self.attempt(f, 0)
        if not ok:
            self.m = IncrementalMPT(secured=True, default=None, root_node=None)

    def op_lookup_acct(self, addr):
        self.inp += bytes([OP_LOOKUP_ACCT]) + addr
        def f():
            leaf = _trie_lookup(self.m.root_node, keccak256(addr))
            if leaf is None:
                return (None, None)
            return _decode_account_from_leaf(leaf)
        ok, r = self.attempt(f, 112)
        if ok:
            self.payload(self.acct_rec(*r))
        return r if ok else None

    def op_lookup_slot(self, addr, slot):
        self.inp += bytes([OP_LOOKUP_SLOT]) + addr + slot
        def f():
            leaf = _trie_lookup(self.m.root_node, keccak256(addr))
            if leaf is None:
                return None
            _, sr = _decode_account_from_leaf(leaf)
            if sr == EMPTY_TRIE_ROOT:
                return None
            sm = decode_witness_to_mpt(self.db, sr, True, U256(0))
            return _trie_lookup(sm.root_node, keccak256(slot))
        ok, r = self.attempt(f, 40)
        if ok:
            self.payload(self.value_rec(r))

    def op_set_acct(self, addr, acc, sr):
        if acc is None:
            self.inp += bytes([OP_SET_ACCT]) + addr + bytes(1) + bytes(8 + 96)
            ok, _ = self.attempt(lambda: mpt_set(self.m, addr, None), 0)
        else:
            self.inp += (bytes([OP_SET_ACCT]) + addr + b"\x01" + struct.pack("<Q", int(acc.nonce))
                         + int(acc.balance).to_bytes(32, "little") + bytes(sr) + bytes(acc.code_hash))
            ok, _ = self.attempt(lambda: mpt_set(self.m, addr, acc, get_storage_root=lambda a: sr), 0)
        return ok

    def op_decode_acct(self, leaf):
        self.inp += bytes([OP_DECODE_ACCT]) + struct.pack("<H", len(leaf)) + leaf
        def f():
            acc, sr = _decode_account_from_leaf(leaf)
            if int(acc.nonce) >= 1 << 64:
                raise ValueError("nonce envelope")
            return acc, sr
        ok, r = self.attempt(f, 112)
        if ok:
            self.payload(self.acct_rec(*r))

    def op_encode_acct(self, nonce, balance, sr, ch):
        self.inp += (bytes([OP_ENCODE_ACCT]) + struct.pack("<Q", nonce)
                     + balance.to_bytes(32, "little") + sr + ch)
        enc = rlp.encode((Uint(nonce), U256(balance), sr, ch))
        self.status(0)
        self.payload(self.value_rec(enc))

    def op_keccak(self, n, reps):
        self.inp += bytes([OP_KECCAK]) + struct.pack("<II", n, reps)
        self.status(0)
        self.payload(keccak256(bytes(n)))


def key_nibbles(key, secured):
    return keccak256(key) if secured else key


def collect_nodes(node, out):
    """All hash-referenced node preimages of a mutable tree (plus the root)."""
    if node is None or isinstance(node, HashedNode):
        return
    h, r = _compute_node_hash_and_rlp(node)
    if h is not None:
        out.append(bytes(r))
    if isinstance(node, MutableExtensionNode):
        collect_nodes(node.child, out)
    elif isinstance(node, MutableBranchNode):
        for c in node.children:
            collect_nodes(c, out)


def rand_value(rng):
    kind = rng.random()
    if kind < 0.15:
        n = rng.randint(1, 5)
    elif kind < 0.5:
        n = rng.randint(6, 31)      # inline children
    else:
        n = rng.randint(32, 90)     # hashed children
    return rng.randbytes(n)


# ---- scenarios ----------------------------------------------------------------

def scenario_random(g, rng, secured, keys, roots_every=1):
    g.op_new(secured)
    g.op_root()                       # empty trie
    live = {}
    order = list(keys)
    rng.shuffle(order)
    for i, k in enumerate(order):
        v = rand_value(rng)
        g.op_set(k, v)
        live[k] = v
        if i % roots_every == 0:
            g.op_root()
    # updates (short<->long), same-value writes, missing-key gets
    for k in rng.sample(order, min(6, len(order))):
        v = rand_value(rng)
        g.op_set(k, v)
        live[k] = v
        g.op_root()
        g.op_get(k)
    g.op_get(rng.randbytes(len(order[0])))
    g.op_set(rng.randbytes(len(order[0])), b"")      # delete of an absent key
    g.op_root()
    # delete everything in random order, collapsing back to the empty trie
    rng.shuffle(order)
    for i, k in enumerate(order):
        g.op_set(k, b"")
        if i % roots_every == 0 or i >= len(order) - 3:
            g.op_root()
    g.op_get(order[0])
    g.op_root()


def scenario_structural(g, rng):
    # single leaf
    g.op_new(0)
    g.op_set(b"\xab\xcd", b"v")
    g.op_root()
    g.op_get(b"\xab\xcd")
    g.op_get(b"\xab")
    g.op_set(b"\xab\xcd", b"")
    g.op_root()
    # branch value: a key that is a prefix of two others (unsecured)
    g.op_new(0)
    g.op_set(b"\x12", b"x" * 40)
    g.op_set(b"\x12\x34", b"y")
    g.op_set(b"\x12\x35", b"z" * 33)
    g.op_root()
    g.op_get(b"\x12")
    g.op_set(b"\x12", b"")                      # remove the branch value
    g.op_root()
    g.op_set(b"\x12\x34", b"")                  # collapse to a single leaf
    g.op_root()
    g.op_get(b"\x12\x35")
    g.op_set(b"\x12\x35", b"")
    g.op_root()
    # value at a branch whose children vanish -> leaf with empty rest_of_key
    g.op_new(0)
    g.op_set(b"\x12", b"top")
    g.op_set(b"\x12\x34", b"a")
    g.op_set(b"\x12\x35", b"b")
    g.op_set(b"\x12\x34", b"")
    g.op_set(b"\x12\x35", b"")
    g.op_root()
    g.op_get(b"\x12")
    # extension splits: long shared prefix, divergence at several depths
    g.op_new(0)
    base = b"\xde\xad\xbe\xef\xca\xfe"
    g.op_set(base + b"\x00\x01", b"A" * 35)
    g.op_set(base + b"\x00\x02", b"B" * 35)
    g.op_root()                                  # extension over a branch
    g.op_set(base + b"\x10\x00", b"C")           # split at the end of the extension
    g.op_root()
    g.op_set(b"\xde\xad\xbe\x00", b"D" * 36)     # split in the middle
    g.op_root()
    g.op_set(b"\xde\xad\xbe\xef\xca\xfe", b"E")  # key ends inside the extension path
    g.op_root()
    g.op_set(b"\xd0", b"F")                      # split at the first nibble
    g.op_root()
    for k in [base + b"\x00\x01", b"\xde\xad\xbe\x00", b"\xd0", base + b"\x10\x00", base, base + b"\x00\x02"]:
        g.op_set(k, b"")
        g.op_root()
    # extension whose child branch collapses -> extension merge / leaf merge
    g.op_new(0)
    g.op_set(b"\xaa\xaa\x01\x00", b"1" * 40)
    g.op_set(b"\xaa\xaa\x02\x00", b"2" * 40)
    g.op_set(b"\xaa\xaa\x02\x11", b"3" * 40)
    g.op_root()
    g.op_set(b"\xaa\xaa\x01\x00", b"")           # ext -> (branch collapses to ext) => merged extension
    g.op_root()
    g.op_set(b"\xaa\xaa\x02\x11", b"")           # ext -> leaf => merged leaf
    g.op_root()
    g.op_get(b"\xaa\xaa\x02\x00")


def scenario_indexed(g, rng):
    g.op_indexed([])
    g.op_indexed([b"\x01"])
    g.op_indexed([rng.randbytes(50), rng.randbytes(3), rng.randbytes(100)])
    vals = [rng.randbytes(rng.choice([1, 8, 31, 32, 60, 120])) for _ in range(135)]
    g.op_indexed(vals)


def scenario_accounts(g, rng):
    sr = EMPTY_TRIE_ROOT
    for nonce, bal in [(0, 0), (1, 10**18), (127, 128), (128, 2**64 - 1), (2**64 - 1, 2**256 - 1),
                       (5, 255), (rng.getrandbits(64), rng.getrandbits(256))]:
        ch = rng.randbytes(32)
        g.op_encode_acct(nonce, bal, sr, ch)
        leaf = rlp.encode((Uint(nonce), U256(bal), sr, ch))
        g.op_decode_acct(leaf)
    # sentinels for empty fields, and malformed leaves
    g.op_decode_acct(rlp.encode((b"", b"", b"", b"")))
    g.op_decode_acct(rlp.encode((b"\x01" * 9, b"", b"", b"")))           # nonce > 8 bytes
    g.op_decode_acct(rlp.encode((b"", b"\x01" * 33, b"", b"")))          # balance > 32 bytes
    g.op_decode_acct(rlp.encode((b"", b"", b"\x01" * 31, b"")))          # bad storage_root
    g.op_decode_acct(rlp.encode((b"", b"", b"", b"\x01" * 33)))          # bad code_hash
    g.op_decode_acct(rlp.encode((b"", b"", b"")))                        # 3 items
    g.op_decode_acct(rlp.encode(b"\x01\x02"))                            # not a list
    g.op_decode_acct(rlp.encode((b"", [b""], b"", b"")))                 # nested list field
    g.op_decode_acct(b"\xc4\x80\x80\x80")                                # truncated


def scenario_synthetic_witness(g, rng):
    """State + storage tries built with the Python spec; every >= 32-byte node
    becomes a witness entry. Then decode, look up, mutate, and re-root."""
    addrs = [rng.randbytes(20) for _ in range(9)]
    storage = {}
    srs = {}
    nodes = []
    for a in addrs[:4]:
        sm = IncrementalMPT(secured=True, default=U256(0), root_node=None)
        slots = {}
        for _ in range(rng.randint(1, 6)):
            slot = rng.choice([rng.randbytes(32), rng.getrandbits(8).to_bytes(32, "big")])
            val = rng.choice([1, 255, 256, rng.getrandbits(64), rng.getrandbits(256)])
            slots[slot] = U256(val)
            mpt_set(sm, slot, U256(val))
        storage[a] = slots
        srs[a] = mpt_root(sm)
        collect_nodes(sm.root_node, nodes)
    accts = {}
    m = IncrementalMPT(secured=True, default=None, root_node=None)
    for a in addrs:
        acc = Account(nonce=Uint(rng.getrandbits(8)), balance=U256(rng.getrandbits(80)),
                      code_hash=rng.choice([EMPTY_CODE_HASH, rng.randbytes(32)]))
        accts[a] = acc
        mpt_set(m, a, acc, get_storage_root=lambda x: srs.get(x, EMPTY_TRIE_ROOT))
    state_root = mpt_root(m)
    collect_nodes(m.root_node, nodes)
    rng.shuffle(nodes)

    g.op_witness(nodes, state_root)
    g.op_root()
    for a in addrs + [rng.randbytes(20)]:
        g.op_lookup_acct(a)
    for a in addrs[:5]:
        for slot in list(storage.get(a, {}))[:3] + [rng.randbytes(32), bytes(32)]:
            g.op_lookup_slot(a, slot)
    # mutate: update, create, delete; compare roots
    a0 = addrs[0]
    g.op_set_acct(a0, Account(nonce=Uint(7), balance=U256(1), code_hash=accts[a0].code_hash), srs[a0])
    g.op_root()
    g.op_lookup_acct(a0)
    new = rng.randbytes(20)
    g.op_set_acct(new, Account(nonce=Uint(1), balance=U256(2**200), code_hash=EMPTY_CODE_HASH), EMPTY_TRIE_ROOT)
    g.op_root()
    g.op_lookup_acct(new)
    for a in addrs[1:4]:
        g.op_set_acct(a, None, None)
        g.op_root()
        g.op_lookup_acct(a)
    g.op_set_acct(new, None, None)
    g.op_root()
    # withhold one account leaf -> HashedNode placeholder: reachable reads/writes fail
    leaf_rlps = []
    for a in addrs[4:6]:
        leaf_rlps.append(bytes(rlp.encode(_leaf_of(m.root_node, keccak256(a)))))
    withheld = [n for n in nodes if n not in leaf_rlps]
    g.op_witness(withheld, state_root)
    g.op_root()                       # root still computable (hashed children embed as hashes)
    g.op_lookup_acct(addrs[4])        # -> MptErr (unresolved hashed node)
    g.op_lookup_acct(addrs[0])        # fine
    g.op_set_acct(addrs[4], None, None)  # write reaching the placeholder -> MptErr
    g.op_witness(withheld, state_root)
    g.op_set_acct(addrs[0], Account(nonce=Uint(9), balance=U256(9), code_hash=EMPTY_CODE_HASH), EMPTY_TRIE_ROOT)
    g.op_root()                       # write elsewhere still works
    # missing root preimage
    g.op_witness(withheld[:3], state_root)
    g.op_witness(nodes, EMPTY_TRIE_ROOT)
    g.op_root()
    g.op_lookup_acct(addrs[0])


def scenario_withheld_collapse(g, rng):
    """IncrementalMptWrite.lean sanity check: with one of two account leaves
    withheld, deleting the other forces the branch collapse onto the
    HashedNode sibling -> rejection, never a wrong root."""
    a, b = rng.randbytes(20), rng.randbytes(20)
    m = IncrementalMPT(secured=True, default=None, root_node=None)
    acc = Account(nonce=Uint(1), balance=U256(100), code_hash=EMPTY_CODE_HASH)
    for x in (a, b):
        mpt_set(m, x, acc, get_storage_root=lambda _x: EMPTY_TRIE_ROOT)
    state_root = mpt_root(m)
    nodes = []
    collect_nodes(m.root_node, nodes)
    leaf_b = bytes(rlp.encode(_leaf_of(m.root_node, keccak256(b))))
    g.op_witness([n for n in nodes if n != leaf_b], state_root)
    g.op_lookup_acct(a)
    g.op_root()
    g.op_set_acct(a, acc, EMPTY_TRIE_ROOT)         # rewriting a -> fine
    g.op_root()
    g.op_set_acct(a, None, None)                    # collapse onto the hashed sibling -> MptErr
    g.op_witness([n for n in nodes if n != leaf_b], state_root)
    c = rng.randbytes(20)
    g.op_set_acct(c, acc, EMPTY_TRIE_ROOT)          # a third account: may or may not touch the placeholder
    g.op_root()
    g.op_witness(nodes, state_root)
    g.op_set_acct(a, None, None)                    # fully resolved: collapse succeeds
    g.op_root()
    g.op_lookup_acct(b)


def scenario_inline_witness(g, rng):
    """Unsecured trie with short keys: children with RLP < 32 bytes are embedded
    inline in their parent (the _resolve_child_ref list case)."""
    m = IncrementalMPT(secured=False, default=b"", root_node=None)
    keys = [b"\x10\x01", b"\x10\x02", b"\x10\x02\x33", b"\x20", b"\x21\x00", b"\x21\x01"]
    vals = {k: rng.randbytes(rng.choice([1, 2, 5])) for k in keys}
    vals[b"\x20"] = rng.randbytes(40)             # one hashed child among inline ones
    for k in keys:
        mpt_set(m, k, vals[k])
    r = mpt_root(m)
    nodes = []
    collect_nodes(m.root_node, nodes)
    g.op_witness(nodes, r, secured=0)
    g.op_root()
    for k in keys + [b"\x10", b"\x30"]:
        g.op_get(k)
    g.op_set(b"\x10\x02", b"")
    g.op_root()
    g.op_set(b"\x21\x02", b"new")
    g.op_root()
    g.op_set(b"\x20", b"")
    g.op_root()
    g.op_get(b"\x10\x02\x33")


def _leaf_of(node, key_hash):
    """The (compact, value) tuple of the leaf holding key_hash (helper for withholding)."""
    from ethereum.forks.amsterdam.incremental_mpt import MutableLeafNode, _encode_mutable_node
    nib = bytes(b for x in key_hash for b in (x >> 4, x & 15))
    pos = 0
    while node is not None:
        if isinstance(node, MutableLeafNode):
            assert bytes(nib[pos:]) == node.rest_of_key
            return _encode_mutable_node(node)
        if isinstance(node, MutableExtensionNode):
            pos += len(node.key_segment)
            node = node.child
            continue
        node = node.children[nib[pos]]
        pos += 1
    raise AssertionError("leaf not found")


def scenario_fixture(g, rng, path):
    from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
    from ethereum.forks.amsterdam.blocks import Header
    packed = open(path, "rb").read()
    n = struct.unpack("<Q", packed[:8])[0]
    si = deserialize_stateless_input(packed[8:8 + n])
    w = si.witness
    hdr = rlp.decode_to(Header, w.headers[-1])
    pl = si.new_payload_request.execution_payload
    bal = rlp.decode(pl.block_access_list)
    addrs = [bytes(e[0]) for e in bal] + [bytes(pl.fee_recipient), rng.randbytes(20), rng.randbytes(20)]
    g.op_witness([bytes(x) for x in w.state], hdr.state_root)
    g.op_root()
    found = []
    for a in addrs:
        r = g.op_lookup_acct(a)
        if r is not None and r[0] is not None:
            found.append((a, r))
    for e in bal[:3]:
        slots = [bytes(s[0]).rjust(32, b"\0") for s in e[1]] + [bytes(s).rjust(32, b"\0") for s in e[2]]
        for s in (slots or [bytes(32)])[:2]:
            g.op_lookup_slot(bytes(e[0]), s)
    # updates / creation / deletion on the real state trie
    for a, (acc, sr) in found[:3]:
        acc2 = Account(nonce=acc.nonce + Uint(1), balance=acc.balance + U256(12345), code_hash=acc.code_hash)
        if not g.op_set_acct(a, acc2, sr):
            g.op_witness([bytes(x) for x in w.state], hdr.state_root)
        g.op_root()
    new = rng.randbytes(20)
    if not g.op_set_acct(new, Account(nonce=Uint(0), balance=U256(1), code_hash=EMPTY_CODE_HASH), EMPTY_TRIE_ROOT):
        g.op_witness([bytes(x) for x in w.state], hdr.state_root)
    g.op_root()
    for a, _ in found[:2]:
        if not g.op_set_acct(a, None, None):
            g.op_witness([bytes(x) for x in w.state], hdr.state_root)
        g.op_root()
    g.op_lookup_acct(found[0][0])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out_dir")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--fixture", default=None)
    ap.add_argument("--bench-sets", type=int, default=None)
    ap.add_argument("--bench-keccak", type=int, default=None)
    ap.add_argument("--bench-root", type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    g = Gen()
    if args.bench_sets is not None or args.bench_keccak is not None:
        if args.bench_sets is not None:
            g.op_new(1)
            for _ in range(args.bench_sets):
                g.op_set(rng.randbytes(32), rng.randbytes(40))
            if args.bench_root:
                g.op_root()
        if args.bench_keccak is not None:
            g.op_keccak(100, args.bench_keccak)
    else:
        scenario_structural(g, rng)
        # unsecured keys sharing long prefixes, some keys prefixes of others
        base = rng.randbytes(5)
        keys = {base, base + b"\x01"} | {base + rng.randbytes(rng.randint(1, 3)) for _ in range(14)}
        scenario_random(g, rng, 0, sorted(keys))
        scenario_random(g, rng, 1, [rng.randbytes(20) for _ in range(28)], roots_every=3)
        scenario_random(g, rng, 1, [rng.randbytes(32) for _ in range(6)])
        scenario_indexed(g, rng)
        scenario_accounts(g, rng)
        scenario_synthetic_witness(g, rng)
        scenario_withheld_collapse(g, rng)
        scenario_inline_witness(g, rng)
        fixture = args.fixture
        if fixture is None:
            cands = sorted(glob.glob(os.path.join(ROOT, "work/inputs/*.input")))
            fixture = cands[0] if cands else None
        if fixture:
            scenario_fixture(g, rng, fixture)
        else:
            print("no fixture input found; skipping the real-witness scenario", file=sys.stderr)
    os.makedirs(args.out_dir, exist_ok=True)
    blob = bytes(g.inp)
    pad = (-(8 + len(blob))) % 8
    open(os.path.join(args.out_dir, "mpt.input"), "wb").write(struct.pack("<Q", len(blob)) + blob + bytes(pad))
    open(os.path.join(args.out_dir, "mpt.expected"), "wb").write(bytes(g.exp))
    open(os.path.join(args.out_dir, "mpt.mask"), "wb").write(bytes(g.mask))
    print(f"{g.nrec} records, input {len(blob)} bytes, expected {len(g.exp)} bytes")


if __name__ == "__main__":
    main()
