"""exp_tx_neg.py -- rejection cases for tx.pnk. CASES: (envelope hex, stage,
expected TxErr code); stage 0 = decode_transaction, 1 = tx_chain_id after a
successful decode, 2 = signature_recovery_parameters (chain id 1),
3 = validate_transaction. Running this file regenerates t_tx_neg.pnk, which
embeds the envelopes and outputs one LE word (the caught code, 0 = no
error) per case. The unit INPUT is ignored (any fixture works)."""
import struct, sys, os

def enc_len(n, base):
    if n <= 55: return bytes([base + n])
    lb = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    return bytes([base + 55 + len(lb)]) + lb
def B(b):
    if len(b) == 1 and b[0] < 0x80: return bytes(b)
    return enc_len(len(b), 0x80) + bytes(b)
def L(items):
    p = b''.join(items); return enc_len(len(p), 0xC0) + p
def S(n): return B(n.to_bytes((n.bit_length() + 7) // 8, 'big') if n else b'')

ADDR = bytes(20) + b''; ADDR = bytes([0xAA] * 20)
R = 1; SS = 1
def legacy(nonce=S(1), gp=S(10), gas=S(21000), to=B(ADDR), value=S(0), data=B(b''), v=S(27), r=S(R), s=S(SS), extra=()):
    return L([nonce, gp, gas, to, value, data, v, r, s, *extra])
def fee(cid=S(1), nonce=S(1), prio=S(1), mf=S(10), gas=S(21000), to=B(ADDR), value=S(0), data=B(b''), al=L([]), yp=S(0), r=S(R), s=S(SS)):
    return b'\x02' + L([cid, nonce, prio, mf, gas, to, value, data, al, yp, r, s])
def blob(to=B(ADDR), bvh=L([B(b'\x01' + bytes(31))])):
    return b'\x03' + L([S(1), S(1), S(1), S(10), S(21000), to, S(0), B(b''), L([]), S(1), bvh, S(0), S(R), S(SS)])
def setcode(auths=L([L([S(1), B(ADDR), S(0), S(0), S(R), S(SS)])]), nonce=S(1)):
    return b'\x04' + L([S(1), nonce, S(1), S(10), S(60000), B(ADDR), S(0), B(b''), L([]), auths, S(0), S(R), S(SS)])
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

CASES = [
    (b'', 0, 1),                                   # empty
    (b'\x05' + L([]), 0, 2),                       # unknown type
    (b'\xff' + L([]), 0, 2),                       # 0xFF assert
    (b'\x80', 0, 2),                               # a string, not a list prefix
    (L([S(1)] * 8), 0, 4),                         # legacy needs 9 fields
    (legacy(extra=(S(0),)), 0, 4),                 # 10 fields
    (legacy(nonce=B(b'\x00\x01')), 0, 11),         # leading zero
    (legacy(nonce=B(bytes([1] * 33))), 0, 12),     # nonce > 32 bytes
    (legacy(gp=B(bytes([1] * 33))), 0, 13),        # Uint gasPrice > 32 bytes (envelope)
    (legacy(gas=B(bytes([1] * 9))), 0, 14),        # gas > 8 bytes (envelope)
    (legacy(to=B(bytes(19))), 0, 17),              # bad to
    (legacy(nonce=L([])), 0, 10),                  # list as scalar
    (legacy(data=L([])), 0, 15),                   # list as bytes
    (legacy() + b'\x00', 0, 106),                  # trailing byte -> RlpErr 6
    (legacy()[:-1], 0, 103),                       # truncated -> RlpErr 3
    (fee() + b'\x00', 0, 106),                     # typed trailing byte
    (fee(cid=B(bytes([1] * 9))), 0, 12),           # chainId > 8 bytes
    (fee(al=S(0)), 0, 18),                         # access list not a list
    (fee(al=L([L([B(ADDR)])])), 0, 19),            # access entry with 1 field
    (fee(al=L([L([B(ADDR), L([B(bytes(31))])])])), 0, 16),  # slot of 31 bytes
    (fee(al=L([L([B(bytes(19)), L([])])])), 0, 16),         # address of 19 bytes
    (b'\x02' + L([S(1)] * 11), 0, 4),              # fee market needs 12
    (blob(to=B(b'')), 0, 16),                      # blob creation forbidden
    (blob(bvh=L([B(bytes(31))])), 0, 16),          # 31-byte versioned hash
    (setcode(nonce=B(bytes([1] * 9))), 0, 12),     # setCode nonce > 8 bytes
    (setcode(auths=L([L([S(1), B(ADDR), S(0), S(0), S(R)])])), 0, 20),  # 5-field auth
    (setcode(auths=L([L([S(1), B(ADDR), S(0), S(2**8), S(R), S(SS)])])), 0, 12),  # y_parity 2 bytes
    (setcode(auths=L([L([S(1), B(ADDR), S(2**64), S(0), S(R), S(SS)])])), 0, 12),  # auth nonce 9 bytes
    (legacy(v=S(30)), 1, 44),                      # chain_id: v < 35
    (legacy(v=S(2**70)), 1, 45),                   # chain_id does not fit 64 bits (envelope)
    (legacy(v=S(37)), 1, 0),                       # chain id 1 -> fine
    (legacy(r=S(0)), 2, 40),                       # r = 0
    (legacy(r=S(N)), 2, 40),                       # r = n
    (legacy(s=S(0)), 2, 41),                       # s = 0
    (legacy(s=S(N // 2 + 1)), 2, 41),              # s > n/2
    (legacy(s=S(N // 2)), 2, 0),                   # s = n/2 ok
    (legacy(v=S(39)), 2, 42),                      # v for chain id 2, given 1
    (legacy(v=S(38)), 2, 0),                       # v = 36 + 2*1 ok
    (fee(yp=S(2)), 2, 43),                         # y_parity 2
    (fee(yp=S(1)), 2, 0),
    (legacy(gas=S(14999)), 3, 60),                 # 12000 + 3000 = 15000 > gas
    (legacy(gas=S(15000)), 3, 0),
    (legacy(to=B(b''), gas=S(23010), data=B(bytes(1))), 3, 61),  # regular 23006 <= gas < floor 23064
    (legacy(nonce=S(2**64 - 1), gas=S(15000)), 3, 65),
    (fee(nonce=S(2**64), gas=S(15000)), 3, 65),
    (legacy(to=B(b''), gas=S(9000000), data=B(b'\x00' * 131073)), 3, 62),  # init code too large
]

def expected(blob):
    return b''.join(struct.pack('<Q', c[2]) for c in CASES)

def gen():
    here = os.path.dirname(os.path.abspath(__file__))
    out = ['#include "config.h"', '#include "types.h"', '#include "lib/mem.pnk"',
           '#include "lib/arith.pnk"', '#include "lib/u256.pnk"', '#include "lib/keccak.pnk"',
           '#include "lib/rlp.pnk"', '#include "tx.pnk"', '#include "secp_stub.pnk"',
           '/* GENERATED by exp_tx_neg.py: one word per case = the TxErr code caught */',
           'fun 1 run_case(1 p, 1 n, 1 stage, 1 sender, 1 scratch) {',
           '  var code = 0;', '  var 1 tx = 0;',
           '  try tx = decode_transaction(p, n) catch TxErr => code { return code; }',
           '  if stage == 1 { var {1,1} c = <0, 0>; try c = tx_chain_id(tx) catch TxErr => code { return code; } return 0; }',
           '  if stage == 2 { var 1 rid = 0; try rid = signature_recovery_parameters(tx, 1, scratch) catch TxErr => code { return code; } return 0; }',
           '  if stage == 3 { var {1,1,1} ic = <0, 0, 0>; try ic = validate_transaction(tx, sender) catch TxErr => code { return code; } return 0; }',
           '  return 0;', '}',
           'fun 1 main() {', '  mem_init();', '  keccak_init();',
           '  var 1 out = alloc(%d);' % (8 * len(CASES) + 8),
           '  var 1 sender = alloc(24);', '  memzero(sender, 24);', '  var 1 scratch = alloc(32);',
           '  var 1 buf = 0;', '  var 1 c = 0;']
    for i, (env, stage, _) in enumerate(CASES):
        out.append('  buf = alloc(%d);' % (len(env) + 8))
        # long runs of zeros come from memzero; other bytes are stored one by one
        out.append('  memzero(buf, %d);' % (len(env) + 8))
        for j, b in enumerate(env):
            if b: out.append('  st8 buf + %d, %d;' % (j, b))
        out.append('  c = run_case(buf, %d, %d, sender, scratch);' % (len(env), stage))
        out.append('  st out + %d, c;' % (8 * i))
    out += ['  output_write(out, %d);' % (8 * len(CASES)), '  @halt(@base, 0, @base, 0);', '  return 0;', '}']
    open(os.path.join(here, 't_tx_neg.pnk'), 'w').write('\n'.join(out) + '\n')

if __name__ == '__main__':
    gen()
