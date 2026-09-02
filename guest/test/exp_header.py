import struct, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'tools'))
import pyref
def le32(b, o): return struct.unpack_from('<I', b, o)[0]
def var_list(b):
    if not b: return []
    first = le32(b, 0); n = first // 4
    offs = [le32(b, 4*i) for i in range(n)] + [len(b)]
    return [b[offs[i]:offs[i+1]] for i in range(n)]
def expected(blob):
    body = blob[2:]
    o = [le32(body, 4*i) for i in range(4)]
    wit = body[o[1]:o[2]]
    w = [le32(wit, 4*i) for i in range(3)]
    headers = var_list(wit[w[2]:])
    out = b''.join(pyref.keccak256(h) for h in headers)
    out += b''.join(struct.pack('<Q', 1) for _ in headers)
    return out
