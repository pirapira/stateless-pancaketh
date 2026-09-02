"""Oracle for guest/test/t_p256.pnk (tools/unit.py @exp_p256.py): the pure-Python
P-256 verifier of tools/gen_p256_vectors.py over 160-byte cases."""
import os, struct, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
from gen_p256_vectors import verify


def expected(blob):
    out = b""
    for c in range(len(blob) // 160):
        h = blob[c * 160:c * 160 + 32]
        r, s, qx, qy = (int.from_bytes(blob[c * 160 + 32 * k:c * 160 + 32 * (k + 1)], "big") for k in range(1, 5))
        out += struct.pack("<Q", 1 if verify(h, r, s, qx, qy) else 0)
    return out
