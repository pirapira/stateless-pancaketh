"""Oracle for t_ripemd160.pnk."""
import hashlib


def expected(blob):
    k = min(len(blob), 150)
    out = b"".join(hashlib.new("ripemd160", blob[:i]).digest() for i in range(k + 1))
    return out + hashlib.new("ripemd160", blob).digest()
