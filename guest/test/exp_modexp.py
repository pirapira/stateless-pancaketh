"""Oracle for t_modexp.pnk: per record [4B blen][4B elen][4B mlen][base][exp][mod]
the mlen-byte big-endian pow(base, exp, mod) (zeros when mod == 0)."""
import struct


def expected(blob):
    out, i = [], 0
    while i + 12 <= len(blob):
        nb, ne, nm = struct.unpack(">III", blob[i:i + 12]); i += 12
        b = int.from_bytes(blob[i:i + nb], "big"); i += nb
        e = int.from_bytes(blob[i:i + ne], "big"); i += ne
        m = int.from_bytes(blob[i:i + nm], "big"); i += nm
        out.append((pow(b, e, m) if m else 0).to_bytes(nm, "big"))
    return b"".join(out)
