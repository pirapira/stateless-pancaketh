import struct
def expected(blob):
    n = min(len(blob)//32, 150)
    d = {}
    for i in range(n): d[blob[i*32:i*32+32]] = i + 1000
    for i in range(n):
        if i % 4 == 0: d.pop(blob[i*32:i*32+32], None)
    for i in range(n):
        if i % 8 == 0: d[blob[i*32:i*32+32]] = i + 5000
    out = struct.pack('<Q', len(d))
    for i in range(n):
        k = blob[i*32:i*32+32]
        out += struct.pack('<Q', (1 | (d[k] << 8)) if k in d else 0)
    return out
