"""pyref.py -- pure-Python reference functions for the unit-test harness.
keccak256 mirrors evm-asm/EvmAsm/Stateless/SpecRef/Crypto.lean (keccakPad,
keccakAbsorbBlock, keccak256): rate 136, pad 0x01..0x80, 32-byte digest."""

MASK64 = (1 << 64) - 1
RATE = 136

_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
# rotation offsets, indexed by x + 5*y
_ROT = [0, 1, 62, 28, 27,
        36, 44, 6, 55, 20,
        3, 10, 43, 25, 39,
        41, 45, 15, 21, 8,
        18, 2, 61, 56, 14]


def _rotl(v, r):
    return ((v << r) | (v >> (64 - r))) & MASK64 if r else v


def keccak_f1600(a):
    """Keccak-f[1600] on a list of 25 lanes (index x + 5*y)."""
    for rc in _RC:
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl(a[x + 5 * y], _ROT[x + 5 * y])
        a = [b[i] ^ ((~b[(i + 1) % 5 + 5 * (i // 5)]) & b[(i + 2) % 5 + 5 * (i // 5)]) & MASK64
             for i in range(25)]
        a[0] ^= rc
    return a


def keccak256(data: bytes) -> bytes:
    pad_len = RATE - (len(data) % RATE)
    if pad_len == 1:
        msg = data + b"\x81"
    else:
        msg = data + b"\x01" + b"\x00" * (pad_len - 2) + b"\x80"
    st = [0] * 25
    for off in range(0, len(msg), RATE):
        block = msg[off:off + RATE]
        for i in range(17):
            st[i] ^= int.from_bytes(block[8 * i:8 * i + 8], "little")
        st = keccak_f1600(st)
    return b"".join(lane.to_bytes(8, "little") for lane in st[:4])


if __name__ == "__main__":
    assert keccak256(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    assert keccak256(b"abc").hex() == "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
    print("pyref ok")


# ---- BLAKE2b compression (ethereum/crypto/blake2.py, class Blake2b) ----
_B2_IV = [0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
          0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]
_B2_SIGMA = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]
_B2_MIX = [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
           (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]


def _rotr64(x, n):
    return ((x >> n) | (x << (64 - n))) & MASK64


def blake2b_compress(rounds, h, m, t0, t1, f):
    """F compression; h, m lists of ints; returns 64 bytes (8 LE words)."""
    v = list(h) + list(_B2_IV)
    v[12] ^= t0
    v[13] ^= t1
    if f:
        v[14] ^= MASK64
    for r in range(rounds):
        s = _B2_SIGMA[r % 10]
        for i, (a, b, c, d) in enumerate(_B2_MIX):
            x, y = m[s[2 * i]], m[s[2 * i + 1]]
            v[a] = (v[a] + v[b] + x) & MASK64
            v[d] = _rotr64(v[d] ^ v[a], 32)
            v[c] = (v[c] + v[d]) & MASK64
            v[b] = _rotr64(v[b] ^ v[c], 24)
            v[a] = (v[a] + v[b] + y) & MASK64
            v[d] = _rotr64(v[d] ^ v[a], 16)
            v[c] = (v[c] + v[d]) & MASK64
            v[b] = _rotr64(v[b] ^ v[c], 63)
    return b"".join(((h[i] ^ v[i] ^ v[i + 8]).to_bytes(8, "little")) for i in range(8))


def blake2f(data):
    """blake2f precompile body on a 213-byte input (no length/flag checks)."""
    le = lambda o: int.from_bytes(data[o:o + 8], "little")
    rounds = int.from_bytes(data[:4], "big")
    h = [le(4 + 8 * i) for i in range(8)]
    m = [le(68 + 8 * i) for i in range(16)]
    return blake2b_compress(rounds, h, m, le(196), le(204), data[212])
