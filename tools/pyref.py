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
