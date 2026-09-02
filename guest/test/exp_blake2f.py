"""Oracle for t_blake2f.pnk: 64 bytes per 213-byte record."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
import pyref


def expected(blob):
    return b"".join(pyref.blake2f(blob[i:i + 213]) for i in range(0, len(blob) - 212, 213))
