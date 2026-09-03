"""Oracle for tools/unit.py and guest/test/t_bls12381.pnk."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
from gen_bls12381_vectors import expected  # noqa: E402,F401
