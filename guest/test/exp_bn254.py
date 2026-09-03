"""Oracle for tools/unit.py: expected(blob) from tools/gen_bn254_vectors.py
(needs py_ecc: run unit.py under `uv run --directory evm-asm/execution-specs python`)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
from gen_bn254_vectors import expected  # noqa: E402,F401
