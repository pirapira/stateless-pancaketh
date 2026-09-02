#!/usr/bin/env python3
"""unit.py TEST.pnk INPUT_FILE EXPECT_EXPR
Build a test Pancake program, run it on INPUT_FILE with spike_run and compare
the output bytes (as hex, truncated to expected length) with the hex string
produced by evaluating EXPECT_EXPR in Python (blob = input blob bytes without
the ziskemu framing; hashlib available)."""
import hashlib, os, struct, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPIKE_RUN = os.environ.get("SPIKE_RUN", os.path.join(ROOT, "evm-asm/scripts/spike/spike_run"))
test, inp, expr = sys.argv[1], sys.argv[2], sys.argv[3]
name = os.path.splitext(os.path.basename(test))[0]
bdir = os.path.join(ROOT, "work/unit"); os.makedirs(bdir, exist_ok=True)
elf = os.path.join(bdir, name + ".elf")
subprocess.check_call([os.path.join(ROOT, "guest/build.sh"), test, elf], stdout=subprocess.DEVNULL)
packed = open(inp, "rb").read()
n = struct.unpack("<Q", packed[:8])[0]; blob = packed[8:8+n]
out = os.path.join(bdir, name + ".out")
env = dict(os.environ); env.setdefault("SPIKE_OUTPUT_LEN", "4096")
log = subprocess.run([SPIKE_RUN, elf, inp, out], capture_output=True, text=True, env=env)
print(log.stderr.strip().splitlines()[-1] if log.stderr.strip() else f"rc={log.returncode}")
expected = eval(expr, {"blob": blob, "hashlib": hashlib, "struct": struct})
if isinstance(expected, bytes): expected = expected.hex()
actual = open(out, "rb").read()[:len(expected)//2].hex()
print("expected", expected); print("actual  ", actual)
print("PASS" if actual == expected else "FAIL"); sys.exit(0 if actual == expected else 1)
