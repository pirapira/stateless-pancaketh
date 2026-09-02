#!/usr/bin/env bash
# check_u256.sh [--count N] [--seed S] [--ops MASK]
# Build guest/test/t_u256.pnk, run it on generated vectors and compare the
# output byte-for-byte with the Python oracle.  --ops builds a variant with a
# cpp OPS_MASK (for instruction-cost measurement; comparison is skipped).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COUNT=60; SEED=1; OPS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --count) COUNT="$2"; shift 2;;
    --seed) SEED="$2"; shift 2;;
    --ops) OPS="$2"; shift 2;;
    *) echo "unknown arg $1" >&2; exit 2;;
  esac
done
W="$ROOT/work/u256"; mkdir -p "$W"
INP="$W/u256_${COUNT}_${SEED}.in"; EXP="$W/u256_${COUNT}_${SEED}.expected"
python3 "$ROOT/tools/gen_u256_vectors.py" --count "$COUNT" --seed "$SEED" "$INP" "$EXP"
SRC="$ROOT/guest/test/t_u256.pnk"; ELF="$W/t_u256.elf"
if [ -n "$OPS" ]; then
  SRC="$W/t_u256_ops.pnk"; ELF="$W/t_u256_ops.elf"
  printf '#define OPS_MASK %s\n#include "%s"\n' "$OPS" "$ROOT/guest/test/t_u256.pnk" > "$SRC"
fi
"$ROOT/guest/build.sh" "$SRC" "$ELF" > /dev/null
OUT="$W/t_u256.out"
SPIKE_OUTPUT_LEN=65536 "$ROOT/evm-asm/scripts/spike/spike_run" "$ELF" "$INP" "$OUT" 2>&1 | tail -1
if [ -n "$OPS" ]; then exit 0; fi
LEN=$(stat -c %s "$EXP")
head -c "$LEN" "$OUT" > "$W/t_u256.actual"
if cmp -s "$W/t_u256.actual" "$EXP"; then
  echo "PASS ($COUNT cases)"
else
  echo "FAIL: first differing byte:"; cmp "$W/t_u256.actual" "$EXP" || true
  python3 - "$W/t_u256.actual" "$EXP" "$INP" <<'EOF'
import sys, struct
act, exp, inp = (open(p, "rb").read() for p in sys.argv[1:4])
n = struct.unpack("<Q", inp[:8])[0]; blob = inp[8:8+n]
NRES = 22
shown = 0
for i in range(0, len(exp), 32):
    if act[i:i+32] != exp[i:i+32]:
        case, res = divmod(i // 32, NRES)
        a, b, m = (int.from_bytes(blob[case*96+k*32:case*96+(k+1)*32], "big") for k in range(3))
        print(f"case {case} result {res}: a={a:#x} b={b:#x} m={m:#x}")
        print(f"  expected {exp[i:i+32].hex()}\n  actual   {act[i:i+32].hex()}")
        shown += 1
        if shown >= 12: break
EOF
  exit 1
fi
