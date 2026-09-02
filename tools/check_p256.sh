#!/usr/bin/env bash
# check_p256.sh [--count N] [--seed S] [--define NAME]... [--steps]
# Generate P-256 verification vectors (tools/gen_p256_vectors.py, cross-checked
# against `cryptography` when the execution-specs uv env is available), build
# guest/test/t_p256.pnk, run it under spike_run and compare the output with
# the Python oracle byte-for-byte.  --define P256_SIMPLE_MUL builds the
# u256_mulmod field-multiply variant.  --steps also runs the first case (the
# EIP-7951 valid vector) alone and prints its instruction count.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COUNT=60; SEED=1; DEFS=""; STEPS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --count) COUNT="$2"; shift 2;;
    --seed) SEED="$2"; shift 2;;
    --define) DEFS="$DEFS $2"; shift 2;;
    --steps) STEPS=1; shift;;
    *) echo "unknown arg $1" >&2; exit 2;;
  esac
done
W="$ROOT/work/p256"; mkdir -p "$W"
INP="$W/p256_${COUNT}_${SEED}.in"; EXP="$W/p256_${COUNT}_${SEED}.expected"
if ! uv run --directory "$ROOT/evm-asm/execution-specs" python "$ROOT/tools/gen_p256_vectors.py" \
     --count "$COUNT" --seed "$SEED" "$INP" "$EXP" 2>/dev/null; then
  echo "(uv env unavailable; generating without the cryptography cross-check)" >&2
  python3 "$ROOT/tools/gen_p256_vectors.py" --count "$COUNT" --seed "$SEED" "$INP" "$EXP"
fi
SRC="$ROOT/guest/test/t_p256.pnk"; ELF="$W/t_p256.elf"
if [ -n "$DEFS" ]; then
  TAG=$(echo "$DEFS" | tr -s ' ' '_')
  SRC="$W/t_p256$TAG.pnk"; ELF="$W/t_p256$TAG.elf"
  : > "$SRC"
  for d in $DEFS; do printf '#define %s 1\n' "$d" >> "$SRC"; done
  printf '#include "%s"\n' "$ROOT/guest/test/t_p256.pnk" >> "$SRC"
fi
"$ROOT/guest/build.sh" "$SRC" "$ELF" > /dev/null
SPIKE_RUN="${SPIKE_RUN:-$ROOT/evm-asm/scripts/spike/spike_run}"
OUT="$W/t_p256.out"
SPIKE_OUTPUT_LEN=65536 "$SPIKE_RUN" "$ELF" "$INP" "$OUT" 2>&1 | tail -1
LEN=$(stat -c %s "$EXP")
head -c "$LEN" "$OUT" > "$W/t_p256.actual"
if cmp -s "$W/t_p256.actual" "$EXP"; then
  echo "PASS ($COUNT cases)"
else
  echo "FAIL: first differing byte:"; cmp "$W/t_p256.actual" "$EXP" || true
  python3 - "$W/t_p256.actual" "$EXP" "$INP" <<'PY'
import sys, struct
act, exp, inp = (open(p, "rb").read() for p in sys.argv[1:4])
n = struct.unpack("<Q", inp[:8])[0]; blob = inp[8:8+n]
shown = 0
for c in range(len(exp) // 8):
    a, e = act[c*8:(c+1)*8], exp[c*8:(c+1)*8]
    if a != e:
        f = [blob[c*160+k*32:c*160+(k+1)*32].hex() for k in range(5)]
        print(f"case {c}: hash={f[0]} r={f[1]} s={f[2]}\n  qx={f[3]} qy={f[4]}\n  expected {e.hex()} actual {a.hex()}")
        shown += 1
        if shown >= 8: break
PY
  exit 1
fi
if [ -n "$STEPS" ]; then
  python3 - "$INP" "$W/one.in" <<'PY'
import sys, struct
inp = open(sys.argv[1], "rb").read(); blob = inp[8:8+160]
open(sys.argv[2], "wb").write(struct.pack("<Q", 160) + blob)
PY
  SPIKE_OUTPUT_LEN=4096 "$SPIKE_RUN" "$ELF" "$W/one.in" "$W/one.out" 2>&1 | tail -1 | sed 's/^/one valid verification: /'
  SPIKE_OUTPUT_LEN=4096 "$SPIKE_RUN" "$ELF" "$ROOT/work/u256/empty.in" "$W/empty.out" 2>&1 | tail -1 | sed 's/^/empty input (fixed overhead): /'
fi
