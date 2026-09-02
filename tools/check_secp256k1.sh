#!/usr/bin/env bash
# check_secp256k1.sh [--count N] [--seed S] [--simple] [--steps]
# Generate secp256k1 recovery vectors (tools/gen_secp_vectors.py, cross-checked
# against coincurve when the execution-specs uv env is available), build
# guest/test/t_secp256k1.pnk, run it under spike_run and compare the output
# byte-for-byte with the Python oracle.  --simple builds with -DSECP_SIMPLE_MUL
# (u256_mulmod field multiply).  --steps additionally runs the first KAT alone
# and prints the per-recovery instruction count.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COUNT=44; SEED=1; SIMPLE=""; STEPS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --count) COUNT="$2"; shift 2;;
    --seed) SEED="$2"; shift 2;;
    --simple) SIMPLE=1; shift;;
    --steps) STEPS=1; shift;;
    *) echo "unknown arg $1" >&2; exit 2;;
  esac
done
W="$ROOT/work/secp"; mkdir -p "$W"
INP="$W/secp_${COUNT}_${SEED}.in"; EXP="$W/secp_${COUNT}_${SEED}.expected"
if ! uv run --directory "$ROOT/evm-asm/execution-specs" python "$ROOT/tools/gen_secp_vectors.py" \
     --count "$COUNT" --seed "$SEED" "$INP" "$EXP" 2>/dev/null; then
  echo "(uv env unavailable; generating without the coincurve cross-check)" >&2
  python3 "$ROOT/tools/gen_secp_vectors.py" --count "$COUNT" --seed "$SEED" "$INP" "$EXP"
fi
SRC="$ROOT/guest/test/t_secp256k1.pnk"; ELF="$W/t_secp256k1.elf"
if [ -n "$SIMPLE" ]; then
  SRC="$W/t_secp256k1_simple.pnk"; ELF="$W/t_secp256k1_simple.elf"
  printf '#define SECP_SIMPLE_MUL 1\n#include "%s"\n' "$ROOT/guest/test/t_secp256k1.pnk" > "$SRC"
fi
"$ROOT/guest/build.sh" "$SRC" "$ELF" > /dev/null
SPIKE_RUN="${SPIKE_RUN:-$ROOT/evm-asm/scripts/spike/spike_run}"
OUT="$W/t_secp256k1.out"
SPIKE_OUTPUT_LEN=65536 "$SPIKE_RUN" "$ELF" "$INP" "$OUT" 2>&1 | tail -1
LEN=$(stat -c %s "$EXP")
head -c "$LEN" "$OUT" > "$W/t_secp256k1.actual"
if cmp -s "$W/t_secp256k1.actual" "$EXP"; then
  echo "PASS ($COUNT cases)"
else
  echo "FAIL: first differing byte:"; cmp "$W/t_secp256k1.actual" "$EXP" || true
  python3 - "$W/t_secp256k1.actual" "$EXP" "$INP" <<'EOF'
import sys, struct
act, exp, inp = (open(p, "rb").read() for p in sys.argv[1:4])
n = struct.unpack("<Q", inp[:8])[0]; blob = inp[8:8+n]
shown = 0
for c in range(len(exp) // 112):
    a, e = act[c*112:(c+1)*112], exp[c*112:(c+1)*112]
    if a != e:
        h, r, s = (blob[c*104+k*32:c*104+(k+1)*32].hex() for k in range(3))
        recid = struct.unpack("<Q", blob[c*104+96:c*104+104])[0]
        print(f"case {c}: hash={h} r={r} s={s} recid={recid}")
        print(f"  expected {e.hex()}\n  actual   {a.hex()}")
        shown += 1
        if shown >= 8: break
EOF
  exit 1
fi
if [ -n "$STEPS" ]; then
  # One successful recovery (the EEST KAT) alone: steps of a recovery + ecrecover.
  python3 - "$INP" "$W/one.in" <<'EOF'
import sys, struct
inp = open(sys.argv[1], "rb").read(); blob = inp[8:8+104]
open(sys.argv[2], "wb").write(struct.pack("<Q", 104) + blob)
EOF
  SPIKE_OUTPUT_LEN=4096 "$SPIKE_RUN" "$ELF" "$W/one.in" "$W/one.out" 2>&1 | tail -1 | sed 's/^/one KAT case (recover + ecrecover): /'
  SPIKE_OUTPUT_LEN=4096 "$SPIKE_RUN" "$ELF" "$ROOT/work/u256/empty.in" "$W/empty.out" 2>&1 | tail -1 | sed 's/^/empty input (fixed overhead): /'
fi
