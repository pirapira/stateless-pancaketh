#!/usr/bin/env bash
# check_bn254.sh [--seed S] [--pairings N] [--only TYPES] [--steps]
# Generate alt_bn128 vectors (tools/gen_bn254_vectors.py, py_ecc oracle under the
# execution-specs uv env), build guest/test/t_bn254.pnk, run it under spike_run
# and compare the output records with the oracle.  --steps additionally times
# single-record inputs (ECADD, ECMUL, 1- and 2-pair pairing checks, empty).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SEED=1; PAIRINGS=-1; ONLY=""; STEPS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --seed) SEED="$2"; shift 2;;
    --pairings) PAIRINGS="$2"; shift 2;;
    --only) ONLY="$2"; shift 2;;
    --steps) STEPS=1; shift;;
    *) echo "unknown arg $1" >&2; exit 2;;
  esac
done
W="$ROOT/work/bn254"; mkdir -p "$W"
PY="uv run --directory $ROOT/evm-asm/execution-specs python"
INP="$W/bn254_${SEED}.in"; EXP="$W/bn254_${SEED}.expected"
$PY "$ROOT/tools/gen_bn254_vectors.py" --seed "$SEED" --pairings "$PAIRINGS" ${ONLY:+--only "$ONLY"} "$INP" "$EXP"
ELF="$W/t_bn254.elf"
"$ROOT/guest/build.sh" "$ROOT/guest/test/t_bn254.pnk" "$ELF" > /dev/null
SPIKE_RUN="${SPIKE_RUN:-$ROOT/evm-asm/scripts/spike/spike_run}"
OUT="$W/t_bn254.out"
SPIKE_OUTPUT_LEN=262144 "$SPIKE_RUN" "$ELF" "$INP" "$OUT" 2>&1 | tail -1
LEN=$(stat -c %s "$EXP")
head -c "$LEN" "$OUT" > "$W/t_bn254.actual"
if cmp -s "$W/t_bn254.actual" "$EXP"; then
  echo "PASS"
else
  echo "FAIL:"
  $PY - "$W/t_bn254.actual" "$EXP" "$INP" <<'EOF'
import sys, struct
act, exp, inp = (open(p, "rb").read() for p in sys.argv[1:4])
n = struct.unpack("<Q", inp[:8])[0]; blob = inp[8:8+n]
pos = opos = 0; idx = 0; shown = 0
while pos < len(blob):
    ty, ln = struct.unpack("<QQ", blob[pos:pos+16]); pl = blob[pos+16:pos+16+ln]
    ety, eln = struct.unpack("<QQ", exp[opos:opos+16])
    e = exp[opos+16:opos+16+eln]; a = act[opos+16:opos+16+eln]
    if act[opos:opos+16] != exp[opos:opos+16] or a != e:
        print(f"record {idx} type {ty} len {ln}: input {pl.hex()[:160]}{'...' if ln > 80 else ''}")
        print(f"  expected {e.hex()}\n  actual   {a.hex()}")
        shown += 1
        if shown >= 6: break
    pos += 16 + ((ln + 7) & ~7); opos += 16 + ((eln + 7) & ~7); idx += 1
EOF
  exit 1
fi
if [ -n "$STEPS" ]; then
  $PY - "$W" "$ROOT" <<'EOF'
import sys, struct, os
sys.path.insert(0, os.path.join(sys.argv[2], "tools"))
from gen_bn254_vectors import frame, pad8, g1_bytes, g2_bytes, neg_bytes_g1, C, R, be32
w = sys.argv[1]
g, q = g1_bytes(C.G1), g2_bytes(C.G2)
cases = {
  "empty": b"",
  "ecadd": frame(1, g + g1_bytes(C.multiply(C.G1, 2))),
  "ecmul_full_scalar": frame(2, g + be32(R - 1)),
  "pairing_1pair": frame(3, g + q),
  "pairing_2pairs": frame(3, g + q + neg_bytes_g1(g) + q),
  "pairing_2pairs_infG1": frame(3, bytes(64) + q + bytes(64) + q),
  "pairing_invalid_len": frame(3, b"\x00" * 191),
}
for name, blob in cases.items():
    open(os.path.join(w, f"step_{name}.in"), "wb").write(struct.pack("<Q", len(blob)) + pad8(blob))
print(" ".join(cases))
EOF
  for f in "$W"/step_*.in; do
    n=$(basename "$f" .in); n=${n#step_}
    printf '%-24s ' "$n"; SPIKE_OUTPUT_LEN=4096 "$SPIKE_RUN" "$ELF" "$f" "$W/step.out" 2>&1 | tail -1
  done
fi
