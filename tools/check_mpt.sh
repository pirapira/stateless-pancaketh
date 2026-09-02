#!/usr/bin/env bash
# check_mpt.sh [gen args...] -- generate MPT vectors with the execution-specs
# Python (tools/gen_mpt_vectors.py), build guest/test/t_mpt.pnk, run it under
# spike_run and compare the output with the oracle under the byte mask.
# Extra arguments are passed to the generator (e.g. --seed 7, --fixture PATH,
# --bench-sets 100 --bench-root 0 for instruction-count measurements).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
W="$ROOT/work/mpt"
mkdir -p "$W"
uv run --directory "$ROOT/evm-asm/execution-specs" python "$ROOT/tools/gen_mpt_vectors.py" "$W" "$@"
if [ ! -f "$W/t_mpt.elf" ] || [ "$ROOT/guest/src/mpt.pnk" -nt "$W/t_mpt.elf" ] || [ "$ROOT/guest/test/t_mpt.pnk" -nt "$W/t_mpt.elf" ]; then
  "$ROOT/guest/build.sh" "$ROOT/guest/test/t_mpt.pnk" "$W/t_mpt.elf" >/dev/null
fi
SPIKE_RUN="${SPIKE_RUN:-$ROOT/evm-asm/scripts/spike/spike_run}"
SPIKE_OUTPUT_LEN=65536 "$SPIKE_RUN" "$W/t_mpt.elf" "$W/mpt.input" "$W/mpt.out" 2> "$W/spike.log" || true
tail -n 1 "$W/spike.log"
python3 - "$W" <<'EOF'
import sys, os
w = sys.argv[1]
exp = open(os.path.join(w, "mpt.expected"), "rb").read()
mask = open(os.path.join(w, "mpt.mask"), "rb").read()
act = open(os.path.join(w, "mpt.out"), "rb").read()[:len(exp)]
bad = [i for i in range(len(exp)) if (exp[i] ^ (act[i] if i < len(act) else 0)) & mask[i]]
if not bad:
    print(f"PASS ({len(exp)} bytes)")
    sys.exit(0)
i = bad[0]
print(f"FAIL: first mismatch at byte {i} ({len(bad)} bytes differ)")
print("expected", exp[i - i % 8: i - i % 8 + 64].hex())
print("actual  ", act[i - i % 8: i - i % 8 + 64].hex())
sys.exit(1)
EOF
