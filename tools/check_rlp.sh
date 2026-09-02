#!/usr/bin/env bash
# check_rlp.sh -- generate RLP test vectors, build guest/test/t_rlp.pnk, run it
# under spike_run and compare the output records with the Python oracle.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
W="$ROOT/work/rlp"
mkdir -p "$W"
if uv run --directory "$ROOT/evm-asm/execution-specs" python "$ROOT/tools/gen_rlp_vectors.py" "$W" 2>/dev/null; then
  :
else
  echo "(uv env unavailable; generating without ethereum_rlp cross-check)" >&2
  python3 "$ROOT/tools/gen_rlp_vectors.py" "$W"
fi
"$ROOT/guest/build.sh" "$ROOT/guest/test/t_rlp.pnk" "$W/t_rlp.elf" >/dev/null
SPIKE_RUN="${SPIKE_RUN:-$ROOT/evm-asm/scripts/spike/spike_run}"
SPIKE_OUTPUT_LEN=65536 "$SPIKE_RUN" "$W/t_rlp.elf" "$W/rlp.input" "$W/rlp.out" 2> "$W/spike.log" || true
tail -n 1 "$W/spike.log"
n=$(stat -c %s "$W/rlp.expected")
if cmp -n "$n" "$W/rlp.expected" "$W/rlp.out"; then
  echo "PASS ($((n / 32)) records)"
else
  echo "FAIL"; exit 1
fi
