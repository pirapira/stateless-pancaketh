#!/usr/bin/env bash
# make-inputs.sh [N] [extra converter args...]
# Convert EEST zkevm fixtures into guest inputs + manifest under work/inputs
# using evm-asm's converter (identical selection to evm-asm's harnesses).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
N="${1:-50}"; shift || true
TAG="$(cat "$ROOT/evm-asm/scripts/eest-fixture-tag.txt")"
FX="${EEST_FIXTURES_DIR:-$ROOT/evm-asm/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
OUT="${OUT_DIR:-$ROOT/work/inputs}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run evm-asm/scripts/eest-fetch-fixtures.sh $TAG)" >&2; exit 1; }
rm -rf "$OUT"; mkdir -p "$OUT"
python3 "$ROOT/evm-asm/scripts/eest-stateless-to-input.py" --fixtures-dir "$FX" --out-dir "$OUT" --limit "$N" "$@"
echo "manifest: $OUT/manifest.tsv"
