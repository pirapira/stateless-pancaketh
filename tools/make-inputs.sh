#!/usr/bin/env bash
# make-inputs.sh [N] [extra converter args...]
# make-inputs.sh --all OUTDIR
# Convert EEST zkevm fixtures into guest inputs + manifest under work/inputs
# using evm-asm's converter (identical selection to evm-asm's harnesses).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
TAG="$(cat "$ROOT/evm-asm/scripts/eest-fixture-tag.txt")"
FX="${EEST_FIXTURES_DIR:-$ROOT/evm-asm/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"

usage() {
  cat <<'USAGE'
Usage:
  tools/make-inputs.sh [N] [converter options...]
  tools/make-inputs.sh --all OUTDIR

The --all form emits every stateless fixture block into OUTDIR, writes
relative paths in its manifest, and reuses OUTDIR when manifest.tsv already
exists.
USAGE
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

if [[ "${1:-}" == "--all" ]]; then
  shift
  [[ $# -ge 1 && -n "${1:-}" ]] || {
    echo "usage: $0 --all OUTDIR" >&2
    exit 2
  }
  OUT="$1"; shift
  [[ $# -eq 0 ]] || {
    echo "--all does not accept converter limits or filters" >&2
    exit 2
  }
  # The converter writes the output directory into manifest paths. Normalize
  # absolute OUTDIR arguments to a path relative to this repository so the
  # resulting manifest is portable.
  if [[ "$OUT" == /* ]]; then
    OUT="$(python3 -c 'import os, sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))' "$OUT" "$ROOT")"
  fi
  [[ -d "$FX" ]] || {
    echo "fixtures not found at $FX (run evm-asm/scripts/eest-fetch-fixtures.sh $TAG)" >&2
    exit 1
  }
  if [[ -f "$OUT/manifest.tsv" ]]; then
    echo "manifest already exists; reusing inputs in $OUT (no reconversion)"
    exit 0
  fi
  mkdir -p "$OUT"
  python3 "$ROOT/evm-asm/scripts/eest-stateless-to-input.py" \
    --fixtures-dir "$FX" --out-dir "$OUT" --limit 0
  echo "manifest: $OUT/manifest.tsv"
  exit 0
fi

N="${1:-50}"; shift || true
OUT="${OUT_DIR:-$ROOT/work/inputs}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run evm-asm/scripts/eest-fetch-fixtures.sh $TAG)" >&2; exit 1; }
rm -rf "$OUT"; mkdir -p "$OUT"
python3 "$ROOT/evm-asm/scripts/eest-stateless-to-input.py" --fixtures-dir "$FX" --out-dir "$OUT" --limit "$N" "$@"
echo "manifest: $OUT/manifest.tsv"
