#!/usr/bin/env bash
# check_all.sh -- run the repository's unit, vector, and EEST checks.
#
# Every command is captured in work/check-all/*.log so a noisy oracle or
# emulator cannot hide the one-line PASS/FAIL status printed by this script.
# The script deliberately continues after a failure and exits non-zero if any
# check failed.
set -u -o pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

LOG_DIR="${CHECK_ALL_LOG_DIR:-$ROOT/work/check-all}"
mkdir -p "$LOG_DIR"

PASS_COUNT=0
FAIL_COUNT=0

run_check() {
  local name="$1"
  shift
  local slug
  slug="$(printf '%s' "$name" | tr -cs '[:alnum:]._-' '_')"
  local log="$LOG_DIR/$slug.log"
  local rc
  if "$@" >"$log" 2>&1; then
    printf 'PASS  %s\n' "$name"
    PASS_COUNT=$((PASS_COUNT + 1))
  else
    rc=$?
    printf 'FAIL  %s (exit %s; see %s)\n' "$name" "$rc" "$log"
    FAIL_COUNT=$((FAIL_COUNT + 1))
  fi
}

# The EEST conversion is intentionally conditional: a checkout with an
# existing manifest must be reproducible, while a fresh checkout gets the
# same small baseline used by the README.  Override the latter with
# CHECK_ALL_INPUT_COUNT when a larger sweep is desired.
INPUT_MANIFEST="$ROOT/work/inputs/manifest.tsv"
if [[ ! -f "$INPUT_MANIFEST" ]]; then
  run_check "generate EEST inputs" \
    "$ROOT/tools/make-inputs.sh" "${CHECK_ALL_INPUT_COUNT:-30}"
fi

if [[ -f "$INPUT_MANIFEST" ]]; then
  UNIT_INPUT="$(awk -F '\t' 'NF >= 2 { print $2; exit }' "$INPUT_MANIFEST")"
  if [[ "$UNIT_INPUT" != /* ]]; then
    UNIT_INPUT="$ROOT/$UNIT_INPUT"
  fi
  run_check "locate unit-test input" test -f "$UNIT_INPUT"
else
  UNIT_INPUT="$ROOT/work/check-all/missing.input"
  run_check "locate unit-test input" false
fi

# t_globals has no data dependency, but unit.py still needs a framed input.
# The expected pointers use the fixed heap base from guest/runtime/start.S;
# alloc(64) and alloc(1000000) are both already 8-byte aligned.
run_check "unit t_globals" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_globals.pnk" "$UNIT_INPUT" \
  "struct.pack('<QQQQQQQQ', 0xa0100000, 0xa0100000, 0xa0100040, 1234, 5678, 0xa0100040, 0xa01f4280, 1234)"

# t_keccak exercises the full input, empty input, the 200/136/135-byte
# boundaries, and an unaligned slice.  Keep the expression beside the test
# invocation because this test intentionally has no separate oracle file.
run_check "unit t_keccak" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_keccak.pnk" "$UNIT_INPUT" \
  "keccak256(blob) + keccak256(b'') + keccak256(blob[:min(len(blob),200)]) + keccak256(blob[:min(len(blob),136)]) + keccak256(blob[:min(len(blob),135)]) + keccak256(blob[1:1+min(len(blob),201)-1])"

# t_sha256 checks SHA-256(input), followed by sha256_pair(digest,digest).
run_check "unit t_sha256" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_sha256.pnk" "$UNIT_INPUT" \
  "hashlib.sha256(blob).digest() + hashlib.sha256(hashlib.sha256(blob).digest() * 2).digest()"

# The remaining fixture-backed unit tests use the first converted EEST input
# and their checked-in Python expected(blob) functions.
run_check "unit t_header" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_header.pnk" "$UNIT_INPUT" @guest/test/exp_header.py
run_check "unit t_tx" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_tx.pnk" "$UNIT_INPUT" @guest/test/exp_tx.py
run_check "unit t_tx_neg" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_tx_neg.pnk" "$UNIT_INPUT" @guest/test/exp_tx_neg.py
run_check "unit t_ripemd160" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_ripemd160.pnk" "$UNIT_INPUT" @guest/test/exp_ripemd160.py

# t_blake2f and t_modexp share the precompile vector generator.  The larger
# output buffer is required by the modexp cases and is harmless for blake2f.
PRE_DIR="$ROOT/work/check-all/pre"
run_check "generate precompile vectors" \
  python3 "$ROOT/tools/gen_pre_vectors.py" "$PRE_DIR"
run_check "unit t_blake2f" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_blake2f.pnk" "$PRE_DIR/blake2f.in" @guest/test/exp_blake2f.py
run_check "unit t_modexp" \
  env SPIKE_OUTPUT_LEN=65536 "$ROOT/tools/unit.py" \
  "$ROOT/guest/test/t_modexp.pnk" "$PRE_DIR/modexp.in" @guest/test/exp_modexp.py

# t_m1_all is the aggregate M1 source (it has no standalone expected(blob)
# oracle); compiling it is the appropriate smoke check, while the main guest
# build below supplies the end-to-end EEST executable.
run_check "compile t_m1_all" \
  "$ROOT/guest/build.sh" "$ROOT/guest/test/t_m1_all.pnk" \
  "$LOG_DIR/t_m1_all.elf"
run_check "build main guest" \
  "$ROOT/guest/build.sh" "$ROOT/guest/src/main.pnk" \
  "$LOG_DIR/guest.elf"

# These scripts own their generators, expected-data comparisons, and the
# SPIKE_OUTPUT_LEN=65536 setting needed for their largest outputs.
run_check "vector check_u256" "$ROOT/tools/check_u256.sh"
run_check "vector check_rlp" "$ROOT/tools/check_rlp.sh"
run_check "vector check_mpt" "$ROOT/tools/check_mpt.sh"
run_check "vector check_secp256k1" "$ROOT/tools/check_secp256k1.sh"
run_check "vector check_p256" "$ROOT/tools/check_p256.sh"

# Run every converted EEST manifest, including sampled manifests such as
# work/inputs-rand/manifest.tsv when they are present.  Relative input paths
# in the manifests are valid because the script changed to the repository
# root above.  Set CHECK_ALL_EEST_JOBS to override eest-run.py's default.
manifest_found=0
for manifest in "$ROOT"/work/inputs*/manifest.tsv; do
  [[ -f "$manifest" ]] || continue
  manifest_found=1
  manifest_name="$(basename "$(dirname "$manifest")")"
  eest_args=(--quiet-passes --out-dir "$LOG_DIR/eest-$manifest_name")
  if [[ -n "${CHECK_ALL_EEST_JOBS:-}" ]]; then
    eest_args+=(--jobs "$CHECK_ALL_EEST_JOBS")
  fi
  run_check "EEST $manifest_name" \
    "$ROOT/tools/eest-run.py" "$LOG_DIR/guest.elf" "$manifest" \
    "${eest_args[@]}"
done
if [[ "$manifest_found" -eq 0 ]]; then
  run_check "EEST manifests available" false
fi

printf '%s\n' '----------------------------------------'
printf 'Summary: %s PASS, %s FAIL\n' "$PASS_COUNT" "$FAIL_COUNT"
if [[ "$FAIL_COUNT" -ne 0 ]]; then
  exit 1
fi
