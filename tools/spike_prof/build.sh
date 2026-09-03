#!/usr/bin/env bash
# Build the PC-histogram SPIKE driver used by tools/bench.py --profile.
#
# The driver links the same SPIKE libraries and accelerator extension as
# evm-asm/scripts/spike/build.sh, but uses spike_prof.cc so SPIKE_PC_HIST can
# collect one sample per executed instruction.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd -- "$SCRIPT_DIR/../.." && pwd)"
cd "$SCRIPT_DIR"

SPIKE_SRC="${SPIKE_SRC:-$HOME/riscv-isa-sim}"
SPIKE_BUILD="${SPIKE_BUILD:-$SPIKE_SRC/build}"
CXX="${CXX:-g++}"
AS="${RISCV_AS:-riscv64-unknown-elf-as}"
LD="${RISCV_LD:-riscv64-unknown-elf-ld}"
OBJCOPY="${RISCV_OBJCOPY:-riscv64-unknown-elf-objcopy}"

for tool in "$CXX" "$AS" "$LD" "$OBJCOPY" xxd; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "tools/spike_prof/build.sh: missing tool: $tool" >&2
    exit 1
  }
done
[[ -d "$SPIKE_SRC/riscv" ]] || {
  echo "set SPIKE_SRC (no $SPIKE_SRC/riscv)" >&2
  exit 1
}
[[ -f "$SPIKE_BUILD/libriscv.a" ]] || {
  echo "build spike first (no $SPIKE_BUILD/libriscv.a)" >&2
  exit 1
}

INCS=(
  -I"$SPIKE_SRC"
  -I"$SPIKE_SRC/riscv"
  -I"$SPIKE_SRC/fesvr"
  -I"$SPIKE_SRC/softfloat"
  -I"$SPIKE_BUILD"
  -I.
)
CXX_STD=(-std=c++2a -O2 -Wall -Wno-unused-parameter)

# spike_prof.cc uses the same trap handler as spike_run.  Generate the header
# locally so a clean checkout needs no checked-in build products.
"$AS" -march=rv64imac_zicsr \
  -o handler.o "$ROOT/evm-asm/scripts/spike/handler.s"
"$LD" -Ttext=0x60000000 -e _handler -nostdlib \
  -o handler.elf handler.o
"$OBJCOPY" -O binary handler.elf handler.bin
xxd -i handler.bin > handler_bin.h

# Keep these flags and library order in sync with step 3 of
# evm-asm/scripts/spike/build.sh.
"$CXX" "${CXX_STD[@]}" "${INCS[@]}" \
  spike_prof.cc "$ROOT/evm-asm/scripts/spike/zisk_accel.cc" \
  "$SPIKE_BUILD"/libriscv.a "$SPIKE_BUILD"/libdisasm.a \
  "$SPIKE_BUILD"/libsoftfloat.a "$SPIKE_BUILD"/libfesvr.a \
  "$SPIKE_BUILD"/libfdt.a \
  -lpthread -lcrypto \
  -o spike_prof
chmod +x spike_prof
echo "built $SCRIPT_DIR/spike_prof"
