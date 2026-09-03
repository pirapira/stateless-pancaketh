#!/usr/bin/env bash
# build.sh <prog.pnk> <out.elf>
# Pancake source -> RISC-V ELF obeying the evm-asm stateless-guest contract.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
CAKE="${CAKE:-$HOME/cakeml/developers/bin/cake}"
AS="${RISCV_AS:-riscv64-unknown-elf-as}"
LD="${RISCV_LD:-riscv64-unknown-elf-ld}"
CPP="${CPP:-cpp}"
src="$1"; out="$2"
b="${out%.elf}"
# Sources are a cpp translation unit (#include / #define for constants).
cpp_debug_args=()
if [[ "${DEBUG:-0}" == "1" ]]; then
  cpp_debug_args=(-DGUEST_DEBUG)
fi
if [[ "${ACCEL:-0}" == "1" ]]; then
  cpp_debug_args+=(-DZISK_ACCEL)   # ZisK accelerator CSRs via FFI stubs in runtime/start.S
fi
"$CPP" "${cpp_debug_args[@]}" -P -w -nostdinc -I "$HERE/src" -x c "$src" | grep -v '^#' > "$b.pp.pnk"
"$CAKE" --pancake --target=riscv < "$b.pp.pnk" > "$b.cake.S"
# cake's .S uses C-preprocessor macros (cdecl, makesym); run cpp first.
"$CPP" -P -x assembler-with-cpp "$b.cake.S" > "$b.cake.s"
"$AS" -march=rv64imac -mno-relax -o "$b.cake.o" "$b.cake.s"
"$AS" -march=rv64imac_zicsr -mno-relax -o "$b.start.o" "$HERE/runtime/start.S"
"$LD" -Ttext=0x80000000 -Tdata=0xa0020000 -nostdlib --no-relax -e _start \
  -o "$out" "$b.start.o" "$b.cake.o"
echo "built $out"
