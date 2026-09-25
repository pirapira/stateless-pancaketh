#!/usr/bin/env bash
# build.sh <prog.pnk> <out.elf>
# Pancake source -> RISC-V ELF obeying the evm-asm stateless-guest contract.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
CAKE="${CAKE:-$HOME/cakeml/developers/bin/cake}"
COMPILER="${COMPILER:-flapjack}"
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
if [[ "${ZISK_V1:-0}" == "1" ]]; then
  cpp_debug_args+=(-DZISK_V1)      # OUTPUT_ADDR moves for ZisK >=1.1.0-alpha; see config.h
fi
"$CPP" "${cpp_debug_args[@]}" -P -w -nostdinc -I "$HERE/src" -x c "$src" | grep -v '^#' > "$b.pp.pnk"
# COMPILER=flapjack (default) uses the Lean 4 port (lake exe flapjack-compile, pinned by
# the flapjack lake dependency); COMPILER=cake uses the bootstrapped/prebuilt cake binary
# instead, emitting the same cake-style assembly frame consumed below.
case "$COMPILER" in
  cake)
    "$CAKE" --pancake --target=riscv < "$b.pp.pnk" > "$b.cake.S"
    ;;
  flapjack)
    ppabs="$(cd "$(dirname "$b.pp.pnk")" && pwd)/$(basename "$b.pp.pnk")"
    (cd "$ROOT" && lake exe flapjack-compile --assembly "$ppabs") > "$b.cake.S"
    ;;
  *)
    echo "build.sh: unknown COMPILER='$COMPILER' (want 'cake' or 'flapjack')" >&2
    exit 1
    ;;
esac
# cake's .S uses C-preprocessor macros (cdecl, makesym); run cpp first.
"$CPP" -P -x assembler-with-cpp "$b.cake.S" > "$b.cake.s"
"$AS" -march=rv64imac -mno-relax -o "$b.cake.o" "$b.cake.s"
"$AS" -march=rv64imac_zicsr -mno-relax -o "$b.start.o" "$HERE/runtime/start.S"
# -Ttext=0x80000000 (default) puts the ELF/program headers in their own PT_LOAD
# segment just below .text, at 0x7ffff000, and produces an R+E .text segment.
# Both are fine for Spike (generic ELF loader) and ZisK 0.18.0, but ZisK
# >=1.x's stricter loader rejects the headers segment (outside its declared
# ROM range) and its riscv2zisk converter panics on an R+E .text segment
# once a second PT_LOAD segment (.data) is present (reported upstream).
# ZISK_V1=1 links with guest/runtime/zisk-strict.ld instead, which leaves the
# headers unmapped and makes .text execute-only (PF_X, no PF_R); it also
# passes __output_addr, matching config.h's ZISK_V1 OUTPUT_ADDR, for
# start.S's ffitrap (the only place outside config.h with this address).
if [[ "${ZISK_V1:-0}" == "1" ]]; then
  "$LD" -T "$HERE/runtime/zisk-strict.ld" --defsym=__output_addr=0xa0410000 \
    -nostdlib --no-relax -e _start -o "$out" "$b.start.o" "$b.cake.o"
else
  "$LD" -Ttext=0x80000000 -Tdata=0xa0020000 --defsym=__output_addr=0xa0010000 \
    -nostdlib --no-relax -e _start -o "$out" "$b.start.o" "$b.cake.o"
fi
echo "built $out"
