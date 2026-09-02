# start.S -- bare-metal runtime shim for a Pancake program running as a
# ZisK-style stateless guest under evm-asm's spike_run (or ziskemu).
#
# Contract (see evm-asm/scripts/spike/spike_run.cc):
#   input  at 0x40000000: [8B zero meta][8B LE len][blob]
#   output at 0xa0010000: SSZ StatelessValidationResult bytes
#   halt   : ecall with a7 = 93
#
# The Pancake program itself reads/writes those regions with shared-memory
# loads/stores (!ldw / !st8 ...), so the only FFI it needs is `halt`.
.option norelax
.option norvc
.section .text
.globl _start
_start:
    li   sp, 0xa00f0000          # small C-style stack for the shim / FFI stubs
    la   t0, cml_heap
    li   t1, 0xa0100000          # Pancake heap start (@base)
    sd   t1, 0(t0)
    la   t0, cml_stack
    li   t1, 0xb0000000          # Pancake heap end / stack start
    sd   t1, 0(t0)
    la   t0, cml_stackend
    li   t1, 0xbf000000          # Pancake stack end
    sd   t1, 0(t0)
    call cml_main
    j    cml_exit

.globl cml_exit
cml_exit:
    li   a7, 93
    ecall
1:  j 1b

# FFI: @halt(...) -> clean halt.
.globl ffihalt
ffihalt:
    j    cml_exit

# FFI: @trap(...) -- signal an unrecoverable guest error; write a marker
# byte and halt so the harness sees a deterministic (wrong) output.
.globl ffitrap
ffitrap:
    li   t0, 0xa0010000
    li   t1, 0xEE
    sb   t1, 32(t0)
    j    cml_exit
