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

# ---- ZisK accelerator FFI stubs (ZISK_ACCEL builds) --------------------------
# Pancake `@keccakf(p, 200, p, 200)` arrives with a0 = p (absolute address of the
# 25*u64 state).  `csrrs x0, 0x800, a0` is ZisK's Keccak-f[1600] precompile;
# evm-asm's spike_run implements the same CSR (scripts/spike/zisk_accel.cc).
.globl ffikeccakf
ffikeccakf:
    csrrs x0, 0x800, a0

# FFI: BLS12-381 accelerator calls.  The first argument is the parameter
# block described by evm-asm/scripts/spike/zisk_accel.cc; each CSR mutates its
# output operand in place.  Keep these as tiny assembly bridges so the same
# Pancake source reaches both Spike's extension and ziskemu's implementation.
.globl ffibls_arith384
ffibls_arith384:
    .4byte 0x80b52073             # csrs 0x80B, a0 -> Arith384Mod
    ret

.globl ffibls_fp2_add
ffibls_fp2_add:
    .4byte 0x80e52073             # csrs 0x80E, a0 -> Fp2 add
    ret

.globl ffibls_fp2_sub
ffibls_fp2_sub:
    .4byte 0x80f52073             # csrs 0x80F, a0 -> Fp2 subtract
    ret

.globl ffibls_fp2_mul
ffibls_fp2_mul:
    .4byte 0x81052073             # csrs 0x810, a0 -> Fp2 multiply
    ret

.globl ffibls_g1_add
ffibls_g1_add:
    .4byte 0x80c52073             # csrs 0x80C, a0 -> G1 affine add
    ret

.globl ffibls_g1_dbl
ffibls_g1_dbl:
    .4byte 0x80d52073             # csrs 0x80D, a0 -> G1 affine double
    ret
