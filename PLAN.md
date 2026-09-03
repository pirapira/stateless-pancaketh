# Plan / status

Milestones (each is measured with `tools/eest-run.py` on EEST fixtures):

- [x] **M0 pipeline**: Pancake → `cake --pancake --target=riscv` → ELF → `spike_run` / `ziskemu`.
      `guest/src/hello.pnk` echoes the input length (738 instructions).
- [x] **M1 root+tail**: SSZ decode of `StatelessInput`, `hash_tree_root(NewPayloadRequest)`
      (sha256 merkleization), chain-config echo, malformed-input sentinel.
      Expect `[root/----/tail]` on every fixture, `PASS(malformed)` on reject fixtures.
- [x] **M2 pre-execution validation**: RLP header decode, keccak block hash, header chain
      validation, chain-config activation check, witness MPT (keccak-keyed) pre-state.
- [x] **M3 execution** (2026-09-02: 173/200 random fixtures PASS(full); all remaining failures are unimplemented precompiles): transactions (RLP, typed txs, secp256k1 recovery), EVM interpreter,
      gas, state tracker, block access list, receipts/bloom, post-state root
      (incremental MPT writes). `succ` starts matching on plain-transfer / simple-opcode fixtures.
- [ ] **M4 precompiles** (done: ecrecover, sha256, ripemd160, identity, modexp, alt_bn128 add/mul/pairing,
      blake2f, p256verify, BLS12-381 #27; open: KZG point evaluation #28; alt_bn128 is correct but slow #29).
- [ ] **M5 performance**: instruction counts vs evm-asm codegen guest / reth
      (spike minstret and ziskemu steps), profile hot spots.
- [ ] **M6 ZisK accelerators**: keccak/sha256/secp256k1/bn254/bls12/blake2 via ZisK CSRs behind Pancake
      FFI stubs (`ACCEL=1` build; keccak done 2026-09-03, see the M6 section).

## Pancake constraints that shape the port

* Only 64-bit words; ops: `+ - * & | ^ << >> >>> #>>`, comparisons; **no div/mod**,
  no 64x64→128 multiply. 256-bit arithmetic is built from 32-bit half-limbs;
  division is long division.
* No heap allocator: a bump allocator over the Pancake heap (`@base..@top`), no freeing
  except region resets (per-tx / per-call scratch marks).
* Struct values (`<a,b,c,d>` with shape `{1,1,1,1}`) are passed in registers/stack —
  used for U256 to keep arithmetic out of memory.
* No hex literals; no `#include` — the build runs `cpp` over the sources so constants
  and includes are preprocessor macros.
* Input is read directly from `0x40000000` with shared-memory loads and copied into
  the heap once; output is written with shared-memory stores to `0xa0010000`.

## Correspondence with SpecRef

Each Pancake source file names the SpecRef Lean module it ports; function names
follow the Lean/Python names so the "Pancake ≡ SpecRef" argument can be made
function by function.

The deliberate numeric-width and saturation boundaries are catalogued in
[docs/ENVELOPE.md](docs/ENVELOPE.md).

## M6: ZisK precompile acceleration (investigated 2026-09-03; proof of concept landed)

**Mechanism.** ZisK exposes its accelerators as custom CSRs: the guest executes `csrrs x0, <csr>, <reg>`
where `<reg>` holds the address of an 8-byte-aligned parameter block; ziskemu transpiles the instruction
into a precompiled op (one step, fixed cost), and evm-asm's `scripts/spike/spike_run` registers
`scripts/spike/zisk_accel.cc`, a SPIKE extension implementing the same 17 CSRs, so the accelerated guest
runs byte-identically under spike_run and ziskemu (evm-asm's `parity-check.sh` is the model for our gate).
Ids (`~/zisk/definitions/src/syscall.rs`), costs (`~/zisk/core/src/zisk_ops_costs.rs`; an ordinary
instruction costs ~114 on our guest), and parameter layouts (`zisk_accel.cc`, all limbs LE u64):

| CSR | op | cost | param |
|---|---|---|---|
| 0x800 | Keccak-f[1600] | 75,550 | ptr → 25×u64 state, in place |
| 0x802 | arith256_mod: d = (a·b + c) mod m | 1,424 | ptr → 5 ptrs {a,b,c,m,d}, 4×u64 each; m ≠ 0 |
| 0x803 / 0x804 | secp256k1 affine add {p1,p2}→p1 / dbl in place | 1,424 | points = x‖y, 8×u64; add is undefined for p1 = ±p2 and for infinity (wrapper must branch) |
| 0x805 | SHA-256 compress | 8,712 | ptr → {state, block}; state = 4×u64 packing 8×u32 (word 2i in the low half of u64 i), block = 64 raw bytes |
| 0x806 / 0x807 | bn254 G1 affine add / dbl | 1,424 | as secp |
| 0x808–0x80a | bn254 Fp2 add / sub / mul | 1,424 | ptr → {f1, f2}; c0 at +0, c1 at +32; result in f1 |
| 0x80b | arith384_mod | 1,896 | as 0x802 with 6×u64 |
| 0x80c / 0x80d | bls12-381 G1 affine add / dbl | 1,896 | 96-byte points |
| 0x80e–0x810 | bls12-381 Fp2 add / sub / mul | 1,896 | c0 at +0, c1 at +48 |
| 0x819 | one BLAKE2b round | 4,920 | ptr → {round index, &v[16], &m[16]} |

Not in spike_run (ziskemu only): 0x801 arith256, 0x811 add256, 0x812 poseidon2, 0x813–0x816 DMA
memcpy/memcmp/inputcpy/memset, 0x817/0x818 secp256r1 add/dbl. They can be added to `zisk_accel.cc`
(one subclass each) if wanted; DMA and secp256r1 would help memcpy/memeq and p256verify.

**Pancake side.** A Pancake FFI call `@name(p1, n1, p2, n2)` reaches the symbol `ffiname` with
a0 = p1, a1 = n1, a2 = p2, a3 = n2 (absolute addresses; probed 2026-09-03), running on the shim's C stack.
An accelerator is therefore a 2-instruction stub in `guest/runtime/start.S` (`csrrs x0, CSR, a0; ret`;
the shim is assembled with `-march=rv64imac_zicsr`) plus `#ifdef ZISK_ACCEL` in the library; the software
implementation stays as the reference and the default build. `ACCEL=1 guest/build.sh ...` selects the
accelerated build. `alloc` returns 8-aligned pointers; data inside the input blob is not necessarily
aligned, so wrappers copy into scratch (the sponge already does).

**Proof of concept (keccak only, fixture 00000):** spike 21.13M → 19.05M instructions, ziskemu cost
2.479G → 2.259G (PRECOMPILES 20.0M = 265 permutations × 75,550), outputs identical on spike/ziskemu and
30/30 fixtures. Profile of the software guest on that fixture: secp256k1 field mul/sqr 58%, other secp 8%,
keccak-f 10%, sha256 5%, hashtable/memcpy/memeq ~3%.

**Verification stance.** Pancake's compiler theorem treats FFI calls as oracle events, so an accelerated
guest is still a verified compilation of its source; the obligation "CSR 0x8xx computes f" is the same
one evm-asm takes on in `Rv64/ZiskAccel.lean`. Keeping the software path compiled under `#ifndef
ZISK_ACCEL` gives a differential test: both builds must produce identical bytes on every fixture.

**Plan** (issues #37–#41; each PR keeps the default build unchanged and gates on
`tools/eest-run.py` 30/30 for both builds plus ziskemu parity of the accelerated one):
1. keccak — done (PoC above).
2. sha256 compress (0x805) in `sha256_block`/`sha256_pair`: ~1.1M instr/block → ~17k steps.
3. secp256k1: `fp_mul`/`fp_sqr`/scalar-field ops via arith256_mod, inversion by Fermat over arith256_mod,
   `ec_add_affine`/`ec_double` via 0x803/0x804 with a wrapper for infinity and p1 = ±p2. Expected
   ~14M → well under 0.5M instr per recovery, i.e. ~4× fewer steps per typical block.
4. alt_bn128: ECADD/ECMUL on 0x806/0x807; pairing with Fp via arith256_mod and Fp2 via 0x808–0x80a
   (Fp6/Fp12 towers in Pancake on top). Replaces the software optimisation (#29, closed).
5. BLS12-381 (#27) and KZG (#28): build the library on 0x80b–0x810 from the start.
6. blake2f on 0x819 (12 rounds × 1 step).
7. Tooling: `tools/check_all.sh` and `tools/bench.py` build and run both variants; add a ziskemu parity
   step for the accelerated ELF; bench table gets a "software vs accelerated" pair for the gist comparison.

## Status log
* 2026-09-02: full pipeline executes blocks; ~20M RISC-V instructions per small fixture block
  (sha256 merkleization ~2M, secp256k1 recovery ~7M per transaction, keccak ~8k/permutation).
  Debug bytes: output[69] = failure class (1 BlockErr, 2 HdrErr, 3 RlpErr, 4 MptErr, 5 StateErr,
  6 TxErr, 7 EvmErr), output[70] = code (see `throw` sites), output[100] = last stage marker.
* 2026-09-02: ziskemu runs the guest (output identical to spike). Fixture 00000 (1 tx, 5.8 KB input):
  24.1M ZisK steps, cost 2.75G (114 cost/step; the gist's reth is ~120 cost/step), 0.14 s emulation.
  Profile (spike PC histogram, `tools/spike_prof`): secp256k1 field mul/sqr ~47%, sha256 ~21%
  (before zero-hash precomputation), keccak ~8%. The gist's devnet-7 block 115260 input is not in
  this checkout; `tools/eest-run.py --ziskemu` reports ZisK steps for any manifest.

* 2026-09-03: merged the 13 codex PRs for issues #1–#13 (debug gating, shadowing, manifest paths, tests,
  check_all.sh, byte-helper/htab speedups, merge sort, scratch-buffer init, docs, eest-run histogram/filters,
  bench --profile) and landed alt_bn128 from the interrupted agents' branch: 30/30 baseline fixtures,
  185/200 random (remaining 15 = BLS12-381/KZG, fail 1/99). Unmerged partial work (BLS12-381 library,
  sha256 rewrite) is kept on branch `wip/agents-partial`; issues #27–#36 describe how to finish it (#29–#32, software crypto speedups, were closed on 2026-09-03 as superseded by M6).

* 2026-09-03: BLS12-381 (#27) uses the existing Spike/ZisK acceleration points for
  Fp, Fp2, and affine G1 operations, with the software implementation retained
  behind `#ifndef ZISK_ACCEL`.  The standalone differential is byte-identical:
  3,980,271,828 -> 207,495,435 Spike steps for the full vector stream; one
  pairing is 531,453,581 -> 28,242,021 steps.  The accelerated main guest passes
  all 1,015 BLS EEST blocks and the 30-fixture baseline; the 200-fixture sample
  is 198/200 with the two known KZG `1/99` failures.

## Workflow
Mechanical, well-specified tasks are filed as GitHub issues with the `mechanical` label
(https://github.com/pirapira/stateless-pancaketh/issues) for other agents; this session keeps the
spec-porting and semantic-debugging work.
PR checklist for those issues: read `guest/PANCAKE-NOTES.md`; add every new test to `tools/check_all.sh`;
report the `check_all.sh` summary and the 30/30 line of `tools/eest-run.py guest/build/guest.elf
work/inputs/manifest.tsv --quiet-passes`; performance PRs report before/after instruction counts.
Unit tests must call the same `*_init()` functions as `guest/src/main.pnk` (scratch buffers are never
allocated lazily).
