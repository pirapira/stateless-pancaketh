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
- [ ] **M4 precompiles** (done: ecrecover, sha256, identity): ecrecover, sha256, ripemd160, identity, modexp, bn254, blake2f,
      KZG point evaluation, BLS12-381.
- [ ] **M5 performance**: instruction counts vs evm-asm codegen guest / reth
      (spike minstret and ziskemu steps), profile hot spots.

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

## Workflow
Mechanical, well-specified tasks are filed as GitHub issues with the `mechanical` label
(https://github.com/pirapira/stateless-pancaketh/issues) for other agents; this session keeps the
spec-porting and semantic-debugging work.
