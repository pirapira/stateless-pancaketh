# Plan / status

Milestones (each is measured with `tools/eest-run.py` on EEST fixtures):

- [x] **M0 pipeline**: Pancake → `cake --pancake --target=riscv` → ELF → `spike_run` / `ziskemu`.
      `guest/src/hello.pnk` echoes the input length (738 instructions).
- [ ] **M1 root+tail**: SSZ decode of `StatelessInput`, `hash_tree_root(NewPayloadRequest)`
      (sha256 merkleization), chain-config echo, malformed-input sentinel.
      Expect `[root/----/tail]` on every fixture, `PASS(malformed)` on reject fixtures.
- [ ] **M2 pre-execution validation**: RLP header decode, keccak block hash, header chain
      validation, chain-config activation check, witness MPT (keccak-keyed) pre-state.
- [ ] **M3 execution**: transactions (RLP, typed txs, secp256k1 recovery), EVM interpreter,
      gas, state tracker, block access list, receipts/bloom, post-state root
      (incremental MPT writes). `succ` starts matching on plain-transfer / simple-opcode fixtures.
- [ ] **M4 precompiles**: ecrecover, sha256, ripemd160, identity, modexp, bn254, blake2f,
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
