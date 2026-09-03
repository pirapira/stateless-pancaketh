# stateless-pancake

Experiment: an Ethereum **stateless guest** written in
[Pancake](https://cakeml.org/pancake) (the verified C-like language compiled
by the CakeML compiler) and run as a RISC-V zkVM guest, as an alternative
route to evm-asm's hand-written/codegen RV64 guest.

## Goal

1. Port `evm-asm/EvmAsm/Stateless/SpecRef` (the pure-Lean functional port of
   execution-specs' Amsterdam `run_stateless_guest`) to Pancake source in
   `guest/src/`.
2. Compile it with the **verified** `cake --pancake --target=riscv` compiler
   to an ELF that obeys the same guest contract as evm-asm's
   `stateless_guest` (input at `0x40000000`, output at `0xa0010000`, halt via
   `ecall a7=93`), so evm-asm's `spike_run` and `ziskemu` can run it unchanged.
3. Run it against the EEST `tests-zkevm` fixtures (same fixture selection as
   `evm-asm/scripts/eest-specref-check.sh`) and compare the output regions
   root / succ / tail exactly like that harness.
4. Measure instruction counts (`spike_run` minstret, ziskemu steps) and
   compare with the evm-asm codegen guest and reth, in the style of
   https://gist.github.com/pirapira/a5cc0088ade5ac31fcbed3b562e3e9b1 .

Trust story: the Pancake compiler is verified end-to-end (Pancake semantics →
RISC-V machine code), so the remaining verification obligation is
"Pancake source ≡ SpecRef", instead of proving a hand-written RV64 program.

## Layout

| Path | Ports (SpecRef Lean module) |
|------|------|
| `guest/src/lib/{mem,arith,htab}.pnk` | bump allocator, division, hash tables (Python dict/set stand-ins) |
| `guest/src/lib/{sha256,keccak}.pnk` | `Crypto.lean` |
| `guest/src/lib/u256.pnk` | 256-bit arithmetic (`InstructionsCore.lean` U256 semantics) |
| `guest/src/lib/rlp.pnk` | `EvmAsm/EL/RLP` (strict decode, encode) |
| `guest/src/lib/secp256k1.pnk` | `Secp256k1Recover.lean` |
| `guest/src/ssz.pnk` | `SszCodec.lean`, `Ssz.lean` (decode + hash_tree_root) |
| `guest/src/header.pnk` | `Stateless.lean` headers, `BlocksRlp.lean`, `Gas.lean` blob/base-fee rules |
| `guest/src/mpt.pnk` | `WitnessState.lean`, `IncrementalMpt*.lean` (node DB, trie read/write, roots) |
| `guest/src/tx.pnk` | `Transactions.lean` (5 tx types, signing hashes, intrinsic gas, sender recovery) |
| `guest/src/state.pnk` | `StateTracker.lean`, `WitnessReads.lean` (journal-based rollback) |
| `guest/src/bal.pnk` | `BlockAccessLists.lean` (EIP-7928 builder, encoding, hash) |
| `guest/src/evm.pnk`, `evm_calls.pnk` | `Vm.lean`, `InstructionsCore/Env.lean`, `Interpreter.lean` (frames, opcodes, calls, creates, EIP-7702) |
| `guest/src/precompiles*.pnk` | `Precompiles*.lean` |
| `guest/src/block.pnk` | bloom, receipts, requests, `WitnessStateRoot.lean` post-state root |
| `guest/src/fork.pnk` | `SeamShell.lean`, `Fork.lean`, `ElExecute.lean` (pre-checks, apply_body, post checks) |
| `guest/src/main.pnk` | `Guest.lean` `run_stateless_guest` |
| `guest/runtime/start.S` | bare-metal shim (`_start`, `cml_exit`, FFI `halt`/`trap`) |
| `guest/build.sh` | `cpp` → `cake --pancake --target=riscv` → `as`/`ld` → ELF |
| `guest/test/`, `tools/check_*.sh`, `tools/gen_*_vectors.py` | unit tests against Python oracles |
| `tools/eest-run.py` | EEST manifest runner (spike_run or `--ziskemu`), root/succ/tail classification, step counts |
| `tools/spike_prof/` | spike variant with a PC histogram + per-function aggregation |
| `guest/PANCAKE-NOTES.md` | Pancake language rules and project conventions (read before editing `.pnk`) |

Debug bytes in the output region (past the 69-byte result, ignored by the harness):
`[69]` failure class, `[70]` failure code (see `throw` sites in `fork.pnk`), `[100]` last stage marker.

## Toolchain

* `cake` (prebuilt, bootstrapped CakeML compiler with Pancake): `~/cakeml/developers/bin/cake`
  (or set `CAKE=`). Version pinned by the `cakeml` submodule.
* `riscv64-unknown-elf-{as,ld}` (Ubuntu `binutils-riscv64-unknown-elf`).
* `spike_run`: `SPIKE_SRC=~/riscv-isa-sim evm-asm/scripts/spike/build.sh`
  (needs a built riscv-isa-sim and `libssl-dev`).
* `ziskemu` (`~/.zisk/bin/ziskemu`) for ZisK step counts.
* Python oracle: `uv run --directory evm-asm/execution-specs python ...`.

## Quick start

```bash
tools/make-inputs.sh 50                       # work/inputs/manifest.tsv
guest/build.sh guest/src/main.pnk guest/build/guest.elf      # ~1-2 min in cake
tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv --quiet-passes
tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv --ziskemu   # ZisK steps
```

## Testing

Run `tools/check_all.sh` for the unit/oracle tests, vector checks, and every
EEST manifest under `work/inputs*/manifest.tsv`. If `work/inputs/manifest.tsv`
is absent, it generates a 30-fixture baseline first; set
`CHECK_ALL_INPUT_COUNT` to choose another size. Each check gets a PASS/FAIL
line, detailed output is saved under `work/check-all/`, and any failure makes
the script exit non-zero.

## Status / plan

See `PLAN.md`. Deliberate numeric-width and saturation boundaries are
documented in [docs/ENVELOPE.md](docs/ENVELOPE.md).
