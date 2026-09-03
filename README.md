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
| `guest/build.sh`, `tools/build_both.sh` | software or software + `ZISK_ACCEL` builds |
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

## Tools

`guest/build.sh` accepts `DEBUG=1` to define `GUEST_DEBUG`; this preserves the
debug bytes at output offsets 69, 70, and 100. The default build omits those
stores. For example:

```bash
DEBUG=1 guest/build.sh guest/src/main.pnk guest/build/guest-debug.elf
```

`tools/build_both.sh` builds the two main guests used by differential checks:
`guest/build/guest.elf` is the software/reference build and
`guest/build/guest-accel.elf` is built with `ACCEL=1`. The software path remains
the default implementation; the accelerated path reaches the same precompile
acceleration points through Spike or ziskemu.

`tools/eest-run.py` uses Spike by default and supports several ways to narrow
down a failing sweep:

```bash
tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv --json work/run/results.json
tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv \
  --from-json work/run/results.json --fail-code 1/99
```

`--labels FILE` selects one manifest label per line (blank lines and lines
starting with `#` are ignored). A JSON run records the classification, debug
bytes, regions, and steps for each fixture. When failures exist, the runner
also prints a histogram grouped by result regions and debug failure code.

For the per-function profile, build the histogram-enabled Spike runner first,
then pass `--profile` to `tools/bench.py`:

```bash
tools/spike_prof/build.sh
tools/bench.py guest/build/guest.elf work/inputs/manifest.tsv --profile
```

`tools/check_all.sh` saves command output under `$CHECK_ALL_LOG_DIR` (default
`work/check-all`). `CHECK_ALL_INPUT_COUNT` controls the generated EEST sample
size, and `CHECK_ALL_EEST_JOBS` controls EEST parallelism. The alt_bn128
vector checker can run a quick ECADD/ECMUL smoke check with:

```bash
tools/check_bn254.sh --only 1,2
```

`check_all.sh` builds and checks both main guests with Spike, compares every
EEST output file byte-for-byte, and runs the unit/vector checks in both modes.
Because ziskemu is considerably slower than Spike, its accelerated parity gate
is opt-in: set `CHECK_ALL_ZISKE_PARITY=1` to run the accelerated guest under
ziskemu and compare those output files with the accelerated Spike run.

The checker also covers pairing and field-tower records; select those record
types with `--only` when running the slower software reference cases.

## Quick start

```bash
tools/make-inputs.sh 50                       # work/inputs/manifest.tsv
tools/build_both.sh                            # software + accelerated ELFs
tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv --quiet-passes
tools/eest-run.py guest/build/guest-accel.elf work/inputs/manifest.tsv --quiet-passes
```

## Testing

Run `tools/check_all.sh` for the unit/oracle tests, vector checks, and every
EEST manifest under `work/inputs*/manifest.tsv`. If `work/inputs/manifest.tsv`
is absent, it generates a 30-fixture baseline first; set
`CHECK_ALL_INPUT_COUNT` to choose another size. EEST results are checked
against the checked-in `tools/eest-baseline.json`: a fixture that passed in
the baseline must keep passing, while recorded failures are allowed only with
the same failure class/code. A better result passes with a refresh hint; use
`python3 tools/eest-baseline.py update MANIFEST.tsv RESULTS.json` after
reviewing the improvement. Each check gets a PASS/FAIL line, detailed output
is saved under `work/check-all/`, and regressions make the script exit
non-zero.

For performance work, `bench.py --elf2` prints paired software/accelerated
columns for Spike instructions, ZisK STEPS, TOTAL cost, and PRECOMPILES cost:

```bash
tools/bench.py guest/build/guest.elf work/inputs/manifest.tsv \
  --elf2 guest/build/guest-accel.elf --limit 3
```

For a single guest, or for performance work that needs a JSON snapshot, use:

```bash
tools/bench.py guest/build/guest.elf work/inputs/manifest.tsv --json work/bench/new.json
tools/bench_compare.py work/bench/baseline-main.json work/bench/new.json
```

The comparator prints per-fixture and total Spike instruction, ZisK step, and
ZisK cost deltas, and exits non-zero for an `ok` regression or more than 2%
Spike instruction growth (override with `--max-regress`). After reviewing a
new main baseline, regenerate it with the same `bench.py` command using
`work/bench/baseline-main.json`, force-add that ignored file with
`git add -f`, and paste the comparator output into the performance PR.

## Status / plan

See `PLAN.md`. Deliberate numeric-width and saturation boundaries are
documented in [docs/ENVELOPE.md](docs/ENVELOPE.md).
