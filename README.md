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

| Path | What |
|------|------|
| `guest/src/*.pnk` | Pancake sources (single translation unit, assembled via `cpp`) |
| `guest/runtime/start.S` | bare-metal startup shim: sets `cml_heap/stack/stackend`, `_start`, `cml_exit`, FFI `halt`/`trap` |
| `guest/build.sh` | `.pnk` → `cake` → `.S` → `as`/`ld` → ELF |
| `tools/eest-run.py` | run an ELF over an EEST input manifest with `spike_run`, classify root/succ/tail, collect step counts |
| `tools/make-inputs.sh` | produce fixture inputs + manifest via evm-asm's converter |
| `evm-asm/`, `cakeml/` | git submodules |

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
guest/build.sh guest/src/guest.pnk guest/build/guest.elf
tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv
```

## Status / plan

See `PLAN.md`.
