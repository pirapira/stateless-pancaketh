# Run the flapjack-compiled guest under ziskemu and produce a ZisK proof

This walks through emulating the guest with `ziskemu` — for step counts,
and as a cheap preliminary check before the much more expensive
`cargo-zisk prove` — and then generating an actual STARK proof of a real
execution with `cargo-zisk prove`, with the guest compiled by `flapjack`
(the Lean 4 port of the Pancake compiler, `lake exe flapjack-compile`). It
starts with a tiny example (`hello.pnk`) to validate the pipeline cheaply,
then does the same with an EEST test fixture (a synthetic single-block,
single-transaction test case, not a chain block).

Follow [README.md's "Quick start"](../README.md#quick-start) first. This
document assumes it has already been run: submodules initialized, `lake`
and `spike_run` built, and `tools/make-inputs.sh 50` plus
`tools/build_both.sh` already producing `work/inputs/manifest.tsv`,
`guest/build/guest.elf`, and `guest/build/guest-accel.elf`.

## Prerequisites

A ZisK toolchain installed via `ziskup` (https://ziskup.zisk.tech):
`ziskup -v 0.18.0 --provingkey`, then `cargo-zisk check-setup` (it
regenerates constant-tree files for a new key on first run, which takes a
couple of minutes). Two `ziskup` gotchas hit while preparing this
document, worth knowing before you run it:

* `ziskup --provingkey` with no `-v` installs the latest release first,
  silently swapping out a pinned older `ziskemu`/`cargo-zisk`. Always pass
  `-v <version>`.
* The installer's "Configuring CPU binaries" step is unreliable when
  switching versions in an existing `~/.zisk`: it can leave `ziskemu`
  updated but `cargo-zisk` on the old version (`cargo-zisk --version` will
  show it). If so, the correctly-versioned binary is already on disk as
  `~/.zisk/bin/cargo-zisk-cpu`; `cp ~/.zisk/bin/cargo-zisk-cpu
  ~/.zisk/bin/cargo-zisk` fixes it without a full reinstall.

Versions used for the run recorded below:

| Component | Version / commit |
| --- | --- |
| `ziskemu` | 0.18.0 (790f9e2, 2026-05-15) |
| `cargo-zisk` | 0.18.0 (790f9e2, 2026-05-15) |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| EEST fixtures | `tests-zkevm@v0.6.2` |
| Host | Ubuntu 24.04.5, 32 cores |

**Proving is CPU-heavy** (the fixture run below used all cores at ~100+
CPU-minutes of user time over 5-6 minutes wall-clock). Run `cargo-zisk
prove`/`execute` under `nice` so it does not starve other work on a shared
machine, as done in every command below.

## Build `hello.elf`

Quick start already builds `guest/build/guest.elf` and
`guest/build/guest-accel.elf`, and its `work/inputs/manifest.tsv` (50
fixtures) already includes fixture 00000: `tools/make-inputs.sh`'s fixture
selection is sorted, so `--limit 1` and `--limit 50` agree on which fixture
comes first. The one artifact `tools/build_both.sh` doesn't build is this
walkthrough's small example:

```bash
guest/build.sh guest/src/hello.pnk guest/build/hello.elf
```

It builds in well under a second. (The 40 static-analysis warnings
`flapjack-compile` prints while Quick start builds `main.pnk` are
non-fatal and expected, not specific to this walkthrough.)

## Small example: `hello.pnk`

An 8-byte input (`ziskemu` requires input length to be a multiple of 8):

```bash
printf 'hello\0\0\0' > /tmp/hello.input
~/.zisk/bin/ziskemu -e guest/build/hello.elf -i /tmp/hello.input -o /tmp/hello.out -m
```

Recorded result: **1,032 steps**.

Generate and verify a proof (`-o` is a single output file; `prove` always
produces one aggregated, fixed-size proof):

```bash
time nice cargo-zisk prove -e guest/build/hello.elf -i /tmp/hello.input \
  -l -o work/proof-hello.json -y
cargo-zisk verify -p work/proof-hello.json
```

Recorded result: 11 AIR instances (Main, Rom, Binary, BinaryExtension,
MemAlignWriteByte, Mem, InputData, RomData, SpecifiedRanges, VirtualTable0/1)
folded into one **Vadcop Final** proof, verified in-process (`-y`) and again
standalone (`verify`, 70ms); contributions 31.1s, inner proofs 172.5s, final
aggregation 9.3s, **3m43s** wall including proving-key load, **376 KB
(375,809 bytes)** proof file.

## EEST test fixture 00000

EEST fixture 00000
(`blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_authority_is_recipient.json`).
This uses the **accelerated** guest (`guest-accel.elf`, already built by
Quick start's `tools/build_both.sh`) throughout — it's the guest anyone
proving a real block cares about; see
[docs/ZISK-PROVE-BLOCK-FLAPJACK.md](ZISK-PROVE-BLOCK-FLAPJACK.md) for the
real-block pipeline.

```bash
INPUT=work/inputs/00000_test_account_write_authority_is_recipient_fork_Amsterdam-blockchain_test_from_state_test-non-zer.input
time ~/.zisk/bin/ziskemu -e guest/build/guest-accel.elf -i "$INPUT" -o /tmp/block00000.out -m
```

Recorded result: **2,584,624 ZisK steps**, and `PASS(full)` per
`tools/eest-run.py`'s classification against the Python oracle.

```bash
time nice cargo-zisk prove -e guest/build/guest-accel.elf -i "$INPUT" \
  -l -o work/proof-block00000-accel.json -y
cargo-zisk verify -p work/proof-block00000-accel.json
```

Recorded result: 15 AIR instances (one each of Main, Rom, Binary,
BinaryExtension, Arith, ArithEq, Keccakf, Sha256f, MemAlign, Mem, InputData,
RomData, SpecifiedRanges, VirtualTable0/1) folded into one Vadcop Final
proof; contributions 43.6s, inner proofs 244.4s, final aggregation 6.8s,
**5m7s** wall clock for the whole `prove` invocation (including
proving-key load), **376 KB (375,809 bytes)** proof file (identical size
to `hello.pnk`'s — the aggregated proof is fixed-size regardless of the
underlying execution length), verified standalone in 75ms.

## Notes

* `-l/--emulator` and `-s/--asm` are mutually exclusive; this guest is a raw
  RISC-V ELF (not a ZisK SDK Rust program), so there is no `--asm` build to
  use — always pass `-l`.
* `-o` takes a single output file path; `prove` always aggregates into one
  Vadcop Final proof, and `cargo-zisk verify -p <that file>` works correctly
  and quickly.
* Proving cost is dominated by the fixed per-AIR setup (contributions/inner-
  proof machinery), not step count: 1,032 steps (`hello.pnk`) and 2.58M
  steps (the fixture, accelerated guest) differ by three orders of
  magnitude in steps but under 1.5x in proving time (3m43s vs. 5m7s wall),
  because both stay within a handful of AIR instances of the fixed
  proving-key size.

For the same pipeline against a real chain block instead of a synthetic
EEST fixture, see
[docs/ZISK-PROVE-BLOCK-FLAPJACK.md](ZISK-PROVE-BLOCK-FLAPJACK.md).
