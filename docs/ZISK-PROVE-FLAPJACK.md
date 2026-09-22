# Run the flapjack-compiled guest under ziskemu and produce a ZisK proof

This walks through emulating the guest with `ziskemu` — for step counts,
and as a cheap preliminary check before the much more expensive
`cargo-zisk prove` — and then generating an actual STARK proof of a real
execution with `cargo-zisk prove`, with the guest compiled by `flapjack`
(the Lean 4 port of the Pancake compiler, `lake exe flapjack-compile`). It
starts with a tiny example (`hello.pnk`) to validate the pipeline cheaply,
then does the same with an EEST test fixture (a synthetic single-block,
single-transaction test case, not a chain block).

flapjack's output was checked for correctness against the guest's original
toolchain separately; see
[docs/FLAPJACK-CORRECTNESS.md](FLAPJACK-CORRECTNESS.md).

Follow `README.md`'s "Quick start" first. This document assumes it has
already been run: submodules initialized, `lake` and `spike_run` built,
and `tools/make-inputs.sh 50` plus `tools/build_both.sh` already producing
`work/inputs/manifest.tsv`, `guest/build/guest.elf`, and
`guest/build/guest-accel.elf`.

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

```bash
INPUT=work/inputs/00000_test_account_write_authority_is_recipient_fork_Amsterdam-blockchain_test_from_state_test-non-zer.input
time ~/.zisk/bin/ziskemu -e guest/build/guest.elf -i "$INPUT" -o /tmp/block00000.out -m
```

Recorded result: **18,864,486 ZisK steps**, 0.18s emulation time, and
`PASS(full)` per `tools/eest-run.py`'s classification against the Python
oracle. The accelerated guest (`guest-accel.elf`) runs the same fixture in
**2,584,624 steps**.

```bash
time nice cargo-zisk prove -e guest/build/guest.elf -i "$INPUT" \
  -l -o work/proof-block00000.json -y
```

Recorded result: 17 AIR instances (5× Main, plus Rom, 2× Binary, Arith,
BinaryExtension, MemAlign, Mem, InputData, RomData, SpecifiedRanges,
VirtualTable0/1) folded into one Vadcop Final proof, breakdown from the
`cargo-zisk` log:

| Stage | Time |
| --- | --- |
| Execute (witness/plan) | 0.73s |
| Calculating contributions | 54.3s |
| Generating inner proofs | 289.8s |
| Generating Vadcop final proof | 8.3s |
| Verifying Vadcop final proof (in-process) | 0.01s |
| **Total proving** | **~353s (~5m53s)** |

Wall clock for the whole `prove` invocation (including proving-key load):
**6m7s**; **376 KB (375,809 bytes)** proof file (identical size to `hello.pnk`'s — the
aggregated proof is fixed-size regardless of the underlying execution
length). Standalone `cargo-zisk verify -p work/proof-block00000.json`
confirms it in 68ms.

The same fixture with the accelerated guest:

```bash
time nice cargo-zisk prove -e guest/build/guest-accel.elf -i "$INPUT" \
  -l -o work/proof-block00000-accel.json -y
```

Recorded result: 15 AIR instances (one each of Main, Rom, Binary,
BinaryExtension, Arith, ArithEq, Keccakf, Sha256f, MemAlign, Mem, InputData,
RomData, SpecifiedRanges, VirtualTable0/1); contributions 43.6s, inner
proofs 244.4s, final aggregation 6.8s, **5m7s** wall, again a 376 KB
fixed-size proof, verified standalone in 75ms.

## Notes

* `-l/--emulator` and `-s/--asm` are mutually exclusive; this guest is a raw
  RISC-V ELF (not a ZisK SDK Rust program), so there is no `--asm` build to
  use — always pass `-l`.
* `-o` takes a single output file path; `prove` always aggregates into one
  Vadcop Final proof, and `cargo-zisk verify -p <that file>` works correctly
  and quickly.
* Proving cost is dominated by the fixed per-AIR setup (contributions/inner-
  proof machinery), not step count: 1,032 steps (`hello.pnk`) and 18.86M
  steps (the fixture) differ by four orders of magnitude in steps but well
  under 2x in proving time, because both stay within a handful of AIR
  instances of the fixed proving-key size.

For the same pipeline against a real chain block instead of a synthetic
EEST fixture, see
[docs/ZISK-PROVE-REAL-BLOCK-FLAPJACK.md](ZISK-PROVE-REAL-BLOCK-FLAPJACK.md).
