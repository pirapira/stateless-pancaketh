# Run the flapjack-compiled guest under ziskemu and produce a ZisK proof

This is [docs/ZISK-PROVE.md](ZISK-PROVE.md)'s pipeline (`ziskemu` step counts,
then an actual STARK proof with `cargo-zisk prove`) with the guest compiled
by `flapjack` (the Lean 4 port of the Pancake compiler,
`lake exe flapjack-compile`) instead of the bootstrapped/prebuilt `cake`
binary. It reuses that document's `hello.pnk` smoke test and EEST fixture
00000, and only replaces the compiler.

**Correctness first.** Before recording any of the ziskemu/proving numbers
below, the flapjack-compiled guest was checked against the `cake`-compiled
guest (built fresh from the same `guest/src`, non-`DEBUG`) on the 30-fixture
baseline (`work/inputs/manifest.tsv`):

* `guest.elf` (software) and `guest-accel.elf` (`ACCEL=1`): byte-identical
  Spike/ziskemu output and identical step counts on all 30/30 fixtures; the
  disassembled `.text` is byte-identical to `cake`'s output (only the ELF's
  non-code bytes, e.g. symbol-table ordering, differ); the two compilers emit
  the exact same 40 static-analysis warnings across the same 12 functions.
* `tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv` and the
  `guest-accel.elf` equivalent both report `30/30 PASS(full)` against the
  Python oracle for the flapjack build.

This is a new milestone: `flapjack-compile` could not build the full guest as
recently as the pin bumped in #97 (see the "Toolchain" section of
`README.md` for the issues that blocked it); at the pin used here it not only
builds but matches `cake` instruction-for-instruction on this guest.

## Prerequisites

Same as [docs/ZISK-PROVE.md](ZISK-PROVE.md), except the compiler:

* `flapjack` is a `lake` dependency of this repo (`lakefile.toml`'s
  `[[require]] name = "flapjack"`), pinned by commit; no separate checkout or
  bootstrap step is needed beyond `lake build` (which `lake exe
  flapjack-compile` triggers on first use). `guest/build.sh` picks it via
  `COMPILER=flapjack`; `COMPILER=cake` (the default) is unchanged.
* `riscv64-unknown-elf-{as,ld}` and `cpp` (Ubuntu `binutils-riscv64-unknown-elf`).
* A ZisK toolchain installed via `ziskup` (https://ziskup.zisk.tech), giving
  `~/.zisk/bin/ziskemu` and `~/.zisk/bin/cargo-zisk`, plus the proving key at
  `~/.zisk/provingKey` (`ziskup -v 0.16.0 --provingkey`; `cargo-zisk
  check-setup` confirms it loads). `ziskup --provingkey` alone reinstalls the
  *latest* ZisK version, not just the key — pass `-v` to stay on the version
  the rest of this repo's docs use.

Versions used for the run recorded below:

| Component | Version / commit |
| --- | --- |
| `ziskemu` | 0.16.0 (aacf0a7, 2026-03-12) |
| `cargo-zisk` | 0.16.0 (aacf0a7, 2026-03-12) |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `cake` (comparison reference only) | bootstrapped, CakeML `e8eca63` |
| `cakeml` submodule | `857f0d98da8f8a3580f34423338e697809308ede` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| EEST fixtures | `tests-zkevm@v0.6.2` |
| Host | Ubuntu 24.04.5, 32 cores |

**Proving is CPU-heavy** (the fixture run below used all cores at ~80+
CPU-minutes of user time over a few minutes wall-clock). Run `cargo-zisk
prove`/`execute` under `nice` so it does not starve other work on a shared
machine, as done in every command below.

## Fetch fixtures and build the guest with flapjack

```bash
TAG="$(cat evm-asm/scripts/eest-fixture-tag.txt)"
evm-asm/scripts/eest-fetch-fixtures.sh "$TAG"   # or copy an existing evm-asm/gen-out
tools/make-inputs.sh 1                          # work/inputs: just fixture 00000
mkdir -p guest/build
COMPILER=flapjack guest/build.sh guest/src/hello.pnk guest/build/hello.elf
COMPILER=flapjack guest/build.sh guest/src/main.pnk guest/build/guest.elf
ACCEL=1 COMPILER=flapjack guest/build.sh guest/src/main.pnk guest/build/guest-accel.elf
```

`guest/build.sh` for `main.pnk` with `COMPILER=flapjack` takes about 40s
(`flapjack-compile` + `as` + `ld`) the first time in a session (it includes
compiling flapjack itself via `lake`; a warm `lake` build cache brings the
compile step itself down to under a second); `hello.pnk` builds in well under
a second. `flapjack-compile` emits the same 40 static-analysis warnings on
`main.pnk` that `cake` does (non-fatal; see the "Correctness first" note
above), which is expected and not a build failure.

## Small example: `hello.pnk`

An 8-byte input (`ziskemu` requires input length to be a multiple of 8):

```bash
printf 'hello\0\0\0' > /tmp/hello.input
~/.zisk/bin/ziskemu -e guest/build/hello.elf -i /tmp/hello.input -o /tmp/hello.out -m
```

Recorded result: **1,032 steps** (matching the bootstrapped-`cake` step
count recorded in ZISK-PROVE.md, not the prebuilt-release's 906 — the two
`cake` builds emit slightly different code; flapjack matches whichever `cake`
build it is compared against instruction-for-instruction here).

Generate and verify a proof:

```bash
mkdir -p work/proof-hello/proofs
time nice cargo-zisk prove -e guest/build/hello.elf -i /tmp/hello.input \
  -l -o work/proof-hello -b -y
```

Recorded result: 12 AIR instances (Main, Rom, Binary, BinaryAdd,
BinaryExtension, MemAlignWriteByte, Mem, InputData, RomData,
SpecifiedRanges, VirtualTable0/1), all verified in-process (`-y`);
contributions 23.4s, inner proofs 86.4s, verification 2.2s, **1m58s** wall
including proving-key load, 108 MB of proof JSON.

## EEST test fixture 00000

Same fixture as ZISK-PROVE.md
(`blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_authority_is_recipient.json`).

```bash
INPUT=work/inputs/00000_test_account_write_authority_is_recipient_fork_Amsterdam-blockchain_test_from_state_test-non-zer.input
time ~/.zisk/bin/ziskemu -e guest/build/guest.elf -i "$INPUT" -o /tmp/block00000.out -m
```

Recorded result: **18,864,486 ZisK steps**, 0.155s emulation time — identical
to the fresh `cake` build's step count and output bytes on this fixture (see
"Correctness first"), and `PASS(full)` per `tools/eest-run.py`'s
classification against the Python oracle. The accelerated guest
(`guest-accel.elf`) runs the same fixture in **2,584,624 steps**, also with
identical output to `cake`'s accelerated build.

```bash
mkdir -p work/proof-block00000/proofs
time nice cargo-zisk prove -e guest/build/guest.elf -i "$INPUT" \
  -l -o work/proof-block00000 -b -y
```

Recorded result: 18 AIR instances (5× Main, plus Rom, 2× Binary, Arith,
BinaryExtension, BinaryAdd, MemAlign, Mem, InputData, RomData,
SpecifiedRanges, VirtualTable0/1) — the same composition ZISK-PROVE.md
recorded for the `cake` build — all verified, breakdown from the
`cargo-zisk` log:

| Stage | Time |
| --- | --- |
| Execute (witness/plan) | 0.58s |
| Calculating contributions | 52.0s |
| Generating inner proofs | 181.7s |
| Verifying proofs | 3.2s |
| **Total proving** | **~237s (~3m57s)** |

Wall clock for the whole `prove` invocation (including proving-key load):
**4m5s**; 162 MB of proof JSON under `work/proof-block00000/proofs/`.

The same fixture with the accelerated guest:

```bash
mkdir -p work/proof-block00000-accel/proofs
time nice cargo-zisk prove -e guest/build/guest-accel.elf -i "$INPUT" \
  -l -o work/proof-block00000-accel -b -y
```

Recorded result: 16 AIR instances (one each of Main, Rom, Binary, BinaryAdd,
BinaryExtension, Arith, ArithEq, Keccakf, Sha256f, MemAlign, Mem, InputData,
RomData, SpecifiedRanges, VirtualTable0/1) — again the same composition as
the `cake` build — all verified; contributions 44.9s, inner proofs 139.8s,
verification 3.0s, **3m17s** wall, 160 MB of proof JSON.

## Notes

* Everything in [docs/ZISK-PROVE.md](ZISK-PROVE.md)'s Notes section applies
  unchanged (the `-l`/`-s` mutual exclusion, `DIR/proofs` needing to
  pre-exist, proving time being dominated by fixed per-AIR setup rather than
  step count).
* `cargo-zisk verify -p work/proof-*/proofs/<Air>_<n>.json`, documented as
  re-checking an individual proof file standalone, errored in this
  environment/toolchain version (`invalid value: integer ..., expected
  variant index 0 <= i < 5`) on every proof file tried, including from the
  `hello.pnk` run — this reproduces with `cake`-compiled proofs too, so it is
  a `cargo-zisk` 0.16.0 issue unrelated to which Pancake compiler produced
  the guest. The in-process `-y` verification during `prove` (which did
  succeed for every AIR instance recorded above) is the correctness check
  this document relies on.
* `ziskup --provingkey` (no `-v`) reinstalls the *latest* ZisK release before
  fetching the key, silently swapping out a pinned older `ziskemu`/`cargo-zisk`
  the rest of the repo's docs assume. Always pass `-v <version>` when only
  the proving key is missing.
