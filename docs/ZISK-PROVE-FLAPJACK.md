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

## ZisK version

This document uses **ZisK 0.18.0** (the newest non-alpha release at the time
of writing — 1.0.0-alpha through 1.2.0-alpha exist but are pre-release, and
1.2.0-alpha's guest ELF loader currently rejects this repo's linked guest
outright, `cake`-built or `flapjack`-built alike: `PT_LOAD segment
0x7ffff000-0x80003000 is outside ZisK addressable space`, unrelated to either
compiler). 0.18.0 was checked to produce the exact same step counts and
output bytes as 0.16.0 (the version [docs/ZISK-PROVE.md](ZISK-PROVE.md) and
[docs/ZISK-PROVE-REAL-BLOCK.md](ZISK-PROVE-REAL-BLOCK.md) use), and its
`cargo-zisk prove` now aggregates everything into one small, fixed-size
proof (see below) with a working standalone `cargo-zisk verify` — an
improvement over 0.16.0, at the cost of longer proving time (aggregation is
extra work). If you need to match those other documents' exact `cargo-zisk`
CLI shape (`-b`, a `proofs/` output directory, per-AIR JSON files), use
`ziskup -v 0.16.0 --provingkey` instead; everything in the "Correctness
first" section above and the ziskemu step counts below are identical on
either version.

## Prerequisites

Same as [docs/ZISK-PROVE.md](ZISK-PROVE.md), except the compiler and the ZisK
version:

* `flapjack` is a `lake` dependency of this repo (`lakefile.toml`'s
  `[[require]] name = "flapjack"`), pinned by commit; no separate checkout or
  bootstrap step is needed beyond `lake build` (which `lake exe
  flapjack-compile` triggers on first use). `guest/build.sh` picks it via
  `COMPILER=flapjack`; `COMPILER=cake` (the default) is unchanged.
* `riscv64-unknown-elf-{as,ld}` and `cpp` (Ubuntu `binutils-riscv64-unknown-elf`).
* A ZisK toolchain installed via `ziskup` (https://ziskup.zisk.tech):
  `ziskup -v 0.18.0 --provingkey`, then `cargo-zisk check-setup` (it
  regenerates constant-tree files for a new key on first run, which takes a
  couple of minutes). Three `ziskup` gotchas hit while preparing this
  document, worth knowing before you run it:
  * `ziskup --provingkey` with no `-v` installs the *latest* release first
    (currently `1.2.0-alpha`), silently swapping out a pinned older
    `ziskemu`/`cargo-zisk`. Always pass `-v <version>`.
  * The installer's "Configuring CPU binaries" step is unreliable when
    switching versions in an existing `~/.zisk`: it can leave `ziskemu`
    updated but `cargo-zisk` on the old version (`cargo-zisk --version` will
    show it). If so, the correctly-versioned binary is already on disk as
    `~/.zisk/bin/cargo-zisk-cpu`; `cp ~/.zisk/bin/cargo-zisk-cpu
    ~/.zisk/bin/cargo-zisk` fixes it without a full reinstall.
  * `1.2.0-alpha`'s proving-key artifact (`zisk-provingkey-1.2.0.tar.gz` and
    its `.md5`) both 404 at `storage.googleapis.com/zisk-setup/` as of this
    writing — an upstream gap, not fixable locally, and part of why this
    document stays on 0.18.0.

Versions used for the run recorded below:

| Component | Version / commit |
| --- | --- |
| `ziskemu` | 0.18.0 (790f9e2, 2026-05-15) |
| `cargo-zisk` | 0.18.0 (790f9e2, 2026-05-15) |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `cake` (comparison reference only) | bootstrapped, CakeML `e8eca63` |
| `cakeml` submodule | `857f0d98da8f8a3580f34423338e697809308ede` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| EEST fixtures | `tests-zkevm@v0.6.2` |
| Host | Ubuntu 24.04.5, 32 cores |

**Proving is CPU-heavy** (the fixture run below used all cores at ~100+
CPU-minutes of user time over 5-6 minutes wall-clock). Run `cargo-zisk
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
build it is compared against instruction-for-instruction here). Identical on
both ZisK 0.16.0 and 0.18.0, and the output bytes match a fresh `cake` build
exactly.

Generate and verify a proof (0.18.0's `prove` no longer takes `-b`/needs a
pre-made `proofs/` subdirectory — `-o` is a single output file, and it always
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
aggregation 9.3s, **3m43s** wall including proving-key load, **376 KB (375,809 bytes)**
proof file (0.16.0's equivalent run produced 108 MB of per-AIR JSON with no
working standalone verify — see "Notes").

## EEST test fixture 00000

Same fixture as ZISK-PROVE.md
(`blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_authority_is_recipient.json`).

```bash
INPUT=work/inputs/00000_test_account_write_authority_is_recipient_fork_Amsterdam-blockchain_test_from_state_test-non-zer.input
time ~/.zisk/bin/ziskemu -e guest/build/guest.elf -i "$INPUT" -o /tmp/block00000.out -m
```

Recorded result: **18,864,486 ZisK steps**, 0.18s emulation time — identical
to the fresh `cake` build's step count and output bytes on this fixture (see
"Correctness first"), and `PASS(full)` per `tools/eest-run.py`'s
classification against the Python oracle. Identical step count and output on
both ZisK 0.16.0 and 0.18.0 (ziskemu's RISC-V emulation is unaffected by the
proving-side changes between those versions). The accelerated guest
(`guest-accel.elf`) runs the same fixture in **2,584,624 steps**, also with
identical output to `cake`'s accelerated build.

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

Both 0.18.0 runs above have one fewer AIR instance than the equivalent
0.16.0 run recorded in an earlier revision of this document (0.16.0 had a
`BinaryAdd` instance that 0.18.0 folds elsewhere) — a proving-engine
composition change between ZisK versions, not a correctness difference: step
counts and output bytes are identical either way.

## Notes

* Everything in [docs/ZISK-PROVE.md](ZISK-PROVE.md)'s Notes section applies
  to 0.16.0 unchanged. On 0.18.0, `-b`, the `DIR/proofs` subdirectory
  requirement, and per-AIR JSON output are gone: `-o` takes a single file
  path, `prove` always aggregates into one Vadcop Final proof, and
  `cargo-zisk verify -p <that file>` (documented as broken for 0.16.0 in the
  next bullet) works correctly and quickly.
* On ZisK **0.16.0**, `cargo-zisk verify -p work/proof-*/proofs/<Air>_<n>.json`
  — documented there as re-checking an individual proof file standalone —
  errors in this toolchain version (`invalid value: integer ..., expected
  variant index 0 <= i < 5`) on every proof file tried, `cake`-compiled or
  `flapjack`-compiled alike, so it's a `cargo-zisk` 0.16.0 issue unrelated to
  either compiler. 0.18.0's `cargo-zisk verify` does not have this problem
  (see above), which is one reason to prefer it.
* Proving cost is still dominated by fixed per-AIR setup work rather than
  step count on 0.18.0, same as 0.16.0 (see ZISK-PROVE.md's Notes): 1,032
  steps (`hello.pnk`) and 18.86M steps (the fixture) differ by four orders of
  magnitude in steps but well under 2x in proving time.
