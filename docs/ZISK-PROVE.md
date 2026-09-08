# Run the guest under ziskemu and produce a ZisK proof

This walks through the two ZisK-specific steps that `README.md` only
summarizes: emulating the Pancake-compiled guest with `ziskemu` (for step
counts) and generating an actual STARK proof of a real execution with
`cargo-zisk prove`. It starts with a tiny example (`hello.pnk`) to validate
the pipeline cheaply, then does the same with an EEST test fixture (a
synthetic single-block, single-transaction test case, not a chain block).

## Prerequisites

* A bootstrapped CakeML `cake` executable built from the pinned `cakeml`
  submodule (see `README.md` Toolchain). Set `CAKE=` if it is not at
  `cakeml/developers/bin/cake`.
* `riscv64-unknown-elf-{as,ld}` and `cpp` (Ubuntu `binutils-riscv64-unknown-elf`).
* A ZisK toolchain installed via `ziskup` (https://ziskup.zisk.tech), giving
  `~/.zisk/bin/ziskemu` and `~/.zisk/bin/cargo-zisk`, plus the proving key at
  `~/.zisk/provingKey`. Run `cargo-zisk check-setup` once to confirm the
  proving key loads.

Versions used for the run recorded below:

| Component | Version / commit |
| --- | --- |
| `ziskemu` | 0.16.0 (f8ef9b0, 2026-06-22) |
| `cargo-zisk` | 0.16.0 (aacf0a7, 2026-03-12) |
| `cakeml` submodule | `857f0d98da8f8a3580f34423338e697809308ede` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| EEST fixtures | `tests-zkevm@v0.6.2` |
| Host | Ubuntu 24.04.4, 16 physical cores |

**Proving is CPU-heavy** (the real-block run below used all cores at ~89
CPU-minutes of user time over ~3.5 minutes wall-clock). Run `cargo-zisk
prove`/`execute` under `nice` so it does not starve other work on a shared
machine, as done in every command below.

## Fetch fixtures and build the guest

```bash
CAKE="${CAKE:-$PWD/cakeml/developers/bin/cake}"
TAG="$(cat evm-asm/scripts/eest-fixture-tag.txt)"
evm-asm/scripts/eest-fetch-fixtures.sh "$TAG"   # or copy an existing evm-asm/gen-out
tools/make-inputs.sh 1                          # work/inputs: just fixture 00000
mkdir -p guest/build
CAKE="$CAKE" guest/build.sh guest/src/hello.pnk guest/build/hello.elf
CAKE="$CAKE" guest/build.sh guest/src/main.pnk guest/build/guest.elf
```

`guest/build.sh` for `main.pnk` takes about 24s (cake + as + ld); `hello.pnk`
builds in well under a second.

## Small example: `hello.pnk`

An 8-byte input (`ziskemu` requires input length to be a multiple of 8):

```bash
printf 'hello\0\0\0' > /tmp/hello.input
~/.zisk/bin/ziskemu -e guest/build/hello.elf -i /tmp/hello.input -o /tmp/hello.out -c
```

Generate and verify a proof (`-l` selects the prebuilt emulator instead of an
`--asm` build; `-b` persists the per-AIR proof JSONs under `-o`, which must
already contain a `proofs/` subdirectory; `-y` verifies in-process after
proving):

```bash
mkdir -p work/proof-hello/proofs
time nice cargo-zisk prove -e guest/build/hello.elf -i /tmp/hello.input \
  -l -o work/proof-hello -b -y
```

Recorded result: 1032 steps, 12 AIR instances (Main, Rom, Binary,
BinaryAdd, BinaryExtension, MemAlignWriteByte, Mem, InputData, RomData,
SpecifiedRanges, VirtualTable0/1), all verified, **106.8s** proving time
(`~1m49s` wall including proving-key load), ~108 MB of proof JSON.
`cargo-zisk verify -p work/proof-hello/proofs/<Air>_<n>.json` re-checks any
individual proof file standalone.

## EEST test fixture 00000

`work/inputs/00000_..non-zer.input` (5.8 KB) is fixture
`blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_authority_is_recipient.json`
from `tools/make-inputs.sh` above.

```bash
INPUT=work/inputs/00000_test_account_write_authority_is_recipient_fork_Amsterdam-blockchain_test_from_state_test-non-zer.input
time ~/.zisk/bin/ziskemu -e guest/build/guest.elf -i "$INPUT" -o /tmp/block00000.out -m
```

Recorded result: **18,769,741 ZisK steps**, 0.12s emulation time, output
bytes identical to the fixture's expected `statelessOutputBytes` (root/succ/tail
all match, same classification `tools/eest-run.py` would report as
`PASS(full)`).

```bash
mkdir -p work/proof-block00000/proofs
time nice cargo-zisk prove -e guest/build/guest.elf -i "$INPUT" \
  -l -o work/proof-block00000 -b -y
```

Recorded result: 18 AIR instances (5× Main, plus Rom, 2× Binary, Arith,
BinaryExtension, BinaryAdd, MemAlign, Mem, InputData, RomData,
SpecifiedRanges, VirtualTable0/1), all verified, breakdown from the
`cargo-zisk` log:

| Stage | Time |
| --- | --- |
| Execute (witness/plan) | 0.57s |
| Calculating contributions | 47.7s |
| Generating inner proofs | 160.4s |
| Verifying proofs | 3.1s |
| **Total proving** | **211.9s (~3m32s)** |

Wall clock for the whole `prove` invocation (including proving-key load):
**3m34s**; 162 MB of proof JSON under `work/proof-block00000/proofs/`.

## Notes

* `-l/--emulator` and `-s/--asm` are mutually exclusive; this guest is a raw
  RISC-V ELF (not a ZisK SDK Rust program), so there is no `--asm` build to
  use — always pass `-l`.
* `cargo-zisk prove -o DIR` requires `DIR/proofs` to exist beforehand with
  `-b`; otherwise it silently fails per-AIR JSON writes partway through the
  (otherwise successful) proving run.
* Proving cost above is dominated by the fixed per-AIR setup
  (contributions/inner-proof machinery), not step count: 1032 steps (hello)
  and 18.77M steps (fixture) differ by four orders of magnitude in steps
  but only ~2x in proving time, because both stay within a handful of AIR
  instances of the fixed proving-key size.
