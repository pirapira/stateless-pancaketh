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
`guest/build/guest.elf`, and `guest/build/guest-accel.elf`. This guide also
needs its own guest builds, with `ZISK_V1=1` (see "Build the ZisK 1.x guest
ELFs" below) — Quick Start's plain builds cannot run under ZisK 1.x at all.

## Prerequisites

A ZisK toolchain installed via `ziskup` (https://ziskup.zisk.tech):
`ziskup -v 1.3.0-alpha --provingkey`, plus a manual proving-key fix (see
below). Gotchas hit while preparing this document, worth knowing before you
run it:

* `ziskup --provingkey` with no `-v` installs the latest release first,
  silently swapping out a pinned older `ziskemu`/`cargo-zisk`. Always pass
  `-v <version>`.
* `ziskup`'s own proving-key download is broken for this release. It
  computes the download URL by dropping the `-alpha` suffix
  (`zisk-provingkey-1.3.0.tar.gz`, no longer even present in the bucket as
  of this writing) instead of the correctly-suffixed
  `zisk-provingkey-1.3.0-alpha.tar.gz`, so its checksum check against the
  wrong file's sidecar fails and `ziskup --provingkey` exits partway through
  (the `ziskemu`/`cargo-zisk` binaries install fine; the key does not).
  Fetch and verify the correct key manually instead:

  ```bash
  curl -fL -o zisk-provingkey-1.3.0-alpha.tar.gz \
    https://storage.googleapis.com/zisk-setup/zisk-provingkey-1.3.0-alpha.tar.gz
  curl -fL -o zisk-provingkey-1.3.0-alpha.tar.gz.md5 \
    https://storage.googleapis.com/zisk-setup/zisk-provingkey-1.3.0-alpha.tar.gz.md5
  md5sum -c zisk-provingkey-1.3.0-alpha.tar.gz.md5
  rm -rf ~/.zisk/provingKey   # only needed if a different version's key is already there
  tar xzf zisk-provingkey-1.3.0-alpha.tar.gz -C ~/.zisk
  ```

  A separate `zisk-provingkey-pre-1.3.0-alpha-blake3.tar.gz` also exists in
  the same bucket. That one matches the BLAKE3-based recursive-proving
  configuration this release's changelog calls out as "available for
  testing", not the default: it installs and lets `ziskemu` run guests
  fine, but `cargo-zisk prove` fails witness generation in the recursive1
  stage (`Failed assert in template/function VerifyEvaluations0`). The key
  fetched above uses Poseidon1, the actual default (`cargo-zisk prove`
  logs `Using hash function: Poseidon1` when it is active).
* The installer's "Configuring CPU binaries" step is unreliable when
  switching versions in an existing `~/.zisk`: it can leave `ziskemu`
  updated but `cargo-zisk` on the old version (`cargo-zisk --version` will
  show it). If so, the correctly-versioned binary is already on disk as
  `~/.zisk/bin/cargo-zisk-cpu`; `cp ~/.zisk/bin/cargo-zisk-cpu
  ~/.zisk/bin/cargo-zisk` fixes it without a full reinstall.

Versions used for the run recorded below:

| Component | Version / commit |
| --- | --- |
| `ziskemu` | 1.3.0-alpha (2026-09-21) |
| `cargo-zisk` | 1.3.0-alpha (2026-09-21) |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| EEST fixtures | `tests-zkevm@v0.6.2` |
| Host | Ubuntu 24.04.5, 32 cores |

**Proving is CPU-heavy** (full CPU-time figures are recorded below for each
run). Run `cargo-zisk prove`/`execute` under `nice` so it does not starve
other work on a shared machine, as done in every command below.

## Two upstream issues in ZisK 1.x, and how this guide works around them

Compared to 0.18.0, ZisK 1.x (starting at v1.1.0-alpha) introduces two
behavior changes that break this project's guest as built by Quick Start /
`tools/build_both.sh`:

1. **Stricter ELF segment handling.** `guest/build.sh`'s default link
   (`-Ttext=0x80000000`) produces an R+E (readable+executable) `.text`
   `PT_LOAD` segment, with the ELF/program headers in their own segment
   just below it at `0x7ffff000`. ZisK 0.18.0 tolerates both. ZisK 1.x
   rejects the headers segment outright (outside its declared ROM window,
   `Error during emulation: Unknown("PT_LOAD segment ... is outside ZisK
   addressable space")`), and once that is worked around, its RISC-V→ZisK
   ROM converter panics (`Riscv2ZiskContext::convert() found invalid
   riscv_instruction.inst_name=c.fsdsp`) on an R+E `.text` segment whenever
   a second `PT_LOAD` segment (`.data`) is also present — true of every
   real guest here, since input/output/heap all live in a separate RAM
   segment from ROM. This reproduces on a minimal ELF (a single `nop` plus
   one byte of `.data`, no compressed instructions involved) and has been
   reported upstream.
2. **`OUTPUT_ADDR` moved.** ZisK 0.18.0 (and v1.0.0-alpha) define a guest's
   output region at `SYS_ADDR + SYS_SIZE` where `SYS_ADDR = RAM_ADDR`
   (`0xa0010000`) — the address this project's guest contract
   (`guest/src/config.h`, `guest/runtime/start.S`, evm-asm's
   `spike_run.cc`) has always used. ZisK v1.1.0-alpha added a dedicated,
   guarded 4MB stack region at the base of RAM (`STACK_SIZE = 0x400000`,
   matching that release's changelog entry "Added stack overflow protection
   using an unmapped guard region"), which pushes `SYS_ADDR` to
   `RAM_ADDR + STACK_SIZE` and `OUTPUT_ADDR` to `0xa0410000`. A guest still
   writing to the old address executes to completion with plausible step
   counts but reports all-zero output, because ZisK now reads the new
   address instead.

`guest/build.sh` has a `ZISK_V1=1` flag that works around both: it links
with `guest/runtime/zisk-strict.ld` (execute-only `.text`, ELF headers left
unmapped — avoids both the header-segment rejection and the R+E-segment
panic) and defines `-DZISK_V1` so `guest/src/config.h` uses
`OUTPUT_ADDR = 0xa0410000` (`guest/runtime/start.S`'s one non-`config.h`
use of this address, in the trap handler, picks it up via a `--defsym` at
link time).

`ZISK_V1=1` builds are for this guide only. They write output to a
different address than Spike expects, so they will not produce correct
results under `tools/eest-run.py` or the `CHECK_ALL_ZISKE_PARITY=1` gate in
`tools/check_all.sh`, both of which target the default (Spike / ZisK
0.18.0) `OUTPUT_ADDR`. Keep `ZISK_V1=1` builds in separate output paths
from Quick Start's, as done below.

## Build the ZisK 1.x guest ELFs

```bash
ZISK_V1=1 guest/build.sh guest/src/hello.pnk guest/build/hello-v1.elf
ACCEL=1 ZISK_V1=1 guest/build.sh guest/src/main.pnk guest/build/guest-accel-v1.elf
```

(The 40 static-analysis warnings `flapjack-compile` prints while building
`main.pnk` are non-fatal and expected, not specific to this walkthrough.)

## Small example: `hello.pnk`

An 8-byte input (`ziskemu` requires input length to be a multiple of 8):

```bash
printf 'hello\0\0\0' > /tmp/hello.input
~/.zisk/bin/ziskemu -e guest/build/hello-v1.elf -i /tmp/hello.input -o /tmp/hello.out -m
```

Recorded result: **907 steps** (0.18.0's bootstrapped-`cake` build gave
1,032; `FLAPJACK-CORRECTNESS.md` separately recorded 906 for a
prebuilt-release `cake` build — the gap from either 0.18.0 figure is
consistent with ISA-level step-accounting changes across the 0.18.0→1.x
line, e.g. 1.3.0-alpha's native RISC-V Zba support, not a correctness
regression).

Generate and verify a proof (`-o` is a single output file; `prove` always
produces one aggregated, fixed-size proof; unlike 0.18.0, there is no
separate `cargo-zisk check-setup` step — the first `prove` invocation
against a given proving key regenerates the constant trees automatically):

```bash
time nice cargo-zisk prove -e guest/build/hello-v1.elf -i /tmp/hello.input \
  -o work/proof-hello.json -y
cargo-zisk verify -p work/proof-hello.json
```

Recorded result: the first-ever invocation against this proving key spent
219.0s regenerating constant trees (one-time; the tool's own reported
"Proof generated in 305.840s" excludes this). 9 AIR instances (Binary,
BinaryExtension, InputData, Main, Mem, MemAlign, Rom, VirtualTableZisk0/1)
folded into one Vadcop Final proof: contributions 65.2s, inner proofs
235.0s, final aggregation 5.5s, verified in-process (`-y`) and again
standalone (`verify`, 69ms); **9m19s** wall including the one-time
constant-tree regeneration (150m31s user / 4m14s system CPU time across
cores), **415,200 bytes** proof file.

## EEST test fixture 00000

EEST fixture 00000
(`blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_authority_is_recipient.json`).
This uses the **accelerated** guest (`guest-accel-v1.elf`, built above)
throughout — it's the guest anyone proving a real block cares about; see
[docs/ZISK-PROVE-BLOCK-FLAPJACK.md](ZISK-PROVE-BLOCK-FLAPJACK.md) for the
real-block pipeline.

```bash
INPUT=work/inputs/00000_test_account_write_authority_is_recipient_fork_Amsterdam-blockchain_test_from_state_test-non-zer.input
time ~/.zisk/bin/ziskemu -e guest/build/guest-accel-v1.elf -i "$INPUT" -o /tmp/block00000.out -m
```

Recorded result: **2,576,557 ZisK steps** (0.18.0: 2,584,624); the dumped
output's first 71 bytes match `work/inputs/manifest.tsv`'s expected-output
column exactly, with the rest of the fixed-size output buffer correctly
zero-padded.

```bash
time nice cargo-zisk prove -e guest/build/guest-accel-v1.elf -i "$INPUT" \
  -o work/proof-block00000-accel.json -y
cargo-zisk verify -p work/proof-block00000-accel.json
```

Recorded result: 13 AIR instances (one each of Arith, ArithEq, Binary,
BinaryExtension, InputData, Keccakf, Main, Mem, MemAlign, Rom, Sha256f,
VirtualTableZisk0/1) folded into one Vadcop Final proof; `cargo-zisk`'s own
log reports proving completed in 451.9s (contributions 83.1s, inner proofs
365.4s, final aggregation 3.3s), **7m59s** wall clock for the whole `prove`
invocation (140m user / 1m40s system CPU time across cores), **415,244
bytes** proof file (close to `hello.pnk`'s — the aggregated proof is
fixed-size regardless of the underlying execution length). Verified both
in-process (`-y`) and standalone (`cargo-zisk verify`, 60ms).

## Notes

* `ziskemu`'s `-l`/`-s` flags no longer mean `--emulator`/`--asm` as they
  did in 0.18.0 (`-l` on 1.x means `--log-step`); there is no longer a
  choice to make on `ziskemu` itself — this guest, a raw RISC-V ELF, always
  runs under the default Rust emulator. `cargo-zisk prove`/`setup`/`execute`
  instead have their own `-a`/`--asm` to opt into the (unused here) ASM
  backend.
* `-o` still takes a single output file path; `prove` still always
  aggregates into one Vadcop Final proof, and `cargo-zisk verify -p <that
  file>` still works correctly and quickly.
* Proof size is still fixed-size regardless of step count: 415,200 /
  415,244 / 415,248 bytes across hello / this fixture /
  [docs/ZISK-PROVE-BLOCK-FLAPJACK.md](ZISK-PROVE-BLOCK-FLAPJACK.md)'s real
  block — all close to each other, about 10% bigger than 0.18.0's 375,809
  bytes across the same three cases.
* The AIR-instance count per proof dropped from 0.18.0 (11→9 for hello,
  15→13 for this fixture, 127→45 for the real block in
  [docs/ZISK-PROVE-BLOCK-FLAPJACK.md](ZISK-PROVE-BLOCK-FLAPJACK.md)), which
  matches 1.x's trace-packing work (multiple execution steps packed per
  row) rather than a smaller proof — file size is essentially unchanged.

For the same pipeline against a real chain block instead of a synthetic
EEST fixture, see
[docs/ZISK-PROVE-BLOCK-FLAPJACK.md](ZISK-PROVE-BLOCK-FLAPJACK.md).
