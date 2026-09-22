# Prove a real chain block on ZisK, guest compiled by flapjack

This does the same `ziskemu`-run-plus-proof pipeline as
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) against an actual
chain block instead of a synthetic EEST fixture: `glamsterdam-devnet-7`
block `115260`, the same block used for the gist comparison in
[issue #54](https://github.com/pirapira/stateless-pancaketh/issues/54)
(`M5: reproduce the gist comparison on devnet-7 block 115260`), with the
guest compiled by `flapjack` (the Lean 4 port of the Pancake compiler,
`lake exe flapjack-compile`). Follow
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) first: it covers the
guest-build prerequisites. This document only adds the real-block-specific
steps below.

Because of the size of a full block (568,669-byte stateless input, vs. a few
KB for an EEST fixture), this uses the **accelerated** guest
(`guest-accel.elf`, `ACCEL=1` build) rather than the software guest: issue
#54 already measured the software guest at `6,152,130,715` ZisK steps versus
`256,756,696` for the accelerated guest on this same block (a 23.96x
difference), and proving cost scales with step count, so proving the
software guest here would take on the order of a day rather than half an
hour. `nice` is used throughout, per the same CPU-load note as
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md).

The flapjack-compiled `guest-accel.elf` was checked for correctness on this
exact block before proving; see
[docs/FLAPJACK-CORRECTNESS.md](FLAPJACK-CORRECTNESS.md).

## Prerequisites

Everything in [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md)'s
"Prerequisites" section (flapjack as a `lake` dependency,
`riscv64-unknown-elf-{as,ld}` and `cpp`, and the ZisK 0.18.0 toolchain via
`ziskup`), plus:

* `curl` and a `tar` with zstd support (Ubuntu: `zstd`) to fetch and extract
  the block archive.
* Python 3 for `evm-asm/scripts/eest-stateless-to-input.py`.

## Fixture

Same block as issue #54:

| Field | Value |
| --- | --- |
| Network | `glamsterdam-devnet-7` |
| Chain ID | `7082904758` |
| Block | `115260` |
| Block hash | `0x3c8d1842a0538d9f67a091fc4b7ab007be665735c2b0ddebeb5a313c382f0764` |
| Gas used | `65,318,413` |
| Stateless input | `568,669` bytes |
| Archive | [`115260-115269.tar.zst`](https://pub-df22334654034ebab51bc096137a59d8.r2.dev/devnets/glamsterdam-devnet-7/exports/batches/115260-115269.tar.zst) |
| Archive SHA-256 | `30562c14a0ac768861fd44e592408f7d5f3775919eb623ac25cda91427dd0405` |

Versions used for the run recorded below:

| Component | Version / commit |
| --- | --- |
| `ziskemu` | 0.18.0 (790f9e2, 2026-05-15) |
| `cargo-zisk` | 0.18.0 (790f9e2, 2026-05-15) |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| guest source | `stateless-pancaketh` `43222a3` |
| Host | Ubuntu 24.04.5, 32 cores |

## Fetch, extract, build, convert

```bash
mkdir -p work/gist/archive
curl -fL \
  'https://pub-df22334654034ebab51bc096137a59d8.r2.dev/devnets/glamsterdam-devnet-7/exports/batches/115260-115269.tar.zst' \
  -o work/gist/115260-115269.tar.zst
printf '%s  %s\n' \
  30562c14a0ac768861fd44e592408f7d5f3775919eb623ac25cda91427dd0405 \
  work/gist/115260-115269.tar.zst | sha256sum -c -
tar --zstd -xf work/gist/115260-115269.tar.zst -C work/gist/archive

ACCEL=1 COMPILER=flapjack guest/build.sh guest/src/main.pnk guest/build/guest-accel.elf

python3 evm-asm/scripts/eest-stateless-to-input.py \
  --fixtures-dir work/gist/archive/blockchain_tests \
  --out-dir work/gist/inputs \
  --filter '115260-' --limit 1 --verify-input-parity
```

This writes `work/gist/inputs/00000_block_115260_..._b0.input`
(568,680 bytes) and a manifest whose expected-output column reproduces issue
#54's recorded hex exactly — unaffected by which Pancake compiler built the
guest, since this step doesn't touch the guest at all.

## Emulate and confirm the result

```bash
INPUT=work/gist/inputs/00000_block_115260_3c8d1842a0538d9f67a091fc4b7ab007be665735c2b0ddebeb5a313c382f0764_b0.input
time ~/.zisk/bin/ziskemu -e guest/build/guest-accel.elf -i "$INPUT" \
  -o work/gist/accelerated-zisk.out -X
```

Recorded result: **263,739,098 ZisK steps**, ~16.6s wall (`ziskemu -X`,
including the cost/opcode breakdown report), output bytes identical to
issue #54's recorded 69-byte result (root/succ/tail all match, including
the success byte `01` at offset 32):

```text
7734570c97a937506b9b771b328a2e5bdb8b74af65c54c747603e4b3d1e8d7ce0125000000b68c2ca6010000000c0000000400000008000000080000000000000000000000
```

## Generate and verify the proof

`-o` takes a single output file; `prove` always aggregates into one Vadcop
Final proof:

```bash
time nice -n 15 cargo-zisk prove -e guest/build/guest-accel.elf -i "$INPUT" \
  -l -o work/proof-block115260.json -y
```

Recorded result: **127 AIR instances** (63× Main, 16× Mem, 10× BinaryAdd,
9× Binary, 5× ArithEq384, 4× Sha256f, 3× ArithEq, 3× BinaryExtension, 3×
Keccakf, 2× MemAlignReadByte, plus one each of Arith, InputData, MemAlign,
MemAlignWriteByte, Rom, RomData, SpecifiedRanges, VirtualTable0,
VirtualTable1), folded into one Vadcop Final proof. Verified both
in-process (`-y`) and standalone (`cargo-zisk verify`, 50ms).

| Stage | Time |
| --- | --- |
| Execute (witness/plan) | 5.7s |
| Calculating contributions | 479.6s (8.0 min) |
| Generating inner proofs | 2353.1s (39.2 min) |
| Generating Vadcop final proof | 4.7s |
| Verifying Vadcop final proof (in-process) | 0.02s |
| **Total proving** | **~2843s (47.4 min)** |

Wall clock for the whole `prove` invocation (including proving-key load):
**47m29s**; **955m** of user CPU time and **234m** of system time consumed
across all cores over that wall time (`nice -n 15` is what keeps this from
starving other work on a shared machine). The proof file is **376 KB
(375,809 bytes)** — identical in size to the small `hello.pnk`/EEST-fixture
proofs in [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) (the
aggregated proof is fixed-size regardless of the underlying execution
length).

This machine is shared with other tenants; the first two attempts at this
proof were OOM-killed partway through (once during contribution
calculation, once at the very start) when system load spiked from unrelated
processes (load average briefly over 40 on this host). The run recorded
above succeeded once load dropped back to single digits. This is a
host-contention issue, not a compiler or ZisK-version difference — worth
knowing if reproducing this on a busy shared machine.

## Notes

* This is a genuine chain block (`glamsterdam-devnet-7` #115260), not a
  synthetic EEST test case — see
  [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) for the
  smaller/faster fixture-based walkthrough.
* The *software* guest was not proved here — based on issue #54's ~24x
  larger step count for the software guest on this block, it would
  plausibly take on the order of hours.
* `work/gist/archive`, `work/gist/inputs`, and the proof file are left out
  of version control (large, regenerable); this doc is the reproducible
  record.
