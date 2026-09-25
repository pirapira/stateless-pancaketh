# Prove a chain block on ZisK, guest compiled by flapjack

This does the same `ziskemu`-run-plus-proof pipeline as
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) against an actual
chain block instead of a synthetic EEST fixture: `glamsterdam-devnet-7`
block `115260`, the same block used for the gist comparison in
[issue #54](https://github.com/pirapira/stateless-pancaketh/issues/54)
(`M5: reproduce the gist comparison on devnet-7 block 115260`), with the
guest compiled by `flapjack` (the Lean 4 port of the Pancake compiler,
`lake exe flapjack-compile`). Follow
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) first: it covers the
guest-build prerequisites, including the `ZISK_V1=1` build flag this ZisK
1.x run needs. This document only adds the real-block-specific steps below.

This uses the **accelerated** guest (`guest-accel-v1.elf`, `ACCEL=1
ZISK_V1=1` build). `nice` is used throughout, per the same CPU-load note as
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md).

The flapjack-compiled `guest-accel.elf` was checked for correctness on this
exact block before proving; see
[docs/FLAPJACK-CORRECTNESS.md](FLAPJACK-CORRECTNESS.md). That check predates
the `ZISK_V1=1` build flag, which only changes ELF segment layout and the
output address — not the guest's logic — so it still applies.

## Prerequisites

Everything in [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md)'s
"Prerequisites" section (the ZisK 1.3.0-alpha toolchain via `ziskup`,
including its proving-key workaround; that document also assumes README's
"Quick start" has already been run), plus:

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
| `ziskemu` | 1.3.0-alpha (2026-09-21) |
| `cargo-zisk` | 1.3.0-alpha (2026-09-21) |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| guest source | `stateless-pancaketh` `29c5b34` plus the uncommitted `ZISK_V1` changes to `guest/build.sh`, `guest/src/config.h`, `guest/runtime/start.S`, `guest/runtime/zisk-strict.ld` described in [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) |
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

ACCEL=1 ZISK_V1=1 COMPILER=flapjack guest/build.sh guest/src/main.pnk guest/build/guest-accel-v1.elf

python3 evm-asm/scripts/eest-stateless-to-input.py \
  --fixtures-dir work/gist/archive/blockchain_tests \
  --out-dir work/gist/inputs \
  --filter '115260-' --limit 1 --verify-input-parity
```

This writes `work/gist/inputs/00000_block_115260_..._b0.input`
(568,680 bytes) and a manifest whose expected-output column reproduces issue
#54's recorded hex exactly — unaffected by which Pancake compiler built the
guest, or by `ZISK_V1`, since this step doesn't touch the guest at all.

## Emulate and confirm the result

```bash
INPUT=work/gist/inputs/00000_block_115260_3c8d1842a0538d9f67a091fc4b7ab007be665735c2b0ddebeb5a313c382f0764_b0.input
time ~/.zisk/bin/ziskemu -e guest/build/guest-accel-v1.elf -i "$INPUT" \
  -o work/gist/accelerated-zisk.out -X
```

Recorded result: **263,371,236 ZisK steps** (0.18.0: 263,739,098), ~16.4s
wall (`ziskemu -X`, including the cost/opcode breakdown report), output
bytes identical to issue #54's recorded 69-byte result (root/succ/tail all
match, including the success byte `01` at offset 32):

```text
7734570c97a937506b9b771b328a2e5bdb8b74af65c54c747603e4b3d1e8d7ce0125000000b68c2ca6010000000c0000000400000008000000080000000000000000000000
```

## Generate and verify the proof

`-o` takes a single output file; `prove` always aggregates into one Vadcop
Final proof:

```bash
time nice -n 15 cargo-zisk prove -e guest/build/guest-accel-v1.elf -i "$INPUT" \
  -o work/proof-block115260.json -y
cargo-zisk verify -p work/proof-block115260.json
```

Recorded result: **45 AIR instances** (16× Main, 4× Mem, 4× Sha256f, 3×
BinaryHuge, 2× Keccakf, 2× ArithEq384Large, plus one each of Arith,
Arith256XLarge, ArithEq, ArithEq384, BinaryAddHiHuge, BinaryExtension,
BinaryExtensionLarge, InputData, MemAlign, MemAlignReadByteLarge,
MemAlignWriteByte, Rom, VirtualTableZisk0, VirtualTableZisk1), folded into
one Vadcop Final proof. This is far fewer instances than 0.18.0's 127 (Main
alone dropped from 63 to 16), consistent with 1.x's trace-packing
improvements rather than a smaller proof — file size is essentially
unchanged (see below). Verified both in-process (`-y`) and standalone
(`cargo-zisk verify`, 58ms).

| Stage | Time |
| --- | --- |
| Execute (witness/plan) | 4.8s |
| Calculating contributions | 578.7s (9.6 min) |
| Generating inner proofs | 2459.8s (41.0 min) |
| Generating Vadcop final proof | 4.2s |
| **Total proving** | **~3047s (50.8 min)** |

Wall clock for the whole `prove` invocation: **51m9s**; **1010m22s** of
user CPU time and **6m26s** of system time consumed across all cores over
that wall time. Wall clock and user CPU are close to 0.18.0's figures
(47m29s wall, 955m user), but system time dropped sharply (234m10s →
6m26s, roughly a 97% reduction) — a real kernel/syscall-overhead
improvement somewhere in the 1.x proving pipeline, not something specific
to this guest. The proof file is **415,248 bytes** (close to `hello.pnk`'s
and the EEST fixture's proofs in
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md), about 10% bigger
than 0.18.0's 375,809 bytes — the aggregated proof is fixed-size regardless
of the underlying execution length).

This machine was not under contention for this run (contrast with the
0.18.0 run recorded previously, where the first two attempts were
OOM-killed by unrelated load spikes on this shared host).

## Notes

* This is a genuine chain block (`glamsterdam-devnet-7` #115260), not a
  synthetic EEST test case — see
  [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) for the
  smaller/faster fixture-based walkthrough.
* The *software* guest was not proved here.
* `work/gist/archive`, `work/gist/inputs`, and the proof file are left out
  of version control (large, regenerable); this doc is the reproducible
  record.
