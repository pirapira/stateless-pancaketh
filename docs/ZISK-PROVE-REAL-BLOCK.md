# Prove a real chain block on ZisK

[docs/ZISK-PROVE.md](ZISK-PROVE.md) reproduces the `ziskemu`-run-plus-proof
pipeline against a synthetic EEST test fixture. This does the same thing
against an actual chain block: `glamsterdam-devnet-7` block `115260`, the
same block used for the gist comparison in
[issue #54](https://github.com/pirapira/stateless-pancaketh/issues/54)
(`M5: reproduce the gist comparison on devnet-7 block 115260`). Read
`docs/ZISK-PROVE.md` first for the guest-build prerequisites, the `ziskemu`
input-length/`-l` notes, and the `-o DIR/proofs` gotcha; this doc only adds
the real-block-specific steps.

Because of the size of a full block (568,669-byte stateless input, vs. a few
KB for an EEST fixture), this uses the **accelerated** guest
(`guest-accel.elf`, `ACCEL=1` build) rather than the software guest: issue
#54 already measured the software guest at `6,152,130,715` ZisK steps versus
`256,756,696` for the accelerated guest on this same block (a 23.96x
difference), and proving cost scales with step count, so proving the
software guest here would take on the order of a day rather than half an
hour. `nice` is used throughout, per the same CPU-load note as
`docs/ZISK-PROVE.md`.

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

Versions used for the run recorded below (same host as `docs/ZISK-PROVE.md`):
`ziskemu`/`cargo-zisk` 0.16.0, `cake` from CakeML release v3479 (prebuilt
`cake-x64-64`), `cakeml` submodule `857f0d98d`, guest source
`stateless-pancaketh` `7c31f1f` (after #71, acyclic call graph), Ubuntu 24.04.4,
16 physical cores. The first recording of this document (before #71, with a
bootstrapped `cake`) measured 256,756,696 steps and a 27m21s proof; those
numbers are kept below for comparison.

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

CAKE="${CAKE:-$PWD/cakeml/developers/bin/cake}" tools/build_both.sh

python3 evm-asm/scripts/eest-stateless-to-input.py \
  --fixtures-dir work/gist/archive/blockchain_tests \
  --out-dir work/gist/inputs \
  --filter '115260-' --limit 1 --verify-input-parity
```

This writes `work/gist/inputs/00000_block_115260_..._b0.input` (568,680
bytes: the 568,669-byte stateless input, padded to a multiple of 8) and a
one-row manifest whose expected-output column reproduces issue #54's
recorded hex exactly.

## Emulate and confirm the result

```bash
INPUT=work/gist/inputs/00000_block_115260_3c8d1842a0538d9f67a091fc4b7ab007be665735c2b0ddebeb5a313c382f0764_b0.input
time ~/.zisk/bin/ziskemu -e guest/build/guest-accel.elf -i "$INPUT" \
  -o work/gist/accelerated-zisk.out -X
```

Recorded result: **263,738,968 ZisK steps** (256,756,696 before #71; the
explicit call/tree stacks of the acyclic guest cost 2.7%), `11.6s` wall
(`ziskemu -X`, including the cost/opcode breakdown report), output bytes
identical to issue #54's recorded 69-byte result (root/succ/tail all match,
including the success byte `01` at offset 32):

```text
7734570c97a937506b9b771b328a2e5bdb8b74af65c54c747603e4b3d1e8d7ce0125000000b68c2ca6010000000c0000000400000008000000080000000000000000000000
```

## Generate and verify the proof

```bash
mkdir -p work/proof-block115260/proofs
time nice -n 15 cargo-zisk prove -e guest/build/guest-accel.elf -i "$INPUT" \
  -l -o work/proof-block115260 -b -y
```

Recorded result: **127 AIR instances** (63× Main, 16× Mem, 10×
BinaryAdd, 9× Binary, 5× ArithEq384, 4× Sha256f, 3× ArithEq, 3×
BinaryExtension, 3× Keccakf, 2× MemAlignReadByte, plus one each of Arith,
InputData, MemAlign, MemAlignWriteByte, Rom, RomData, SpecifiedRanges,
VirtualTable0, VirtualTable1) — 7x the 18 instances the small EEST fixture
needed, tracking the 14x step-count difference sublinearly since most of
the extra instances are additional copies of the same fixed-size AIRs.
(Before #71: 125 instances, 62× Main and 15× Mem.) Every instance verified;
global constraints verified.

| Stage | Time |
| --- | --- |
| Execute (witness/plan) | 4.7s |
| Calculating contributions | 376.4s (6.3 min) |
| Generating inner proofs | 1273.0s (21.2 min) |
| Verifying proofs | 21.9s |
| **Total proving** | **~1676s (27.9 min)** |

Wall clock for the whole `prove` invocation: **27m59s** (27m21s before #71);
**1.2 GB** of proof JSON under `work/proof-block115260/proofs/` (127 files).
`755m` of user CPU time and `97m` of system time were consumed across all
cores over that wall time — the `nice -n 15` above is what keeps this from
starving other work on a shared machine; without it, expect the same total CPU
time to complete faster but at the cost of everything else on the box.

## Notes

* This is a genuine chain block (`glamsterdam-devnet-7` #115260), not a
  synthetic EEST test case — see `docs/ZISK-PROVE.md` for that distinction
  and for the smaller/faster fixture-based walkthrough.
* Proving the *software* guest on this block was not attempted here; based
  on its 23.96x larger step count (issue #54) and the near-linear scaling
  observed between the EEST fixture (18 instances, ~214s) and this block (127
  instances, ~1676s), it would plausibly take on the order of hours. Someone
  wanting that number should budget accordingly and still run it under
  `nice`.
* `work/gist/archive`, `work/gist/inputs`, and `work/proof-block115260` are
  left out of version control (large, regenerable); this doc is the
  reproducible record.
