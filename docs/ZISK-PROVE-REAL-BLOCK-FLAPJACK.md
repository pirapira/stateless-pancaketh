# Prove a real chain block on ZisK, guest compiled by flapjack

This is [docs/ZISK-PROVE-REAL-BLOCK.md](ZISK-PROVE-REAL-BLOCK.md)'s pipeline
against the same real chain block, with the guest compiled by `flapjack`
(the Lean 4 port of the Pancake compiler, `lake exe flapjack-compile`)
instead of `cake`. See [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md)
for the compiler-swap mechanics (`COMPILER=flapjack guest/build.sh ...`) and
the correctness comparison against `cake` on the 30-fixture baseline; this
document only adds the real-block-specific steps, exactly mirroring
`docs/ZISK-PROVE-REAL-BLOCK.md`'s structure.

Like that document, this uses the **accelerated** guest
(`guest-accel.elf`, `ACCEL=1` build) only — the software guest's step count
on this block is over 20x larger and would take on the order of hours to
prove.

**Correctness first.** Before proving, the flapjack-compiled
`guest-accel.elf` was checked against a fresh `cake`-compiled
`guest-accel.elf` (same `guest/src`) on this exact block:

* Identical `ziskemu -X` step count (263,739,098) and byte-identical output
  on both compilers.
* The output's first 69 bytes match `issue #54`'s recorded expected result
  exactly (same hex as `docs/ZISK-PROVE-REAL-BLOCK.md` records), and the
  `eest-stateless-to-input.py --verify-input-parity` conversion step (below)
  independently reproduces that same expected-output hex from the archive.

## Fixture

Same block as `docs/ZISK-PROVE-REAL-BLOCK.md` and issue #54:

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
| `cake` (comparison reference only) | bootstrapped, CakeML `e8eca63` |
| `cakeml` submodule | `857f0d98da8f8a3580f34423338e697809308ede` |
| `evm-asm` submodule | `7e65e4d024718f704226cd795f3d03d4e9aafe13` |
| guest source | `stateless-pancaketh` `43222a3` |
| Host | Ubuntu 24.04.5, 32 cores |

`docs/ZISK-PROVE-REAL-BLOCK.md`'s own recorded run used ZisK 0.16.0 and the
`cake`-built guest; its 263,738,968-step count differs from the
263,739,098 recorded here only because `guest/src` has changed slightly
since that recording (more precompiles, bug fixes) — both compilers give
the exact same count against the *current* source (see "Correctness
first").

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

Same output as `docs/ZISK-PROVE-REAL-BLOCK.md`: `work/gist/inputs/00000_block_115260_..._b0.input`
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
including the cost/opcode breakdown report), output bytes identical to issue
#54's recorded 69-byte result and to a fresh `cake` build's output on this
block (root/succ/tail all match, including the success byte `01` at offset
32):

```text
7734570c97a937506b9b771b328a2e5bdb8b74af65c54c747603e4b3d1e8d7ce0125000000b68c2ca6010000000c0000000400000008000000080000000000000000000000
```

## Generate and verify the proof

ZisK 0.18.0's `prove` aggregates into one file rather than 0.16.0's
per-AIR `-b`/`DIR/proofs` layout (see
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md)'s "ZisK version"
section):

```bash
time nice -n 15 cargo-zisk prove -e guest/build/guest-accel.elf -i "$INPUT" \
  -l -o work/proof-block115260.json -y
```

Recorded result: **127 AIR instances** (63× Main, 16× Mem, 10× BinaryAdd,
9× Binary, 5× ArithEq384, 4× Sha256f, 3× ArithEq, 3× BinaryExtension, 3×
Keccakf, 2× MemAlignReadByte, plus one each of Arith, InputData, MemAlign,
MemAlignWriteByte, Rom, RomData, SpecifiedRanges, VirtualTable0,
VirtualTable1) — the exact same composition `docs/ZISK-PROVE-REAL-BLOCK.md`
recorded for the `cake`/0.16.0 build, folded here into one Vadcop Final
proof instead of per-AIR JSON files. Verified both in-process (`-y`) and
standalone (`cargo-zisk verify`, 50ms).

| Stage | Time |
| --- | --- |
| Execute (witness/plan) | 5.7s |
| Calculating contributions | 479.6s (8.0 min) |
| Generating inner proofs | 2353.1s (39.2 min) |
| Generating Vadcop final proof | 4.7s |
| Verifying Vadcop final proof (in-process) | 0.02s |
| **Total proving** | **~2843s (47.4 min)** |

Wall clock for the whole `prove` invocation (including proving-key load):
**47m29s** (vs. `docs/ZISK-PROVE-REAL-BLOCK.md`'s 27m59s on 0.16.0 — a ~1.7x
slowdown; 0.18.0's recursive aggregation is real extra work, in the same
~1.5-1.9x range seen on the small `hello.pnk`/EEST-fixture runs in
`docs/ZISK-PROVE-FLAPJACK.md`); **955m** of user
CPU time and **234m** of system time consumed across all cores over that
wall time (`nice -n 15` is what keeps this from starving other work on a
shared machine). The proof file is **376 KB (375,809 bytes)** — identical in
size to the small `hello.pnk`/EEST-fixture proofs in
`docs/ZISK-PROVE-FLAPJACK.md` (the aggregated proof is fixed-size regardless
of the underlying execution length), versus 0.16.0's 1.2 GB of per-AIR JSON.

This machine is shared with other tenants; the first two attempts at this
proof were OOM-killed partway through (once during contribution
calculation, once at the very start) when system load spiked from unrelated
processes (load average briefly over 40 on this host). The run recorded
above succeeded once load dropped back to single digits. This is a
host-contention issue, not a `flapjack`/`cake` or ZisK-version difference —
worth knowing if reproducing this on a busy shared machine.

## Notes

* This is the same genuine chain block as `docs/ZISK-PROVE-REAL-BLOCK.md`
  (`glamsterdam-devnet-7` #115260), just with the guest compiled by
  `flapjack` instead of `cake`.
* As in that document, the *software* guest was not proved here — the same
  ~24x step-count multiplier applies regardless of which compiler produced
  the guest, since flapjack and cake produce instruction-identical code (see
  "Correctness first").
* `work/gist/archive`, `work/gist/inputs`, and the proof file are left out
  of version control (large, regenerable); this doc is the reproducible
  record.
