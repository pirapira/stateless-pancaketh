# flapjack vs. the original toolchain: correctness comparison

`flapjack` (the Lean 4 port of the Pancake compiler) is newer than the
bootstrapped/prebuilt `cake` binary this guest was originally built with
(`cake --pancake --target=riscv`, from the HOL4-verified CakeML compiler).
Before treating flapjack's ziskemu/proving numbers as meaningful,
[docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) and
[docs/ZISK-PROVE-REAL-BLOCK-FLAPJACK.md](ZISK-PROVE-REAL-BLOCK-FLAPJACK.md)
both check the flapjack-compiled guest against a fresh `cake`-compiled one
first. This document records those checks; neither of the two documents
above needs `cake` for anything else.

## Getting a `cake` build for comparison

A CakeML `cake` executable with Pancake support. Either bootstrap it from
the pinned `cakeml` submodule (see `README.md`'s Toolchain section) or use
CakeML's prebuilt release, which only needs a C compiler:

```bash
gh release download v3479 -R CakeML/cakeml -p cake-x64-64.tar.gz
tar xzf cake-x64-64.tar.gz && (cd cake-x64-64 && make)   # ~2s: cake.S + basis_ffi.c
export CAKE="$PWD/cake-x64-64/cake"
```

## 30-fixture baseline

Before recording any of `docs/ZISK-PROVE-FLAPJACK.md`'s ziskemu/proving
numbers, the flapjack-compiled guest was checked against the
`cake`-compiled guest (built fresh from the same `guest/src`, non-`DEBUG`)
on the 30-fixture baseline (`work/inputs/manifest.tsv`):

* `guest.elf` (software) and `guest-accel.elf` (`ACCEL=1`): byte-identical
  Spike/ziskemu output and identical step counts on all 30/30 fixtures; the
  disassembled `.text` is byte-identical to `cake`'s output (only the ELF's
  non-code bytes, e.g. symbol-table ordering, differ); the two compilers emit
  the exact same 40 static-analysis warnings across the same 12 functions.
* `tools/eest-run.py guest/build/guest.elf work/inputs/manifest.tsv` and the
  `guest-accel.elf` equivalent both report `30/30 PASS(full)` against the
  Python oracle for the flapjack build.
* `hello.pnk`: **1,032 steps** with a bootstrapped-`cake` build; a
  prebuilt-release `cake` build instead gives 906 — the two `cake` builds
  emit slightly different code, and flapjack matches whichever `cake` build
  it is compared against instruction-for-instruction. Output bytes match a
  fresh `cake` build exactly.
* EEST fixture 00000: **18,864,486 ZisK steps** for the software guest and
  **2,584,624** for the accelerated guest — identical to a fresh `cake`
  build's step counts and output bytes on this fixture.

This is a new milestone: `flapjack-compile` could not build the full guest as
recently as the pin bumped in #97 (see the "Toolchain" section of
`README.md` for the issues that blocked it); at the pin used here it not only
builds but matches `cake` instruction-for-instruction on this guest.

Versions used:

| Component | Version / commit |
| --- | --- |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `cake` | bootstrapped, CakeML `e8eca63` |
| `cakeml` submodule | `857f0d98da8f8a3580f34423338e697809308ede` |
| guest source | `stateless-pancaketh` `7c31f1f` |

## Real chain block (`glamsterdam-devnet-7` #115260)

Before proving `docs/ZISK-PROVE-REAL-BLOCK-FLAPJACK.md`'s recorded run, the
flapjack-compiled `guest-accel.elf` was checked against a fresh
`cake`-compiled `guest-accel.elf` (same `guest/src`) on this exact block:

* Identical `ziskemu -X` step count (263,739,098) and byte-identical output
  on both compilers.
* The output's first 69 bytes match [issue #54](https://github.com/pirapira/stateless-pancaketh/issues/54)'s
  recorded expected result exactly, and the
  `eest-stateless-to-input.py --verify-input-parity` conversion step
  independently reproduces that same expected-output hex from the archive.

An earlier `cake`-built run on this same block recorded 263,738,968 steps;
the small difference from the 263,739,098 recorded here is only because
`guest/src` has changed slightly since that recording (more precompiles,
bug fixes) — both compilers give the exact same count against the
*current* source.

The software guest was not compared on this block: issue #54 already
measured a ~24x step-count multiplier for the software guest over the
accelerated one there, and that multiplier applies regardless of which
compiler produced the guest, since flapjack and cake produce
instruction-identical code (above).

Versions used:

| Component | Version / commit |
| --- | --- |
| `flapjack` (lake dependency) | `2732831e21be0a32e3135417f39563cc1124a8d4` |
| `cake` | bootstrapped, CakeML `e8eca63` |
| `cakeml` submodule | `857f0d98da8f8a3580f34423338e697809308ede` |
| guest source | `stateless-pancaketh` `43222a3` |
