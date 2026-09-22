# Reproduce the full EEST run with Spike

This is the complete `tests-zkevm` stateless-fixture run, not the small
`tools/check_all.sh` sample. `tools/eest-run.py` compares each guest result
with the fixture's `statelessOutputBytes` and reports root, success, and tail
regions. The command below uses the accelerated guest under Spike: `ACCEL=1`
selects the same precompile acceleration points that Spike implements, while
the runner itself remains Spike-only. No ziskemu is needed. The guest is
built with `flapjack` (`guest/build.sh`'s default `COMPILER`); pass
`COMPILER=cake` instead to use a bootstrapped/prebuilt CakeML `cake` binary.

## Prerequisites

Follow `README.md`'s "Quick start" section first: it covers cloning, the
`lake`/`elan`, `riscv64-unknown-elf-{as,ld}`, and Spike-build
(`libboost-all-dev`, `device-tree-compiler`, `libssl-dev`) prerequisites,
initializing the `evm-asm` and `riscv-isa-sim` submodules, and building
`spike_run`. This document only adds the full-corpus-specific steps below,
against the EEST fixture tag this repo currently pins
(`evm-asm/scripts/eest-fixture-tag.txt`; `tests-zkevm@v0.6.2` for the
recorded run below).

## Fetch, convert, build, and run all fixtures

`tools/eest-spike-full.sh` fetches the pinned EEST fixture tag, converts the
whole corpus, builds the accelerated guest, and runs it under Spike:

```bash
tools/eest-spike-full.sh
```

Its output directory is named with the source commit
(`work/eest-spike-<commit>`) so result files can't be mistaken for a run
from another checkout; re-running it with the same commit checked out
reuses that directory's manifest. `SPIKE_RUN` and `EEST_JOBS` (default 32)
are overridable env vars; see the script for details.

`eest-run` exits zero only when every record passes, which is
`tools/eest-spike-full.sh`'s own exit code. A nonzero exit is useful: the
JSON and per-fixture logs remain under the commit-named run directory for
inspection and reruns with `--from-json` or `--labels`.

## Recorded result

Run on stateless-pancaketh commit
`1489defbef04e9c22be83152ad53af145f2094b8`, with 32 Spike workers and the
accelerated guest, built with `cake` (the only compiler `guest/build.sh`
supported at that commit; today's default is `flapjack`, which builds an
instruction-for-instruction identical guest — see the "Status" section of
`README.md` and [docs/FLAPJACK-CORRECTNESS.md](FLAPJACK-CORRECTNESS.md) for
the correctness comparison):

```text
records: 26104
PASS(full): 26096
PASS(malformed): 8
eest-run exit: 0
```

There were no fixture failures. The commit-qualified run directory and result
JSON are the reproducible record for this passing revision; the tracked
`work/sweep/all.json.gz` is not used by this command. This full-corpus sweep
has not yet been independently re-run with `flapjack`; the procedure above
builds with it by default for anyone reproducing this today.
