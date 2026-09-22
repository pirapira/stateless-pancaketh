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

On Debian or Ubuntu, install the host tools and RISC-V binutils:

```bash
sudo apt-get update
sudo apt-get install -y build-essential binutils-riscv64-unknown-elf \
  device-tree-compiler libboost-all-dev libssl-dev python3 git curl tar
```

`flapjack` is a `lake` dependency of this repo (`lakefile.toml`), pinned by
commit; no separate checkout or bootstrap step is needed beyond `lake
build` (triggered automatically on first use).

## Fresh checkout and pinned Spike backend

The recorded run below (see "Recorded result") used these revisions; the
`riscv-isa-sim` pin still applies to a fresh run today, since Spike itself
is unaffected by which Pancake compiler builds the guest:

| Component | Revision / tag |
| --- | --- |
| `evm-asm` submodule | `f6b685c3d1d26a4850c908480261ac4903afc566` |
| `riscv-isa-sim` | `55b4658dbf574ba0b714083ec436ce2cb5be1998` |
| EEST fixtures | `tests-zkevm@v0.6.2` |

Clone the repository:

```bash
git clone --recurse-submodules https://github.com/pirapira/stateless-pancaketh.git
cd stateless-pancaketh
```

Build the pinned Spike driver. `SPIKE_SRC` may point at an existing
`riscv-isa-sim` checkout; the default puts it beside this repository.

```bash
REPO_ROOT="$(pwd)"
SPIKE_COMMIT=55b4658dbf574ba0b714083ec436ce2cb5be1998
SPIKE_SRC="${SPIKE_SRC:-$REPO_ROOT/../riscv-isa-sim}"
JOBS="${EEST_JOBS:-32}"

if [[ ! -d "$SPIKE_SRC/.git" ]]; then
  git clone https://github.com/riscv-software-src/riscv-isa-sim.git "$SPIKE_SRC"
fi
git -C "$SPIKE_SRC" fetch origin "$SPIKE_COMMIT"
git -C "$SPIKE_SRC" checkout --detach "$SPIKE_COMMIT"
mkdir -p "$SPIKE_SRC/build"
if [[ ! -f "$SPIKE_SRC/build/Makefile" ]]; then
  (cd "$SPIKE_SRC/build" && ../configure --prefix="$SPIKE_SRC/build/install")
fi
make -C "$SPIKE_SRC/build" -j"$JOBS"
SPIKE_SRC="$SPIKE_SRC" SPIKE_BUILD="$SPIKE_SRC/build" \
  "$REPO_ROOT/evm-asm/scripts/spike/build.sh"
```

## Fetch, convert, build, and run all fixtures

The output directory is named with the source commit so that result files
cannot be mistaken for a run from another checkout. Re-running the command
with the same directory reuses its manifest.

```bash
set -u -o pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"
RESULT_COMMIT="$(git rev-parse HEAD)"
TAG="$(tr -d '[:space:]' < evm-asm/scripts/eest-fixture-tag.txt)"
SPIKE_RUN="${SPIKE_RUN:-$REPO_ROOT/evm-asm/scripts/spike/spike_run}"
JOBS="${EEST_JOBS:-32}"
RUN_ROOT="$REPO_ROOT/work/eest-spike-$RESULT_COMMIT"

test -x "$SPIKE_RUN"

evm-asm/scripts/eest-fetch-fixtures.sh "$TAG"
tools/make-inputs.sh --all "$RUN_ROOT/inputs"
ACCEL=1 guest/build.sh guest/src/main.pnk \
  "$RUN_ROOT/guest-accel.elf"

set +e
SPIKE_RUN="$SPIKE_RUN" python3 tools/eest-run.py \
  "$RUN_ROOT/guest-accel.elf" "$RUN_ROOT/inputs/manifest.tsv" \
  --jobs "$JOBS" --quiet-passes \
  --json "$RUN_ROOT/results.json" --out-dir "$RUN_ROOT/run-accel"
RUN_RC=$?
set -e

python3 - "$RUN_ROOT/results.json" <<'PY'
import collections
import json
import sys

results = json.load(open(sys.argv[1], encoding="utf-8"))
counts = collections.Counter(record["class"] for record in results)
print(f"records: {len(results)}")
for name in ("PASS(full)", "PASS(malformed)", "FAIL", "ERROR"):
    if counts[name]:
        print(f"{name}: {counts[name]}")
PY
printf 'eest-run exit: %s\n' "$RUN_RC"
exit "$RUN_RC"
```

`eest-run` exits zero only when every record passes. A nonzero exit is useful:
the JSON and per-fixture logs remain under the commit-named run directory for
inspection and reruns with `--from-json` or `--labels`.

## Recorded result

Run on stateless-pancaketh commit
`1489defbef04e9c22be83152ad53af145f2094b8`, with 32 Spike workers and the
accelerated guest, built with `cake` (the only compiler `guest/build.sh`
supported at that commit; today's default is `flapjack`, which builds an
instruction-for-instruction identical guest — see the "Status" section of
`README.md` and [docs/ZISK-PROVE-FLAPJACK.md](ZISK-PROVE-FLAPJACK.md) for
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
