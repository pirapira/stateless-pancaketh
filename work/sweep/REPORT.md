# Full EEST sweep report

The complete `tests-zkevm@v0.6.2` fixture tree was converted to
`work/sweep/manifest.tsv`: 26,104 stateless blocks from 6,333 fixture JSON
files. The manifest contains relative input paths and was reused unchanged on
a second `tools/make-inputs.sh --all work/sweep` invocation.

The sweep used the accelerated guest under Spike so that the BLS and KZG
precompile cases completed in a practical time. The acceleration path is the
same Spike CSR extension used by the guest's `ACCEL=1` build; ziskemu was not
used for correctness testing.

Command:

```bash
ACCEL=1 guest/build.sh guest/src/main.pnk guest/build/guest-accel.elf
tools/eest-run.py guest/build/guest-accel.elf work/sweep/manifest.tsv \
  --jobs 32 --quiet-passes --json work/sweep/all.json \
  --out-dir work/sweep/run-accel
gzip -c work/sweep/all.json > work/sweep/all.json.gz
```

## Totals

| Result | Count |
| --- | ---: |
| `PASS(full)` | 26,096 |
| `PASS(malformed)` | 8 |
| `FAIL` | 0 |
| **Total** | **26,104** |

## Failure histogram

The failure histogram is keyed by result regions and the debug class/code
bytes recorded after the expected result.

There are no failures in the refreshed result set.

## Issue #47 resolution

The six former `0/0` trap-shaped results from [#47](https://github.com/pirapira/stateless-pancaketh/issues/47)
were rerun after separating persistent heap, frame memory, and frame scratch.
The fix also gives retained log addresses and receipt-log lists stable
ownership. All six are now `PASS(full)` on both the software and accelerated
guest builds under Spike, with byte-identical result payloads across builds.

The targeted accelerated rerun can be reproduced with one numeric fixture
prefix per invocation:

```bash
for fixture in 15787 18635 18637 20981 20982 20992; do
  SPIKE_RUN=/path/to/evm-asm/scripts/spike/spike_run \
    tools/eest-run.py guest/build/guest-accel.elf work/sweep/manifest.tsv \
    --filter "${fixture}_" --jobs 1 --quiet-passes \
    --out-dir "work/sweep/rerun-${fixture}" \
    --json "work/sweep/rerun-${fixture}.json"
done
```

Repeat the loop with `guest/build/guest.elf` to run the software build. The
base and accelerated result JSON files were compared before refreshing
`all.json.gz`; the checked-in archive is the resulting full-sweep result set.
