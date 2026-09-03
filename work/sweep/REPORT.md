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
```

## Totals

| Result | Count |
| --- | ---: |
| `PASS(full)` | 26,090 |
| `PASS(malformed)` | 8 |
| `FAIL` | 6 |
| **Total** | **26,104** |

## Failure histogram

The failure histogram is keyed by result regions and the debug class/code
bytes recorded after the expected result.

| Regions | Fail class/code | Count |
| --- | --- | ---: |
| `----/----/----` | `0/0` | 6 |

All six failures have `output[100] = 0` (stage marker). They return the
`@trap` marker at the success byte rather than a normal debug failure code, so
`0/0` here identifies the trap-shaped result and is not the usual `1/99`
precompile failure sentinel.

## Follow-up issue

One follow-up issue, [#47](https://github.com/pirapira/stateless-pancaketh/issues/47), was filed for the distinct non-`1/99` code:

* `0/0`: six failures, stage marker `output[100] = 0`. Representative labels
  (the report caps this list at five):
  `15787_test_contract_creation_spam_fork_Amsterdam-blockchain_test_from_state_test__b0`,
  `18635_test_return50000_fork_Amsterdam-blockchain_test_from_state_test--g1__b0`,
  `18637_test_return50000_2_fork_Amsterdam-blockchain_test_from_state_test--g1__b0`,
  `20981_test_static_loop_calls_then_revert_fork_Amsterdam-blockchain_test_from_state_test--g0__b0`,
  `20982_test_static_loop_calls_then_revert_fork_Amsterdam-blockchain_test_from_state_test--g1__b0`
  (one additional label is recorded in `all.json`).

Rerun the group after rebuilding the accelerated guest with:

```bash
tools/eest-run.py guest/build/guest-accel.elf work/sweep/manifest.tsv \
  --from-json work/sweep/all.json --fail-code 0/0 --jobs 32 \
  --out-dir work/sweep/rerun-0-0
```
