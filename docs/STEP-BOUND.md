# Goal 1 (issue #73): a source-level Pancake step bound for the guest

Status of the three `sorry`s of `Guest/StepBound.lean`:

| | state |
|---|---|
| `declaredBlockGasLimit` | **done** — `Guest/InputDecode.lean`, differentially validated against the guest |
| `guestPancakeStepBound` | open |
| `guest_terminates_within_step_bound` | **false as stated** — see [The obstruction](#the-obstruction) |

## `declaredBlockGasLimit`

`Guest/InputDecode.lean` mirrors the guest's own decoder — `decode_stateless_input`,
`decode_payload`, `decode_requests`, `decode_bytes_list` and the helpers
`ssz_check_offsets`, `ssz_split_var_list`, `ssz_fixed_list_count`,
`ssz_optional_u64` of `guest/src/ssz.pnk`, with the field offsets and list
limits of `guest/src/types.h` — as a function of the input bytes. Every
`ssz_fail` site is a `none`, in the guest's order, so
`InputDecode.decodeStatelessInput` is `some` on exactly the inputs on which the
guest returns rather than raising `SszErr`. `declaredBlockGasLimit` is the
payload's `gas_limit` field, which `fork.pnk` copies to `HDR_GAS_LIMIT` and
then to `BE_GAS_LIMIT`.

The record it returns also carries the transaction slices, witness node/code/header
slices and the request counts — the sizes a parametric bound would be stated in
terms of — so it is not only the gas limit.

### Validation

`main` returns `1` from its `catch SszErr` block and `0` once
`decode_stateless_input` has returned, so the value the run returns is an exact
oracle for "this input decodes". `lake exe input-decode-check` compares the two
on a corpus that `tools/ssz-inputs.py` generates:

```bash
tools/ssz-inputs.py work/ssz-inputs --fuzz
lake exe input-decode-check work/ssz-inputs/*.bin
```

* 45 base cases — a minimal well-formed `StatelessInput`; variants with
  non-empty extra data, transactions, withdrawals, block access list, witness
  lists, public keys and fork activations; gas limits 1, 200M and 2^64−1; 24
  single-byte mutations; 10 truncations. **31 decoded, 14 rejected, 0
  mismatches.**
* `--fuzz` adds 386 cases: every SSZ offset field of two base inputs set to
  each of eight boundary values (0, ±1, +4, the body length, one past it,
  `0xffffffff`, half the length) — the bytes a hand-written mirror is most
  likely to disagree on. **0 mismatches.**

Since the model is quadratic in the store count, the corpus deliberately keeps
every list small; see the note at the end of this file.

## The obstruction

`guest_terminates_within_step_bound` is false as stated, for every value of
`guestPancakeStepBound`. The premises admit inputs on which
`runGuestStepped input fuel = none` for every `fuel`, so `TerminatesWithin`
fails — and it fails on evaluation failure, which the theorem is meant to rule
out.

### Mechanism

1. `@trap` returns in the model. `guestMemoryFfi` (`Guest/Accel.lean:155`)
   answers `halt` and `trap` with `some memory`, so the run continues. On the
   machine `ffitrap` (`guest/runtime/start.S`) halts and never returns. The
   `Guest/Model.lean` docstring notes this and calls it a safe
   over-approximation. It is not, in two ways: for `TerminatesWithin` it turns
   a halting machine run into an evaluation failure (step 3), and even when the
   run does complete, continuing past the trap can take a *different* path and
   reach a different control outcome and output than the machine's halt — see
   the 19,456-byte row in the sweep below.
2. So `alloc` keeps allocating past the heap. `alloc`
   (`guest/src/lib/mem.pnk:28`) calls `trap_with(1)` when
   `q >+ HEAP_END` and then, because the trap returned, executes
   `heap_ptr = q` and hands out an address beyond `HEAP_END`.
3. Byte-granular accesses above `HEAP_END` are unmapped, and unmapped means
   `none`. `guestInitialMemory` maps `[SCRATCH_BASE, HEAP_END)` only. Word
   stores extend the map (`panValueMemoryAccessOfModel` is built with the
   default `domain := fun _ => true`), but `ld8`/`st8` go through
   `panModelReadByte`/`panModelStoreByte`, which read the containing word cell
   and fail when it is absent. The guest has 697 byte-access sites (560 `ld8`,
   137 `st8`); the error paths after a trap reach one, and the whole stepped run
   is then `none`.

### Reproduction

The relationship that matters is "`alloc` traps exactly at the end of the
mapped region", and that is preserved if the heap is made smaller: moving
`@base` up (`baseAddress := heapEnd - budget`) leaves `HEAP_END` and the mapped
region where they are, so it is the real configuration at a smaller heap size.
The guest's own init allocations high-water at 17,408 bytes; from there:

| heap | input | result |
|---|---|---|
| high-water + 512 B | 2,000 B | **`none`** — `alloc(2008)` in `input_blob` overruns |
| high-water + 4,096 B | 2,000 B | returns normally, 24,544 steps |
| high-water + 512 B | 0 B | returns normally, 19,778 steps |

So it is the allocation, not the input's content, that turns the run into an
evaluation failure.

Sweeping the heap budget in 1 KiB steps from the init high-water, on the
minimal well-formed input of `Guest.InputDecode`'s test set (658 bytes,
`declaredBlockGasLimit = some 200000000`), against the same guest with the
`throw TrapErr` of fix 1 below:

| heap | baseline | with `throw TrapErr` |
|---|---|---|
| 17,408 B | `none` | `raised TrapErr 1`, 18,170 steps |
| 18,432 B | `none` | `raised TrapErr 1`, 23,566 steps |
| 19,456 B | returns normally, **137,650** steps | `raised TrapErr 1`, 28,597 steps |
| 20,480 B … 40,960 B (21 budgets) | returns normally, 137,596 steps | identical, 137,596 steps |

Two things to read off it. The baseline has two evaluation failures and the
patched guest none. And at 19,456 bytes the baseline *completed* a run the
machine would have halted, by a path 54 steps longer than the untrapped
one — the over-approximation claim does not hold even for runs that finish.

### At the real configuration

The heap is `HEAP_END − HEAP_BASE` = 2,952,790,016 − 2,701,131,776 =
**251,658,240 bytes (240 MiB)**, and `maxInputBytes` is **1,073,741,808 bytes**
— 4.27× the whole heap. `input_blob` (`guest/src/lib/mem.pnk:304`) reads the
host's length word and immediately does `alloc(len + 8)` with no check, so

> every input longer than 251,658,232 bytes traps in `input_blob`.

Smaller inputs do it too, through amplification. `main` calls
`htr_new_payload_request` unconditionally once the input decodes, and that
reaches `htr_bytes_list` on the `block_access_list`: `pack_bytes` allocates
≈L and `merkleize`'s buffer ≤2L, both live at once, on top of the L the input
copy already holds. So an input of order 60 MiB whose block access list is most
of its bulk exhausts the heap as well.

Such inputs decode. The only length-dependent guard on the
`block_access_list` is `len - o_bal >+ MAX_BLOCK_ACCESS_LIST_BYTES`, and
`MAX_BLOCK_ACCESS_LIST_BYTES` is 2^30; `MAX_BYTES_PER_TRANSACTION` is also
2^30 and `MAX_WITNESS_NODES × MAX_BYTES_PER_WITNESS_NODE` is 4 GiB. So a
minimal well-formed input padded through its block access list to 300 MiB
decodes, declares whatever `gas_limit` we put in it, and satisfies both
premises.

(The model cannot be run on such an input to show this end to end:
`guestHostMemory` indexes a `List UInt8` per byte, so `input_blob`'s copy loop
is quadratic in the input length. A 100 KB input already does not finish.)

### The fix

The guest is not at fault: on the machine, heap exhaustion is a clean
deterministic halt with `trap=1` in the debug bytes. What is wrong is that
`@trap` returns in the model. Making it terminal fixes the whole class at once
— all seven `trap_with` sites (`alloc`, `frame_mem_alloc`, `scratch_alloc`,
division by zero, base-fee overflow, and the two journal-full sites) become
immediate termination, which `TerminatesWithin` accepts, and the
"trap continues down the error paths" caveat in `Guest/Model.lean` goes away.
Three ways to get there:

1. **Raise instead of returning.** Give `trap_with` a dedicated exception —
   `exception TrapErr : 1;` in `guest/src/lib/mem.pnk`, `throw TrapErr code`
   after the `@trap` — caught nowhere, so it propagates to the top and the run
   ends as `.raised`, which `TerminatesWithin` accepts. Dead code on the
   machine, since `ffitrap` never returns, and it needs no flapjack change.
   Costs a regeneration of the two committed ASTs
   (`tools/gen-guest-ast.sh`; note that on macOS the script needs `CPP='clang
   -E'`, and its `sha256sum` and `sed -i` are GNU-only).

   Prototyped: the two added lines are the whole cpp-expanded diff, and on the
   sweep above every trapping run becomes a clean `TrapErr` and every
   non-trapping run keeps its exact step count. The trap also fires from
   inside `main`'s `try ... catch SszErr` in the 19,456-byte case and is not
   swallowed by it.
2. **Let the memory handler signal a final event** (flapjack). A
   `PanValueMemoryFfiHandler` returns `Option (locals × memory × ffi)`, and the
   `.extCall` case of `evalPanValueFfiProgSteps` consults it unconditionally
   and always continues as `.normal`, so with a memory handler installed there
   is no path to `.finalFfi` at all. Widening its result — or falling through
   to the oracle when it declines — is the architecturally right fix, but it is
   a change in a pinned dependency.
3. **Sharpen the premise.** Not sufficient on its own: a heap-fit hypothesis on
   `input.length` would not cover exhaustion reached from inside the run
   (`frame_mem_alloc`, `scratch_alloc`, `htab_grow`), and it would give up on
   inputs that the machine handles correctly.

Option 1 also *helps* the bound: every resource-exhaustion path becomes
immediate termination rather than a continuation that has to be bounded.

## What the bound itself needs

The guest's call graph is acyclic (#71), so no recursion-depth argument is
needed; what is left is an iteration bound for each loop. The cpp-expanded
accelerated guest has **257 `while` loops**. By loop condition:

* ~200 are counters against a length or a constant (`i <+ n`, `i < cap`,
  `i < 8`, ...). Their bound is the length or the constant.
* The substantive ones are the de-recursified drivers, where termination is the
  real content:
  * `run_frames` (`evm_calls.pnk:681`) — one iteration per opcode executed
    across all frames, plus one per frame completion. Bounded by gas: every
    opcode costs at least 1 gas, gas is conserved across the call tree, so
    iterations ≤ 200M + frames, and frames ≤ 1024 deep and ≤ gas/700.
  * the witness-decode machine, MPT insert/delete descent and unwind
    (`mpt.pnk:410,714,857,919,1075`) — bounded by trie depth 64 and the witness
    node count, itself bounded by the input.
  * RLP nested-list validation (`rlp.pnk:177`) — bounded by the item length.
  * `htab_find_slot`/`htab_insert_raw`/`htab_del`
    (`htab.pnk:187,225,298`) — open-addressing probes with wrap-around, which
    terminate *only* under the load-factor invariant `2·count ≤ cap` that
    `htab_set` maintains by calling `htab_grow`. `htab_del`'s `while true`
    needs the same invariant (it stops at the first empty slot). This invariant
    is a genuine proof obligation, not a formality: a full table would spin
    forever.
  * modular-inverse and reduction loops (`secp256k1.pnk:475`, `fp384.pnk:264`,
    `bn254.pnk:1140`, `modexp.pnk:122`, `u256.pnk:400`) — terminate by a
    decreasing valuation or a bounded carry, all with small constant bounds.

Since the per-iteration cost of `run_frames` is itself data-dependent (KECCAK256
over memory, CALLDATACOPY, MCOPY are metered per word), the bound has to be
proved in the parametric shape the issue suggests, `α·gas + β·inputBytes + γ`,
and only then specialised to a constant.

Measured data points on the accelerated build, for calibration: empty input
19,778 steps; a 2,000-byte input rejected at the schema check 24,544; the
minimal well-formed 658-byte input 137,596; typical single-transaction EEST
fixtures 2.4M–3.4M; a BLS/secp256r1-heavy one 13.9M.

One practical limit on measuring more: `guestHostMemory` indexes a `List UInt8`
per byte and the memory map is a chain of closures, so the model is quadratic in
both input length and store count. A 658-byte input takes 0.7 s; one with a
64 KiB witness code does not finish. Anything input-proportional in the bound
will have to be argued rather than measured.
