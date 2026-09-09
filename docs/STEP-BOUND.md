# Goal 1 (issue #73): a source-level Pancake step bound for the guest

Status of the three `sorry`s of `Guest/StepBound.lean`:

| | state |
|---|---|
| `declaredBlockGasLimit` | **done** — `Guest/InputDecode.lean`, differentially validated against the guest |
| `guestPancakeStepBound` | open |
| `guest_terminates_within_step_bound` | open — was **false as stated**; [the obstruction](#the-obstruction) is fixed, the bound itself is what is left |
| *foundation* | [`Guest/StepCalculus.lean`](#the-step-calculus-gueststepcalculuslean) — fuel monotonicity, without which no two cost lemmas compose |

Two guest bugs were found on the way, both of which made the theorem false as
stated and both now fixed: [`@trap` returning](#the-obstruction), and
[BLAKE2F's SIGMA row index](#a-second-evaluation-failure-path-blake2f-fixed) —
the latter a real halt on ordinary EIP-152 input, not only a modelling artefact.

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

**Fixed** — by [option 1](#the-fix-taken) below, which is in the guest source
and in the committed ASTs. The section is kept because the mechanism explains
why `trap_with` ends in a `throw`, and because the two rejected options are
worth not re-deriving.

As stated before the fix, `guest_terminates_within_step_bound` was false for
every value of `guestPancakeStepBound`. The premises admit inputs on which
`runGuestStepped input fuel = none` for every `fuel`, so `TerminatesWithin`
failed — and it failed on evaluation failure, which the theorem is meant to
rule out.

### Mechanism

1. `@trap` returns in the model. `guestMemoryFfi` (`Guest/Accel.lean`) answers
   `halt` and `trap` with `some memory`, so the run continues. On the machine
   `ffitrap` (`guest/runtime/start.S`) jumps to `cml_exit` and never returns.
   The `Guest/Model.lean` docstring used to call this a safe
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
| 17,408 B | `none` | `raised TrapErr`, 18,169 steps |
| 18,432 B | `none` | `raised TrapErr`, 23,565 steps |
| 19,456 B | returns normally, **137,650** steps | `raised TrapErr`, 28,596 steps |
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

### The fix taken

The guest is not at fault: on the machine, heap exhaustion is a clean
deterministic halt with `trap=1` in the debug bytes. What was wrong is that
`@trap` returns in the model. Making it terminal fixes the whole class at once
— all seven `trap_with` sites (`alloc`, `frame_mem_alloc`, `scratch_alloc`,
division by zero, base-fee overflow, and the two journal-full sites) become
immediate termination, which `TerminatesWithin` accepts, and the
"trap continues down the error paths" caveat in `Guest/Model.lean` goes away.

**Option 1, raise instead of returning**, is what is in the tree. `trap_with`
(`guest/src/lib/mem.pnk`) declares `exception TrapErr : 1;` and ends with
`throw TrapErr code;` in place of its `return 0;`. Nothing catches `TrapErr`,
so it propagates to the top and the run ends as `.raised`, which
`TerminatesWithin` accepts. It needs no flapjack change, and it is dead code on
the machine: `ffitrap` (`guest/runtime/start.S`) jumps to `cml_exit`, so the
`throw` is never reached there.

What was checked:

* **The cpp-expanded diff is exactly those two lines**, for both builds
  (`Guest/guest.pp.pnk`, `Guest/guest-software.pp.pnk`), and the parse
  regenerated from them (`Guest/Ast.lean`, `Guest/SoftwareAst.lean`) differs
  only in the new `Decl.exnDecl "TrapErr"` and in `trap_with`'s tail becoming
  `Prog.raise "TrapErr" (Exp.var VarKind.local "code")`. `lake build` re-checks
  the ASTs against the sources (`Guest/AstParse.lean`).
* **Trapping runs terminate, non-trapping runs are unchanged**, on the heap
  sweep above: every `none` becomes `raised TrapErr`, and all 21 budgets from
  20,480 B keep 137,596 steps to the step. The trap fires from inside `main`'s
  `try … catch SszErr` in the 19,456-byte case and is not swallowed by it.
  Empty input is still 19,778 steps and the minimal well-formed input still
  137,596 (867,017 on the software build), with byte-identical output.
* **`declaredBlockGasLimit` still agrees with the guest** — `lake exe
  input-decode-check` on the 431 `tools/ssz-inputs.py --fuzz` inputs, 0
  mismatches.
* **`cake` still compiles both builds.** `cake --pancake --target=riscv`
  (CakeML v3479) accepts `Guest/guest.pp.pnk` and
  `Guest/guest-software.pp.pnk`; this mattered because `main` catches only
  `SszErr`, so `TrapErr` leaves it uncaught. Not checked end to end: the ELF
  link and a `ziskemu`/`spike` run, which need a `riscv64-unknown-elf`
  toolchain. Since `TrapErr` is inserted ahead of every other exception
  declaration the compiler's exception tags all shift by one; nothing outside
  the compiled program reads a tag (the debug byte at `OUTPUT_ADDR + 70` is an
  exception *payload*), but a machine run is the check that would confirm it.

Regenerating the ASTs is `tools/gen-guest-ast.sh`. It now runs on macOS as
well: it picks `clang -E` there, spells `sed -i` portably, and drops blank
lines so that GNU `cpp` and `clang -E` produce byte-identical `.pp.pnk` (they
were verified to, on this change).

The two options not taken:

2. **Let the memory handler signal a final event** (flapjack). A
   `PanValueMemoryFfiHandler` returns `Option (locals × memory × ffi)`, and the
   `.extCall` case of `evalPanValueFfiProgSteps` consults it unconditionally
   and always continues as `.normal`, so with a memory handler installed there
   is no path to `.finalFfi` at all. Widening its result — or falling through
   to the oracle when it declines — is the architecturally right fix, but it is
   a change in a pinned dependency. Worth doing upstream regardless: option 1
   makes the *guest* terminate on trap, it does not make `@trap` terminal for
   any other program the model is pointed at.
3. **Sharpen the premise.** Not sufficient on its own: a heap-fit hypothesis on
   `input.length` would not cover exhaustion reached from inside the run
   (`frame_mem_alloc`, `scratch_alloc`, `htab_grow`), and it would give up on
   inputs that the machine handles correctly.

Option 1 also *helps* the bound: every resource-exhaustion path becomes
immediate termination rather than a continuation that has to be bounded.

## The step calculus (`Guest/StepCalculus.lean`)

`TerminatesWithin` asks for *some* fuel at which the run returns. Proving that
compositionally — a cost lemma per function, combined along the call graph —
means combining sub-proofs carried at different fuels, and that needs **fuel
monotonicity**: a successful run is unchanged, same control result *and* same
step count, at any larger fuel.

Flapjack does not have it. `Flapjack/PanSteppedSemantics.lean` proves the
`_fst`/`_snd` projections relating the stepped evaluator to the unstepped one,
and nothing about varying the fuel; `Flapjack/PanValueFfiSemantics.lean` has one
theorem, `evalPanValueFfiProgramStepped_fst`. So the issue's remark that "the
stepped semantics is compositional (steps add up), so per-function cost lemmas
compose" is true of the *definition* — `.seq` returns
`firstSteps + secondSteps + 1` — but there was no theorem to compose with.

`Guest/StepCalculus.lean` supplies it, `sorry`-free:

* `progMono`, `callMono` — for the mutually recursive
  `evalPanValueFfiProgSteps` / `evalPanValueFfiCallSteps`, by the
  functional-induction principle `evalPanValueFfiProgSteps.induct` (25 cases;
  18 are the constructors whose body does not mention fuel and close by
  unfolding both sides, 7 recurse: the call evaluator's successor case, `dec`,
  `seq`, `ite`, `call`, `decCall`, `while`).
* `evalPanValueFfiProgramStepped_fuel_mono` — the public entry point, which is
  what `Guest.runGuestStepped` is.
* In `Guest/StepBound.lean`: `runGuestStepped_fuel_mono` and
  `TerminatesWithin.mono` (bound weakening, so a parametric bound can be
  specialised to the constant).

Worth knowing when reading the evaluator: **fuel is a depth budget, not a work
budget.** `.seq first second` at `fuel + 1` evaluates *both* halves at `fuel`,
and `.while`'s next iteration also recurses at `fuel`, so fuel bounds syntactic
nesting and call depth as well as iteration count. Monotonicity is what makes
that workable — a bound proved for a sub-program stays true in a larger context.

This belongs upstream in flapjack. It lives here so the pinned revision does not
have to move, in namespace `Guest.StepCalculus` rather than `Flapjack.*` so a
re-pin cannot collide with it.

## A second evaluation-failure path: BLAKE2F (fixed)

Fixing `@trap` (#76) removed one way for the model to be `none` where the
machine halts. Auditing the *other* handler that can decline — the accelerator
— turned up a second, and it is a real guest bug rather than a modelling
artefact.

`guestMemoryFfi` (`Guest/Accel.lean`) answers an accelerator call with `none`
"for an unknown name or an input the machine model would trap on", and the
`.extCall` case of `evalPanValueFfiProgSteps` propagates that as `none` for the
whole run — evaluation failure at every fuel, exactly the class the trap fix
removed.

The reachable case is `@blake2bround`. ZisK's CSR 0x819 takes a **SIGMA row**,
not a round number: `csrsValid` requires `sigmaIdx < 10`
(`RiscvZkvm/Rv64/ZiskAccel.lean`) and the machine traps when it fails. The
guest's accelerated loop passed the raw round counter:

```
var r = 0;
while r <+ rounds {
  st b2_round, r;              /* r, not r % 10 */
  @blake2bround(b2_round, 0, 0, 0);
  r = r + 1;
}
```

while the software path immediately below it maintains a `row` that wraps at
10. `rounds` is user input — `pre_blake2f` reads it as `LD_BE32(data)` and
charges 1 gas per round — and **BLAKE2b's standard compression is 12 rounds**,
so an ordinary EIP-152 call reaches row 10 and traps.

Measured on the guest's own `blake2b_f`, driven at each round count (all-zero
state and message):

| rounds | accelerated, before | software | after the fix |
|---|---|---|---|
| 1, 9, 10 | digests agree with software | — | unchanged |
| 11, 12, 13, 21 | **`none`, every fuel** | correct digest | digests agree |

All seven digests match an independent Python BLAKE2b-F reference, so the
software build was always right and the accelerated one is now right too.

The fix mirrors the software path: keep a `row` counter that wraps at 10. It
touches only the `ZISK_ACCEL` branch, so `Guest/guest-software.pp.pnk` is
unchanged.

Consequences worth separating:

* **For the guest.** The accelerated build halted on any block containing a
  BLAKE2F call with `rounds >= 11`, which is the normal use of the precompile.
  That is a bug in the deployed build, independent of any proof.
* **For the theorem.** It was a second way for
  `guest_terminates_within_step_bound` to be false as stated, on inputs well
  inside the premises: 12 rounds costs 12 gas against a 200M limit, and the
  block is small.

### The rest of the accelerator surface

The other conditions under which `acceleratorEffect` declines were checked
against every call site in `guest/src`, and all are guarded by the guest:

| accelerator | declines when | guard |
|---|---|---|
| `secpadd`, `bn_g1_add`, `bls_g1_add` | `x1 == x2`, or a coordinate not reduced | `ec_add`/`ecp_add`/`g1_add` test `x1 == x2` first and route to doubling or to infinity |
| `secpdbl`, `bn_g1_dbl`, `bls_g1_dbl` | `y == 0`, or not reduced | `ec_double`/`ecp_double`/`g1_double` test `y == 0` and return infinity |
| `arith256mod`, `bn_arith256`, `bls_arith384` | modulus zero | the modulus is a constant written at init (`SECP_P`, `SECP_N`, the BN254/BLS field primes), never user data |
| `bn_fp2_*`, `bls_fp2_*` | an operand not reduced | operands are Montgomery-form field elements, reduced by construction |

So BLAKE2F was the only unguarded one.

## Structural termination rules (`Guest/Termination.lean`)

With monotonicity in hand, the next layer is a termination calculus, so a
whole-program proof can be assembled from per-construct facts. All `sorry`-free:

* **`while_terminates_inv`** — a loop terminates when an invariant `I` holds on
  entry and is preserved, the condition evaluates on every state satisfying
  `I`, and the body — whenever entered — terminates and strictly decreases a
  measure `μ`. Proved by strong induction on `μ`, taking `max` of the body's
  fuel and the tail's and lifting both with `progMono` — precisely the step
  that was impossible before. `while_terminates` is this with `I := True`.
* `seq_terminates`, `ite_terminates`, `dec_terminates`, `call_terminates` — the
  compositional rules for a function body.
* `callSteps_terminates` — the call evaluator itself. Its extra hypotheses are
  the evaluator's own `none` branches: the return- and exception-validity
  checks, the destination assignment, and a matching handler's termination.

The leaf constructors need no rule: `Terminates` for them is discharged at the
point of use by exhibiting the one-step run, and their only content is whether
their expressions evaluate.

* `while_terminates_of_increasing_counter` — the shape ~200 of the 257 loops
  actually have (`i <+ n`, `i < cap`, `i < 8`, ...): a counter the body strictly
  increases, against a bound. It does the truncated-subtraction argument once
  rather than per loop, and does not require the counter to stay under the
  bound, since overshooting sends the measure to zero, which is still a
  decrease.

Since the call graph is acyclic (#71), **what is left is invariants and
measures**: every remaining loop reduces to exhibiting a pair, and for most of
them that is a counter and a bound.

### Two things learned by pointing the rules at real guest code

Both came out of trying to prove an actual function rather than designing the
rules in the abstract, and both change how the remaining work has to be
organised.

**The invariant is not decoration.** A loop condition mentioning a local can
only be shown to evaluate on states where that local is bound, so an
invariant-free rule is unusable on anything real. `rlp_be_len` — four lines,
one loop — already needs one.

**Counters wrap, so per-loop lemmas are not independent.** The guest's counters
are `BitVec 64` and Pancake's `+` wraps, so "the body increases the counter" is
a real obligation:

| loop | diverges when | why |
|---|---|---|
| `memzero`'s `while i + 32 <=+ n` | `n ≥ 2^64 − 32` | `i + 32` wraps to `0`, the condition still holds, the counter restarts |
| `ceil_log2`'s `while (1 << d) <+ n` | `n > 2^63` | at `d = 64` the shift gives `0`, which is `<+ n` forever |

Neither is reachable — `memzero`'s call sites pass small constants, and
`ceil_log2` is only called from `merkleize` with SSZ chunk counts bounded by
the list limits — but **both are preconditions that only the caller can
discharge**. So the loops cannot be proved in isolation and then assembled;
each needs its bound threaded down from its callers. That is a structural
constraint on the remaining work, not a detail.

The counter corollary takes `counter` as a `ℕ` precisely so that this obligation
cannot be skipped.

## First guest function proved to terminate (`Guest/FunctionTermination.lean`)

`charge_gas_terminates`, `sorry`-free, composed from `dec_terminates`,
`ite_terminates` and `seq_terminates` against the AST as committed
(`chargeGasBody` is `Guest.guestFn_charge_gas`'s body, checked by `rfl`).

`charge_gas` was chosen because it has no loop, so it tests the calculus on
`dec`/`ite`/`seq`/leaves without needing a measure. Two things it showed:

* the leaf rules really are one-liners at the use site — `skip` closes by
  `rw [evalPanValueFfiProgSteps]` alone — so not writing lemmas for them was
  the right call;
* **`raise` is not free.** `Prog.raise` evaluates its payload and then requires
  `panValueExceptionValid` and `panValuePayloadWithinLimit` against the
  program's contracts, returning `none` otherwise. So every `throw` in the
  guest carries an obligation that the exception is declared with a matching
  shape — true here (`exception EvmErr : 1`), but it must be supplied, at every
  raise site.

Its remaining hypotheses are deliberate, and they name the next piece of
missing infrastructure: `Exp.load` and `Prog.store` bottom out in
`panValueFlatLoad` and `panValueStoreWithAccess`, about which flapjack proves
nothing, so the gas load, the comparison and the tail are assumed rather than
derived from the state. **A memory layer is the next dependency** — without it
no function that touches memory can have its obligations discharged, and almost
all of them do.

## What the bound itself needs

The guest's call graph is acyclic (#71), so no recursion-depth argument is
needed; what is left is an iteration bound for each loop. The cpp-expanded
accelerated guest has **257 `while` loops**. By loop condition:

* ~200 are counters against a length or a constant (`i <+ n`, `i < cap`,
  `i < 8`, ...). Their bound is the length or the constant.
* The substantive ones are the de-recursified drivers, where termination is the
  real content:
  * `run_frames` (`evm_calls.pnk:681`) — one iteration per opcode executed
    across all frames, plus one per frame completion.

    **The obvious gas argument does not work as stated.** "Every opcode costs
    at least 1 gas" is false: `op_stop` (`evm.pnk:870`) charges nothing at all,
    it only clears `EV_RUNNING` and advances the pc, and the other frame-ending
    opcodes are in the same position. The repair is that a zero-gas opcode
    *ends its frame*, so it runs at most once per frame — but that turns the
    bound into a case analysis over the whole of `op_dispatch`, showing every
    opcode either charges ≥ 1 gas or clears `EV_RUNNING`. With that, iterations
    ≤ 200M + 2·frames, frames ≤ 1024 deep and ≤ gas/700.

    `lake exe opcode-census` reads that classification off the committed AST.
    It walks `op_dispatch` for every `op_*` handler it can reach — equality
    tests and the range tests that pass an argument (`if op <+ 128 {
    op_push(op - 95); ... }`) alike — and then runs two passes:

    1. the handler's straight-line prefix, following `seq`, `dec` and `decCall`;
    2. a **path-sensitive, interprocedural must-charge analysis** on whatever
       the first pass left open. `mustCharge` holds when every path leaving a
       program has either charged ≥ 1 gas or ended the frame (cleared
       `EV_RUNNING`, or raised — `run_frames` catches `EvmErr` into
       `frame_exception`). It is conservative by construction: a charge inside
       a `while` does not count, since the loop may run zero times, and a
       `return` that has not charged makes the whole program fail. Callee
       facts come from a fixpoint over the acyclic call graph, tracking both
       "charges unconditionally" and "charges if its first argument is ≥ 1" —
       the latter because the charging helpers take the base cost as a
       parameter (`charge_with_memory(3, start, <32,0,0,0>)`), and positivity
       propagates through `add_sat`, which is monotone, but *not* through
       plain `+`, which wraps.

    | | handlers |
    |---|---|
    | charge a literal ≥ 1 gas up front | 60 |
    | end the frame without charging | 3 — `op_stop`, `op_return`, `op_selfdestruct` |
    | charge or end the frame on every path | 7 — `op_mload`, `op_mstore`, `op_mstore8`, `op_sload`, `op_sstore`, `op_push`, `op_revert` |
    | still need a human | 17 |

    **87 handlers, and the only ones that charge nothing up front are frame
    enders** — which is the repaired bound's shape, confirmed rather than
    assumed. `op_dispatch` also falls through to `throw EvmErr 5` for an
    unmatched opcode, which ends the frame too.

    The 17 left are `op_exp`, `op_keccak`, `op_balance`, the four `*copy`
    opcodes, `op_extcodesize`/`op_extcodehash`/`op_extcodecopy`, `op_mcopy`,
    `op_log`, and the six call/create opcodes. They are open for a reason worth
    stating, because it is the same reason as the loop preconditions above:
    their cost is computed rather than constant, so proving it is ≥ 1 needs a
    no-wraparound side condition. `op_keccak`'s
    `cost = add_sat(30 + 6 * w, x.0)` is ≥ 30 only because `6 * w` cannot wrap,
    which holds since `w = words_of(sat_word(size)) ≤ 2^59` — true, but an
    obligation, not an inspection. The call and create opcodes are open for a
    second reason: part of their cost is paid by the child frame.

    The census is syntactic and conservative — a work-list, not a proof.
    Turning "charges ≥ 1" into a semantic fact still needs a lemma about
    `charge_gas`.

    One wrinkle that lemma will have to handle: gas lives in **two** counters.
    `charge_gas` decrements `EV_GAS_LEFT`, but `charge_state_gas`
    (`evm.pnk:249`) draws from `EV_STATE_GAS_LEFT` first and only spills into
    `EV_GAS_LEFT` when that is exhausted, so the measure has to be the sum.
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
