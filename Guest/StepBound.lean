import Flapjack.PanSteppedSemantics
import Flapjack.RiscV.Model

/-!
# Goal 1: the guest terminates within a constant number of Pancake steps

The stateless guest (`guest/src/main.pnk`, cpp-expanded by `guest/build.sh`)
must terminate, and do so within a fixed number of source-level Pancake steps,
whenever the block it is asked to validate declares a gas limit of at most
`maxBlockGasLimit` (200M). The step count is the one produced by flapjack's
step-counted source semantics `Flapjack.evalPanValueSteppedProgram`.

Together with the step-preserving compilation theorem tracked in
<https://github.com/pirapira/flapjack/issues/352> (a fixed linear relation
between source steps and generated RISC-V instruction steps) this yields a
RISC-V step bound for the compiled guest.

Everything below is stated, not proved. The `sorry`s fall in two groups:

* *Modelling gaps*: the guest program as a flapjack `Decl` list, the initial
  program state under the `guest/src/config.h` memory contract, the primitive
  and FFI handlers, and the "declared block gas limit" projection of the
  SSZ-encoded input. These need either a Pancake parser on the flapjack side
  or a hand-written translation, and are expected to be filled in by
  definitions rather than proofs.
* *The theorem and its constant*: `guestPancakeStepBound` and
  `guest_terminates_within_step_bound`.
-/

namespace Guest

open Flapjack

/-- Word type of the guest: 64-bit RISC-V words (`riscv64` target of `cake`). -/
abbrev Word := RiscV.Word 64

/-- Input bytes as supplied by the host at `INPUT_DATA_ADDR`. -/
abbrev InputBlob := List (BitVec 8)

/-- The stateless guest as flapjack Pancake declarations: the cpp-expanded
translation unit rooted at `guest/src/main.pnk`. -/
def guestDeclarations : List (Decl Word) := sorry

/-- Entry point of the guest (`fun 1 main()` in `guest/src/main.pnk`). -/
def guestEntry : FunName := "main"

/-- Initial program state for a run on `input`, following the memory contract
in `guest/src/config.h`: `INPUT_ADDR` holds `[8B zero meta][8B LE len][blob]`,
`@base` is `HEAP_BASE`, and the heap ends at `HEAP_END`. -/
def guestInitialState (input : InputBlob) : PanValueProgramState Word := sorry

/-- Semantics of Pancake primitive operations (`addCarry`) on 64-bit words. -/
def guestPrimitiveHandler : PanPrimitiveHandler Word := sorry

/-- Host side of the guest's foreign calls (`@halt` and the ZisK accelerator
stubs in `guest/runtime/start.S`). -/
def guestFfiHandler : PanValueFfiHandler Word := sorry

/-- Step-counted run of the guest on `input` with recursion guard `fuel`. -/
def runGuestStepped (input : InputBlob) (fuel : Nat) :
    Option (PanValueSteppedResult Word) :=
  evalPanValueSteppedProgram (guestInitialState input) guestPrimitiveHandler
    guestFfiHandler fuel guestDeclarations guestEntry []

/-- The block gas limit declared by the input: the `gas_limit` field of the
block header inside the SSZ-encoded stateless input (what `fork.pnk` reads
back as `BE_GAS_LIMIT`). `none` when the input does not decode. -/
def declaredBlockGasLimit (input : InputBlob) : Option Nat := sorry

/-- Largest declared block gas limit covered by the bound. -/
def maxBlockGasLimit : Nat := 200000000

/-- The constant: an upper bound on the number of Pancake source steps taken by
the guest on any input whose declared block gas limit is at most
`maxBlockGasLimit`. To be fixed by the proof. -/
def guestPancakeStepBound : Nat := sorry

/-- Termination of the stepped guest run within `bound` steps. -/
def TerminatesWithin (input : InputBlob) (bound : Nat) : Prop :=
  ∃ fuel result steps,
    runGuestStepped input fuel = some (result, steps) ∧ steps ≤ bound

theorem terminatesWithin_panSteppedTerminates {input : InputBlob} {bound : Nat}
    (h : TerminatesWithin input bound) :
    PanSteppedTerminates (runGuestStepped input) := by
  obtain ⟨fuel, result, steps, hrun, _⟩ := h
  exact ⟨fuel, result, steps, hrun⟩

/-- **Goal 1.** If the input declares a block gas limit of at most
`maxBlockGasLimit`, the guest terminates within `guestPancakeStepBound`
Pancake steps. -/
theorem guest_terminates_within_step_bound (input : InputBlob) (gasLimit : Nat)
    (hdeclared : declaredBlockGasLimit input = some gasLimit)
    (hle : gasLimit ≤ maxBlockGasLimit) :
    TerminatesWithin input guestPancakeStepBound := sorry

end Guest
