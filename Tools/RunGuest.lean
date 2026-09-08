import Guest.Model

/-!
`lake exe run-guest [input.bin] [fuel]`

Runs the guest under flapjack's step-counted source semantics exactly as
`Guest.runGuestStepped` defines it, on the bytes of `input.bin` (empty input if
omitted), and prints the control result, the step count, and the output region
as the guest left it. `fuel` is the recursion guard (default `2^40`; every loop
iteration and call consumes one unit, so it must exceed the run's total).
-/

open Flapjack Guest

def describe : PanValueControlResult Word → String
  | .normal _ _ _ => "normal"
  | .returned _ _ _ values => s!"returned {values.length} value(s)"
  | .raised _ _ _ exception _ => s!"raised {exception}"
  | .broke _ _ _ => "broke"
  | .continued _ _ _ => "continued"

def memoryOf : PanValueControlResult Word → (Word → Option (PanValue Word))
  | .normal _ _ memory | .returned _ _ memory _ | .raised _ _ memory _ _
  | .broke _ _ memory | .continued _ _ memory => memory

/-- The first `words` aligned cells of the output region, as hex. -/
def outputWords (memory : Word → Option (PanValue Word)) (words : Nat) : List String :=
  (List.range words).map fun index =>
    match memory (outputAddr + BitVec.ofNat 64 (8 * index)) with
    | some (.word value) => s!"{value.toHex}"
    | some _ => "<struct>"
    | none => "<unmapped>"

def main (args : List String) : IO UInt32 := do
  let input : InputBlob ← match args[0]? with
    | some path => do
        let bytes ← IO.FS.readBinFile ⟨path⟩
        pure (bytes.toList.map fun byte => BitVec.ofNat 8 byte.toNat)
    | none => pure []
  let fuel := (args[1]?.bind String.toNat?).getD (2 ^ 40)
  IO.println s!"input: {input.length} bytes, fuel {fuel}"
  let start ← IO.monoMsNow
  match runGuestStepped input fuel with
  | none =>
      IO.println s!"run failed (none) after {(← IO.monoMsNow) - start} ms"
      return 1
  | some (result, steps) =>
      IO.println s!"{describe result} in {steps} Pancake steps ({(← IO.monoMsNow) - start} ms)"
      IO.println s!"output words: {outputWords (memoryOf result) 8}"
      return 0
