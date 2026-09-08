import Guest.Model

/-!
`lake exe run-guest [input] [fuel]`

Runs the guest under flapjack's step-counted source semantics exactly as
`Guest.runGuestStepped` defines it, and prints the control result, the step
count, and the output region as the guest left it.

`input` is a guest input as `tools/make-inputs.sh` writes it (the ziskemu
packing: 8-byte little-endian blob length, the blob, zero padding to a multiple
of 8); the blob is what lands at `INPUT_DATA_ADDR`. With no `input` the blob is
empty. `fuel` is the recursion guard (default `2^40`; every loop iteration and
call consumes one unit, so it must exceed the run's total).
-/

open Flapjack Guest

/-- Inverse of the converter's `pack_ziskemu_input`: `[8B LE len][blob][pad]`. -/
def unpackInput (bytes : ByteArray) : Except String InputBlob := do
  if bytes.size < 8 then throw s!"packed input too short: {bytes.size} bytes"
  let length := (List.range 8).foldr (fun i acc => acc * 256 + bytes[i]!.toNat) 0
  if bytes.size < 8 + length then
    throw s!"packed input truncated: length {length}, {bytes.size} bytes"
  pure ((bytes.extract 8 (8 + length)).toList.map fun byte => BitVec.ofNat 8 byte.toNat)

def describe : PanValueControlResult Word → String
  | .normal _ _ _ => "normal"
  | .returned _ _ _ values => s!"returned {values.length} value(s)"
  | .raised _ _ _ exception _ => s!"raised {exception}"
  | .broke _ _ _ => "broke"
  | .continued _ _ _ => "continued"

def memoryOf : PanValueControlResult Word → (Word → Option (PanValue Word))
  | .normal _ _ memory | .returned _ _ memory _ | .raised _ _ memory _ _
  | .broke _ _ memory | .continued _ _ memory => memory

/-- The first `count` bytes of the output region as hex, read little-endian
out of the aligned word cells (the byte layout `guestMemoryAccess` uses). -/
def outputHex (memory : Word → Option (PanValue Word)) (count : Nat) : String :=
  String.join <| (List.range count).map fun index =>
    match memory (outputAddr + BitVec.ofNat 64 (8 * (index / 8))) with
    | some (.word value) =>
        let byte := (value.toNat / 256 ^ (index % 8)) % 256
        let digits := String.ofList (Nat.toDigits 16 byte)
        if digits.length < 2 then "0" ++ digits else digits
    | _ => "??"

def main (args : List String) : IO UInt32 := do
  let input : InputBlob ← match args[0]? with
    | some path => do
        match unpackInput (← IO.FS.readBinFile ⟨path⟩) with
        | .ok blob => pure blob
        | .error message => do
            IO.eprintln message
            return 2
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
      IO.println s!"output[0..80): {outputHex (memoryOf result) 80}"
      return 0
