import Guest.Model
import Guest.InputDecode

/-!
`lake exe input-decode-check input.bin ...`

Differential check of `Guest.declaredBlockGasLimit` against the guest itself.
It calls `Guest.InputDecode.declaredGasLimit`, which is that definition's body;
importing `Guest.StepBound` here would force its remaining `sorry` at module
initialisation.

`guest/src/main.pnk` returns `1` from its `catch SszErr` block and `0` once
`decode_stateless_input` has returned, so the value a run returns is an exact
oracle for "this input decodes". The check runs the guest on each input under
the same stepped semantics `Guest.StepBound` reasons about and reports any
input where the oracle and `declaredBlockGasLimit` disagree.

Inputs are in the ziskemu packing that `tools/make-inputs.sh` and
`tools/ssz-inputs.py` write. Generate a corpus that actually decodes with

    tools/ssz-inputs.py work/ssz-inputs --fuzz
    lake exe input-decode-check work/ssz-inputs/*.bin

The model is quadratic in the input length and in the number of stores, so keep
the inputs small; a 658-byte one takes under a second.
-/

open Flapjack Guest

/-- Inverse of the converter's `pack_ziskemu_input`: `[8B LE len][blob][pad]`. -/
def unpackInput (bytes : ByteArray) : Except String InputBlob := do
  if bytes.size < 8 then throw s!"packed input too short: {bytes.size} bytes"
  let length := (List.range 8).foldr (fun index acc => acc * 256 + bytes[index]!.toNat) 0
  if bytes.size < 8 + length then
    throw s!"packed input truncated: length {length}, {bytes.size} bytes"
  pure ((bytes.extract 8 (8 + length)).toList.map fun byte => BitVec.ofNat 8 byte.toNat)

/-- The guest's own verdict on whether the input decodes. -/
inductive Verdict
  /-- `decode_stateless_input` returned; `main` returned 0. -/
  | decoded (steps : Nat)
  /-- `SszErr` was raised and caught; `main` returned 1. -/
  | sszErr (steps : Nat)
  /-- Anything else: no result for the given fuel, or an unexpected outcome. -/
  | inconclusive (reason : String)
  deriving DecidableEq

def Verdict.render : Verdict → String
  | .decoded steps => s!"decoded ({steps} steps)"
  | .sszErr steps => s!"SszErr ({steps} steps)"
  | .inconclusive reason => reason

def guestVerdict (input : InputBlob) (fuel : Nat) : Verdict :=
  match runGuestStepped input fuel with
  | none => .inconclusive s!"no result at fuel {fuel}"
  | some (.returned _ _ _ _ [.word value], steps) =>
      if value == 0 then .decoded steps
      else if value == 1 then .sszErr steps
      else .inconclusive s!"main returned {value}"
  | some (result, _) => .inconclusive <| match result with
      | .normal .. => "fell off the end of main"
      | .returned _ _ _ _ values => s!"main returned {values.length} values"
      | .raised _ _ _ _ exception _ => s!"uncaught {exception}"
      | .broke .. => "broke"
      | .continued .. => "continued"
      | .finalFfi _ _ _ _ event => s!"FFI terminated ({repr event.name})"

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  let verbose := args.contains "--verbose"
  let paths := args.filter fun arg => !arg.startsWith "--"
  let mut decoded := 0
  let mut rejected := 0
  let mut mismatched : List String := []
  let mut inconclusive : List String := []
  for path in paths do
    let input ← match unpackInput (← IO.FS.readBinFile ⟨path⟩) with
      | .ok blob => pure blob
      | .error message => do IO.eprintln s!"{path}: {message}"; return 2
    let name := (System.FilePath.mk path).fileName.getD path
    let declared := InputDecode.declaredGasLimit input
    let verdict := guestVerdict input (2 ^ 32)
    let agrees := match declared, verdict with
      | some _, .decoded _ => true
      | none, .sszErr _ => true
      | _, _ => false
    match verdict with
    | .decoded _ => decoded := decoded + 1
    | .sszErr _ => rejected := rejected + 1
    | .inconclusive _ => inconclusive := name :: inconclusive
    if !agrees then
      match verdict with
      | .inconclusive _ => pure ()
      | _ => do
          mismatched := name :: mismatched
          stdout.putStrLn s!"MISMATCH {name}: declaredGasLimit = {declared}, \
            guest {verdict.render}"
    else if verbose then
      stdout.putStrLn s!"ok {name}: declaredGasLimit = {declared}, guest {verdict.render}"
    stdout.flush
  stdout.putStrLn s!"{paths.length} inputs: {decoded} decoded, {rejected} rejected, \
    {mismatched.length} mismatched, {inconclusive.length} inconclusive"
  for name in inconclusive.reverse do
    stdout.putStrLn s!"  inconclusive: {name}"
  return if mismatched.isEmpty && inconclusive.isEmpty then 0 else 1
