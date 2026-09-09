import Flapjack.PanValues
import Flapjack.RiscV.Model

/-!
Shared types for properties about `guest/src/*.pnk` (see `README.md`'s
Pancake-source-to-SpecRef-module table), stated against flapjack's Pancake
front end and its step-counted source semantics.
-/

namespace Guest

/-- Word type of the guest: 64-bit RISC-V words (`riscv64` target of `cake`). -/
abbrev Word := Flapjack.RiscV.Word 64

/-- Input bytes as supplied by the host at `INPUT_DATA_ADDR`. -/
abbrev InputBlob := List (BitVec 8)

/-- Flapjack's structured source memory over guest words. -/
abbrev Memory := Word → Option (Flapjack.PanValue Word)

end Guest
