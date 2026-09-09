import Guest.Source
import Guest.Ast
import Guest.SoftwareAst
import Guest.DecidableEq
import Guest.StepBound

/-!
The committed ASTs `Guest.guestAst` and `Guest.Software.guestAst` are what
flapjack's parser produces from `Guest/guest.pp.pnk` and
`Guest/guest-software.pp.pnk`. This is the one place the parser runs at build
time; it goes through `native_decide`, so the result rests on
`Lean.ofReduceBool` in addition to the kernel.
-/

namespace Guest

open Flapjack

theorem guestParse_eq_ast : guestParse = .ok guestAst := by
  native_decide

theorem guestDeclarations_eq_ast : guestDeclarations = guestAst := by
  unfold guestDeclarations
  rw [guestParse_eq_ast]
  rfl

theorem Software.guestParse_eq_ast : Software.guestParse = .ok Software.guestAst := by
  native_decide

theorem Software.guestDeclarations_eq_ast : Software.guestDeclarations = Software.guestAst := by
  unfold Software.guestDeclarations
  rw [Software.guestParse_eq_ast]
  rfl

/-- Step-counted run of the software guest as parsed from source, rather than
from the committed AST. -/
def runGuestSoftwareSteppedParsed (input : InputBlob) (fuel : Nat) :
    Option (PanValueSteppedResult Word) :=
  evalPanValueSteppedProgram (guestInitialState input) guestPrimitiveHandler
    guestFfiHandler fuel Software.guestDeclarations guestEntry []
    (memoryAccess := some guestMemoryAccess)

/-- Running the parsed guest is running the committed AST, so results about
`runGuestSoftwareStepped` transfer to the source as written. -/
theorem runGuestSoftwareSteppedParsed_eq :
    runGuestSoftwareSteppedParsed = runGuestSoftwareStepped := by
  funext input fuel
  unfold runGuestSoftwareSteppedParsed runGuestSoftwareStepped
  rw [Software.guestDeclarations_eq_ast]

end Guest
