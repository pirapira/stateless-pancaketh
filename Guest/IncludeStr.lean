import Lean

/-!
`include_str% "relative/path"` elaborates to the contents of a file, read at
elaboration time relative to the directory of the current Lean source file.
Used to bring the preprocessed guest source into Lean without hand-copying a
half-megabyte string literal.
-/

namespace Guest

open Lean Elab Term

syntax (name := includeStr) "include_str% " str : term

@[term_elab includeStr]
def elabIncludeStr : TermElab := fun stx _ => do
  match stx with
  | `(include_str% $path:str) =>
      let current := System.FilePath.mk (← getFileName)
      let directory := current.parent.getD "."
      let file := directory / path.getString
      let contents ← IO.FS.readFile file
      return mkStrLit contents
  | _ => throwUnsupportedSyntax

end Guest
