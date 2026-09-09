import Flapjack.Parser

/-!
`lake exe gen-guest-ast <guest.pp.pnk> [namespace] > <Ast.lean>`

Parses a cpp-expanded guest with flapjack's Pancake parser and prints the
resulting declarations as Lean source in the given namespace (default
`Guest`): one definition per top-level declaration and `guestAst`, the list of
them all. `Guest.AstParse` then proves that parsing the committed source gives
exactly `guestAst`, so everything else can be stated about the committed AST
without re-parsing. `tools/gen-guest-ast.sh` runs it for both guest builds.
-/

open Flapjack

namespace GenGuestAst

def q (s : String) : String := s.quote

def list (f : α → String) (xs : List α) : String :=
  "[" ++ ", ".intercalate (xs.map f) ++ "]"

partial def shape : Shape → String
  | .one => "Shape.one"
  | .comb fields => s!"(Shape.comb {list shape fields})"
  | .named name => s!"(Shape.named {q name})"

def shapeField (field : String × Shape) : String := s!"({q field.1}, {shape field.2})"

def varKind : VarKind → String
  | .local => "VarKind.local"
  | .global => "VarKind.global"

def binOp : BinOp → String
  | .add => "BinOp.add"
  | .sub => "BinOp.sub"
  | .and => "BinOp.and"
  | .or => "BinOp.or"
  | .xor => "BinOp.xor"

def panOp : PanOp → String
  | .mul => "PanOp.mul"

def cmp : Cmp → String
  | .equal => "Cmp.equal"
  | .lower => "Cmp.lower"
  | .less => "Cmp.less"
  | .test => "Cmp.test"
  | .notEqual => "Cmp.notEqual"
  | .notLower => "Cmp.notLower"
  | .notLess => "Cmp.notLess"
  | .notTest => "Cmp.notTest"

def shift : Shift → String
  | .lsl => "Shift.lsl"
  | .lsr => "Shift.lsr"
  | .asr => "Shift.asr"
  | .ror => "Shift.ror"

def opSize : OpSize → String
  | .op8 => "OpSize.op8"
  | .opW => "OpSize.opW"
  | .op32 => "OpSize.op32"
  | .op16 => "OpSize.op16"

def primOp : PrimOp → String
  | .addCarry => "PrimOp.addCarry"

def word (w : BitVec 64) : String := s!"(BitVec.ofNat 64 {w.toNat})"

partial def exp : Exp (BitVec 64) → String
  | .const value => s!"(Exp.const {word value})"
  | .var kind name => s!"(Exp.var {varKind kind} {q name})"
  | .rStruct fields => s!"(Exp.rStruct {list exp fields})"
  | .rField index value => s!"(Exp.rField {index} {exp value})"
  | .nStruct name fields => s!"(Exp.nStruct {q name} {list expField fields})"
  | .nField name value => s!"(Exp.nField {q name} {exp value})"
  | .load sh address => s!"(Exp.load {shape sh} {exp address})"
  | .load32 address => s!"(Exp.load32 {exp address})"
  | .loadByte address => s!"(Exp.loadByte {exp address})"
  | .op operator args => s!"(Exp.op {binOp operator} {list exp args})"
  | .panOp operator args => s!"(Exp.panOp {panOp operator} {list exp args})"
  | .cmp operator left right => s!"(Exp.cmp {cmp operator} {exp left} {exp right})"
  | .shift operator left right => s!"(Exp.shift {shift operator} {exp left} {exp right})"
  | .baseAddr => "Exp.baseAddr"
  | .topAddr => "Exp.topAddr"
  | .bytesInWord => "Exp.bytesInWord"
where
  expField (field : String × Exp (BitVec 64)) : String := s!"({q field.1}, {exp field.2})"

def pad (indent : Nat) : String := "".pushn ' ' indent

/-- A statement as Lean text. The first line carries no indentation (the caller
places it); continuation lines are indented relative to `indent`. A
right-nested `seq` chain is printed flat, one statement per line. -/
partial def prog (indent : Nat) : Prog (BitVec 64) → String
  | .skip => "Prog.skip"
  | .dec name sh value body =>
      s!"(Prog.dec {q name} {shape sh} {exp value}\n{sub indent body})"
  | .assign kind name value => s!"(Prog.assign {varKind kind} {q name} {exp value})"
  | .primitive name operator args =>
      s!"(Prog.primitive {q name} {primOp operator} {list exp args})"
  | .store address value => s!"(Prog.store {exp address} {exp value})"
  | .store32 address value => s!"(Prog.store32 {exp address} {exp value})"
  | .storeByte address value => s!"(Prog.storeByte {exp address} {exp value})"
  | .seq first second =>
      let (rest, tail) := chain second
      let statements := first :: rest
      let opened := statements.map fun statement =>
        s!"(Prog.seq\n{sub indent statement}\n{pad (indent + 2)}"
      String.join opened ++ prog (indent + 2) tail ++ "".pushn ')' statements.length
  | .ite condition thenBranch elseBranch =>
      s!"(Prog.ite {exp condition}\n{sub indent thenBranch}\n{sub indent elseBranch})"
  | .while condition body =>
      s!"(Prog.while {exp condition}\n{sub indent body})"
  | .break => "Prog.break"
  | .continue => "Prog.continue"
  | .call info name args =>
      s!"(Prog.call {callInfo indent info} {q name} {list exp args})"
  | .decCall name sh function args body =>
      s!"(Prog.decCall {q name} {shape sh} {q function} {list exp args}\n{sub indent body})"
  | .extCall function configuration configurationLength array arrayLength =>
      s!"(Prog.extCall {q function} {exp configuration} {exp configurationLength} {exp array} {exp arrayLength})"
  | .raise exception value => s!"(Prog.raise {q exception} {exp value})"
  | .return value => s!"(Prog.return {exp value})"
  | .shMemLoad size kind name address =>
      s!"(Prog.shMemLoad {opSize size} {varKind kind} {q name} {exp address})"
  | .shMemStore size address value =>
      s!"(Prog.shMemStore {opSize size} {exp address} {exp value})"
  | .tick => "Prog.tick"
  | .annot tag text => s!"(Prog.annot {q tag} {q text})"
where
  /-- A nested statement on its own line, indented one level deeper. -/
  sub (indent : Nat) (statement : Prog (BitVec 64)) : String :=
    pad (indent + 2) ++ prog (indent + 2) statement
  /-- Split a right-nested `seq` chain into its statements and final tail. -/
  chain : Prog (BitVec 64) → List (Prog (BitVec 64)) × Prog (BitVec 64)
    | .seq first second =>
        let (rest, tail) := chain second
        (first :: rest, tail)
    | other => ([], other)
  callInfo (indent : Nat) :
      Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog (BitVec 64))) →
        String
    | none => "none"
    | some (ret, handler) =>
        let retString := match ret with
          | none => "none"
          | some (kind, name) => s!"(some ({varKind kind}, {q name}))"
        let handlerString := match handler with
          | none => "none"
          | some (exception, name, body) =>
              s!"(some ({q exception}, {q name},\n{pad (indent + 4)}{prog (indent + 4) body}))"
        s!"(some ({retString}, {handlerString}))"

def declName : Decl (BitVec 64) → String
  | .function declaration => s!"guestFn_{declaration.name}"
  | .decl _ name _ => s!"guestGlobal_{name}"
  | .exnDecl exception _ => s!"guestExn_{exception}"
  | .name struct _ => s!"guestStruct_{struct}"

def decl : Decl (BitVec 64) → String
  | .function declaration =>
      s!"  Decl.function\n" ++
      s!"    \{ name := {q declaration.name}\n" ++
      s!"      inline := {declaration.inline}\n" ++
      s!"      exported := {declaration.exported}\n" ++
      s!"      params := {list shapeField declaration.params}\n" ++
      s!"      body :=\n{pad 8}{prog 8 declaration.body}\n" ++
      s!"      returnShape := {shape declaration.returnShape} }"
  | .decl sh name value => s!"  Decl.decl {shape sh} {q name} {exp value}"
  | .exnDecl exception sh => s!"  Decl.exnDecl {q exception} {shape sh}"
  | .name struct fields => s!"  Decl.name {q struct} {list shapeField fields}"

def header (source namespace_ : String) : String :=
s!"-- Generated by `lake exe gen-guest-ast {source} {namespace_}`; do not edit by hand.
-- `Guest.AstParse` proves that this is what flapjack's parser produces from
-- `{source}`.
import Flapjack.Language

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace {namespace_}

open Flapjack

"

def render (source namespace_ : String) (declarations : List (Decl (BitVec 64))) : String :=
  let definitions := declarations.map fun declaration =>
    s!"def {declName declaration} : Decl (BitVec 64) :=\n{decl declaration}\n"
  header source namespace_ ++ "\n".intercalate definitions ++
    s!"\n/-- The stateless guest as flapjack Pancake declarations. -/\n" ++
    s!"def guestAst : List (Decl (BitVec 64)) :=\n  [ " ++
    ",\n    ".intercalate (declarations.map declName) ++ s!" ]\n\nend {namespace_}\n"

end GenGuestAst

def main (args : List String) : IO UInt32 := do
  let some (path : String) := args[0]? | do
    IO.eprintln "usage: gen-guest-ast <guest.pp.pnk> [namespace]"
    return 1
  let namespace_ := args[1]?.getD "Guest"
  let source ← IO.FS.readFile ⟨path⟩
  match Parser.parseTopDecs (BitVec.ofInt 64) source with
  | .error errors =>
      IO.eprintln (Parser.formatErrors errors)
      return 1
  | .ok declarations =>
      IO.print (GenGuestAst.render path namespace_ declarations)
      return 0
