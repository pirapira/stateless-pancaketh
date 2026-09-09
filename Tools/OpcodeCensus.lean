import Guest.Model

/-!
`lake exe opcode-census`

The work-list for the `run_frames` bound. Issue #73 sketches that bound as
"every opcode costs at least 1 gas"; that is false — `op_stop` charges nothing,
it clears `EV_RUNNING` (offset 104) and returns. The bound that does hold is

> every opcode either charges at least 1 gas, or ends its frame,

so a zero-gas opcode runs at most once per frame. This tool reads the
classification straight off the committed AST (`Guest.guestAst`): it walks
`op_dispatch`'s `if op == k { op_X(); return 0; }` tree for the handler of each
opcode, then inspects each handler.

The classification is deliberately *syntactic and conservative* — it reports
what is evident on the handler's straight-line prefix, and says `unclear` when
a proof will have to look at branches. It is a census, not a proof: turning
`chargesConst` into a semantic fact still needs a lemma about `charge_gas`.
-/

open Flapjack Guest

/-- `EV_RUNNING`, `EV_GAS_LEFT`, `EV_STATE_GAS_LEFT` after cpp expansion. -/
def evRunning : Nat := 104

/-- Straight-line prefix of a body, following `seq` and `dec` into the part
that runs first, stopping at anything that branches. -/
partial def prefixStmts : Prog Word → List (Prog Word)
  | .seq a b => prefixStmts a ++ prefixStmts b
  | .dec _ _ _ body => prefixStmts body
  | .decCall _ _ fn args body => .call none fn args :: prefixStmts body
  | p => [p]

/-- A call to `charge_gas`/`charge_state_gas` with a literal amount. -/
def chargeAmount : Prog Word → Option Nat
  | .call _ name [.const k] =>
      if name == "charge_gas" || name == "charge_state_gas" then some k.toNat else none
  | _ => none

/-- A store of zero to `ev + EV_RUNNING`: the frame stops. -/
def clearsRunning : Prog Word → Bool
  | .store (.op .add [.var _ "ev", .const off]) (.const v) =>
      off.toNat == evRunning && v.toNat == 0
  | _ => false

/-- Does this program contain a `return` on some path? Used to keep the `seq`
rule sound: a charge in the second half does not cover a path that returned out
of the first. -/
partial def containsReturn : Prog Word → Bool
  | .return _ => true
  | .seq a b => containsReturn a || containsReturn b
  | .ite _ t e => containsReturn t || containsReturn e
  | .dec _ _ _ b => containsReturn b
  | .decCall _ _ _ _ b => containsReturn b
  | .while _ b => containsReturn b
  | _ => false

/-- Is this expression certainly ≥ 1? A literal, or a local we are tracking as
positive. -/
def certainlyPositive (pos : List VarName) : Exp Word → Bool
  | .const k => k.toNat ≥ 1
  | .var _ x => pos.contains x
  | _ => false

/-- A `charge_gas`/`charge_state_gas` call whose amount is certainly ≥ 1. -/
def isPositiveCharge (pos : List VarName) (name : FunName) (args : List (Exp Word)) : Bool :=
  (name == "charge_gas" || name == "charge_state_gas") &&
    match args with | [a] => certainlyPositive pos a | _ => false

/-- Locals that stay ≥ 1: an alias of a positive local, or `add_sat` of one
(saturating addition is monotone, so `add_sat a b ≥ a`; plain `+` wraps and is
*not* safe to propagate through). -/
def positiveBinding (pos : List VarName) (fn : FunName) (args : List (Exp Word)) : Bool :=
  fn == "add_sat" && (args.any (certainlyPositive pos))

/-- **Must-charge analysis.** `mustCharge known p` is `true` when *every* path
leaving `p` has either charged at least 1 gas or ended the frame (cleared
`EV_RUNNING`, or raised — `run_frames` catches `EvmErr` into
`frame_exception`, which ends the frame). `known` answers the same question for
callees.

Deliberately conservative: a charge inside a `while` does not count, since the
loop may run zero times, and a `return` that has not yet charged makes the
whole program `false`. -/
partial def mustCharge (known : FunName → Bool) (knownIfArg0 : FunName → Bool)
    (pos : List VarName) : Prog Word → Bool
  | .call _ name args =>
      isPositiveCharge pos name args || known name ||
        (knownIfArg0 name && (args.head?.map (certainlyPositive pos)).getD false)
  | .decCall x _ name args b =>
      isPositiveCharge pos name args || known name ||
        (knownIfArg0 name && (args.head?.map (certainlyPositive pos)).getD false) ||
        mustCharge known knownIfArg0
          (if positiveBinding pos name args then x :: pos else pos) b
  | .raise _ _ => true
  | p@(.store _ _) => clearsRunning p
  | .seq a b =>
      mustCharge known knownIfArg0 pos a ||
        (!containsReturn a && mustCharge known knownIfArg0 pos b)
  | .ite _ t e => mustCharge known knownIfArg0 pos t && mustCharge known knownIfArg0 pos e
  | .dec x _ v b =>
      mustCharge known knownIfArg0 (if certainlyPositive pos v then x :: pos else pos) b
  | _ => false

inductive Verdict | charges (n : Nat) | halts | unclear
  deriving Inhabited

def verdictOf (body : Prog Word) : Verdict :=
  let stmts := prefixStmts body
  match stmts.findSome? chargeAmount with
  | some n => if n ≥ 1 then .charges n else
      if stmts.any clearsRunning then .halts else .unclear
  | none => if stmts.any clearsRunning then .halts else .unclear

/-- Every function in the guest: name, first parameter, body. -/
def allFunctions : List (FunName × Option VarName × Prog Word) :=
  Guest.guestAst.filterMap fun d => match d with
    | .function info => some (info.name, (info.params.head?.map Prod.fst), info.body)
    | _ => none

/-- Least fixpoint of `mustCharge` over the whole program. The call graph is
acyclic (#71), so iterating to stability terminates; the bound is a guard. -/
def mustChargeFixpoint : (FunName → Bool) × (FunName → Bool) := Id.run do
  let mut known : List FunName := []
  let mut knownIfArg0 : List FunName := []
  for _ in [0:64] do
    let k := fun x => known.contains x
    let k0 := fun x => knownIfArg0.contains x
    let next := allFunctions.filterMap fun (n, _, b) =>
      if mustCharge k k0 [] b then some n else none
    let next0 := allFunctions.filterMap fun (n, p, b) =>
      match p with
      | some param => if mustCharge k k0 [param] b then some n else none
      | none => none
    if next.length == known.length && next0.length == knownIfArg0.length then
      return (k, k0)
    known := next; knownIfArg0 := next0
  return (fun x => known.contains x, fun x => knownIfArg0.contains x)

def bodyOf (name : FunName) : Option (Prog Word) :=
  Guest.guestAst.findSome? fun d => match d with
    | .function info => if info.name == name then some info.body else none
    | _ => none

/-- Every `op_*` handler `op_dispatch` can reach. Collected by name rather than
by opcode, because `op_dispatch` mixes equality tests
(`if op == 1 { op_add(); ... }`) with range tests that pass an argument
(`if op <+ 128 { op_push(op - 95); ... }`), and the handler is what gets
classified either way. -/
partial def handlers : Prog Word → List FunName
  | .call _ name _ => if "op_".isPrefixOf name then [name] else []
  | .decCall _ _ name _ b => (if "op_".isPrefixOf name then [name] else []) ++ handlers b
  | .ite _ t e => handlers t ++ handlers e
  | .seq a b => handlers a ++ handlers b
  | .dec _ _ _ b => handlers b
  | .while _ b => handlers b
  | _ => []

def main (args : List String) : IO Unit := do
  let some dispatch := bodyOf "op_dispatch"
    | IO.println "op_dispatch not found"
  let names := (handlers dispatch).eraseDups
  let mut charges : List (FunName × Nat) := []
  let mut halts : List FunName := []
  let mut unclear : List FunName := []
  for name in names do
    match bodyOf name with
    | none => unclear := unclear ++ [name]
    | some body => match verdictOf body with
      | .charges n => charges := charges ++ [(name, n)]
      | .halts => halts := halts ++ [name]
      | .unclear => unclear := unclear ++ [name]
  IO.println s!"{names.length} opcode handlers reachable from op_dispatch"
  IO.println s!"  {charges.length} charge a literal >= 1 gas on their straight-line prefix"
  IO.println s!"  {halts.length} end the frame without charging: {halts}"
  IO.println s!"  {unclear.length} not settled by the straight-line prefix:"
  let (charges?, chargesIfArg0?) := mustChargeFixpoint
  let mut settled : List FunName := []
  let mut open' : List FunName := []
  for name in unclear do
    match bodyOf name with
    | some body => if mustCharge charges? chargesIfArg0? [] body then settled := settled ++ [name]
                   else open' := open' ++ [name]
    | none => open' := open' ++ [name]
  IO.println s!"\nPath-sensitive, interprocedural must-charge analysis on those {unclear.length}:"
  IO.println s!"  {settled.length} charge or end the frame on every path: {settled}"
  IO.println s!"  {open'.length} genuinely need a human:"
  for name in open' do IO.println s!"      {name}"
  if args.contains "--verbose" then
    IO.println "\nup-front charges:"
    for (name, n) in charges do IO.println s!"      {name} charges {n}"
