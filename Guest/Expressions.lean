import Guest.Memory
import Guest.Termination

/-!
# An expression layer for the guest's word expressions

`Guest.Memory` gave the word-shaped load and store; this gives the expression
forms the guest actually writes, so that a function's obligations can be
discharged from facts about the state rather than assumed.

* `eval_const`, `eval_var_global`, `eval_var_local` — the leaves.
* `eval_global_add_const` — `base + K` where `base` is a global holding a word.
  This is the guest's pervasive address form (`ev + 64`, `msg + 136`, ...), and
  it *always* succeeds: `RiscV.panRiscVWordOp .add` is total.
* `eval_load_global_add` and its counted form — `lds 1 (base + K)`, the guest's
  pervasive field read, combining this layer with `Guest.Memory`.
* `eval_op2` — any two-argument operator, composing with arbitrary
  sub-expressions; `wordOp_add`/`wordOp_sub` discharge its side condition.
* `eval_cmp_locals` — a comparison of two word locals. Always succeeds:
  `RiscV.panRiscVCmp` is total, so the only way a guest comparison fails to
  evaluate is an unbound or non-word operand.
* `evalCounted_args_two_locals` — a two-local argument list, which is the
  shape of every call the guest makes with two scalar arguments. The list case
  is the *nested* `evalPanValueExp.evalPanValueExps`, not the top-level name.
* `store_terminates` — **a word store terminates as soon as its two expressions
  evaluate.** There is no further obligation, because the access model's
  `domain` is `fun _ => true`.

Note that `evalPanValueExp` is defined by well-founded recursion, so none of
these hold by `rfl`; they go through the equation lemmas, and the list case is
the nested `evalPanValueExp.evalPanValueExps`, not the top-level name.
-/

open Flapjack
namespace Guest

variable (structs : StructContext) (l g : VarName → Option (PanValue Word))
  (m : Memory) (baseAddress topAddress bytesInWord : Word)

/-- A constant. -/
theorem eval_const (k : Word) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.const k) (some guestMemoryAccess) = some (PanValue.word k) := by
  rw [evalPanValueExp]

/-- A global variable. -/
theorem eval_var_global (name : VarName) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.var VarKind.global name) (some guestMemoryAccess) = g name := by
  rw [evalPanValueExp]

/-- A local variable. -/
theorem eval_var_local (name : VarName) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.var VarKind.local name) (some guestMemoryAccess) = l name := by
  rw [evalPanValueExp]

/-- `base + offset` where `base` is a global holding a word: the guest's
pervasive `ev + K` address form. Always succeeds — `panRiscVWordOp .add` is
total. -/
theorem eval_global_add_const (name : VarName) (e k : Word)
    (hname : g name = some (PanValue.word e)) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.global name, Exp.const k])
      (some guestMemoryAccess) = some (PanValue.word (e + k)) := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hname, guestMemoryAccess,
    panValueMemoryAccessOfModel, RiscV.panRiscVMemoryModel, RiscV.panRiscVWordOp]

/-- `lds 1 (base + K)` where `base` is a global holding a word: the guest's
pervasive field read. Combines the expression layer with `Guest.Memory`. -/
theorem eval_load_global_add (name : VarName) (e k v : Word)
    (hname : g name = some (PanValue.word e))
    (hmem : m (e + k) = some (PanValue.word v)) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.global name, Exp.const k]))
      (some guestMemoryAccess) = some (PanValue.word v) := by
  rw [evalPanValueExp]
  rw [eval_global_add_const structs l g m baseAddress topAddress bytesInWord name e k hname]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [panValueFlatLoad_one, guest_readWord, hmem]
  rfl

/-- The counted forms, which is what the statement evaluator actually calls. -/
theorem evalCounted_load_global_add (name : VarName) (e k v : Word)
    (hname : g name = some (PanValue.word e))
    (hmem : m (e + k) = some (PanValue.word v)) :
    evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      (Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.global name, Exp.const k]))
      (some guestMemoryAccess)
      = some (PanValue.word v,
          panValueExpStepCost
            (Exp.load Shape.one
              (Exp.op BinOp.add [Exp.var VarKind.global name, Exp.const k]))) := by
  rw [evalPanValueExpCounted,
    eval_load_global_add structs l g m baseAddress topAddress bytesInWord name e k v hname hmem]
  rfl

/-- A comparison of two locals holding words. Always succeeds:
`RiscV.panRiscVCmp` is total, so the only way a guest comparison fails to
evaluate is an unbound or non-word operand. This is `charge_gas`'s
`gl <+ amount`. -/
theorem eval_cmp_locals (op : Cmp) (n1 n2 : VarName) (a b : Word)
    (h1 : l n1 = some (PanValue.word a)) (h2 : l n2 = some (PanValue.word b)) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.cmp op (Exp.var VarKind.local n1) (Exp.var VarKind.local n2))
      (some guestMemoryAccess) = some (PanValue.word (RiscV.panRiscVCmp op a b)) := by
  rw [evalPanValueExp]
  rw [eval_var_local structs l g m baseAddress topAddress bytesInWord n1,
    eval_var_local structs l g m baseAddress topAddress bytesInWord n2, h1, h2]
  rfl

theorem evalCounted_cmp_locals (op : Cmp) (n1 n2 : VarName) (a b : Word)
    (h1 : l n1 = some (PanValue.word a)) (h2 : l n2 = some (PanValue.word b)) :
    evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      (Exp.cmp op (Exp.var VarKind.local n1) (Exp.var VarKind.local n2))
      (some guestMemoryAccess)
      = some (PanValue.word (RiscV.panRiscVCmp op a b),
          panValueExpStepCost
            (Exp.cmp op (Exp.var VarKind.local n1) (Exp.var VarKind.local n2) : Exp Word)) := by
  rw [evalPanValueExpCounted,
    eval_cmp_locals structs l g m baseAddress topAddress bytesInWord op n1 n2 a b h1 h2]
  rfl

/-- A comparison of a local against a literal. The guest's `w != 0` idiom,
which is how it tests every "did the callee say yes" result --- as in
`access_gas_cost`'s `if w != 0`. -/
theorem eval_cmp_local_const (op : Cmp) (n : VarName) (a k : Word)
    (h : l n = some (PanValue.word a)) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.cmp op (Exp.var VarKind.local n) (Exp.const k))
      (some guestMemoryAccess) = some (PanValue.word (RiscV.panRiscVCmp op a k)) := by
  rw [evalPanValueExp]
  rw [eval_var_local structs l g m baseAddress topAddress bytesInWord n,
    eval_const structs l g m baseAddress topAddress bytesInWord k, h]
  rfl

theorem evalCounted_cmp_local_const (op : Cmp) (n : VarName) (a k : Word)
    (h : l n = some (PanValue.word a)) :
    evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      (Exp.cmp op (Exp.var VarKind.local n) (Exp.const k))
      (some guestMemoryAccess)
      = some (PanValue.word (RiscV.panRiscVCmp op a k),
          panValueExpStepCost
            (Exp.cmp op (Exp.var VarKind.local n) (Exp.const k) : Exp Word)) := by
  rw [evalPanValueExpCounted,
    eval_cmp_local_const structs l g m baseAddress topAddress bytesInWord op n a k h]
  rfl

/-- A two-local argument list, which is every call the guest makes with two
scalar arguments. -/
theorem evalCounted_args_two_locals (n1 n2 : VarName) (a b : Word)
    (h1 : l n1 = some (PanValue.word a)) (h2 : l n2 = some (PanValue.word b)) :
    evalPanValueExpsCounted structs l g m baseAddress topAddress bytesInWord
      [Exp.var VarKind.local n1, Exp.var VarKind.local n2] (some guestMemoryAccess)
      = some ([PanValue.word a, PanValue.word b],
          panValueExpsStepCost
            ([Exp.var VarKind.local n1, Exp.var VarKind.local n2] : List (Exp Word))) := by
  rw [evalPanValueExpsCounted]
  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, h1, h2]

/-- A one-local argument list: the shape of `access_gas_cost(addr)`,
`is_warm_address(addr)` and every other single-scalar call. -/
theorem evalCounted_args_one_local (n : VarName) (a : Word)
    (h : l n = some (PanValue.word a)) :
    evalPanValueExpsCounted structs l g m baseAddress topAddress bytesInWord
      [Exp.var VarKind.local n] (some guestMemoryAccess)
      = some ([PanValue.word a],
          panValueExpsStepCost ([Exp.var VarKind.local n] : List (Exp Word))) := by
  rw [evalPanValueExpsCounted]
  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, h]

section Store
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory)
  (functions : List (FunName × List VarName × Prog Word))
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **What a word store runs to.** An equation, not just termination: to
compose statements sequentially you have to *know* the resulting state, not
merely that one exists. `store_terminates` below is the weaker corollary.

There is no obligation beyond the two expressions evaluating, because the
guest's access model has `domain := fun _ => true` (see `Guest.Memory`), so the
write itself is total. -/
theorem store_runs (address value : Exp Word) (f : FfiState HostMemory)
    (av vv : Word)
    (haddr : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      address (some guestMemoryAccess) = some (PanValue.word av))
    (hvalue : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      value (some guestMemoryAccess) = some (PanValue.word vv)) :
    evalPanValueFfiProgSteps context primitive handler structs functions baseAddress
      topAddress bytesInWord 1 l g m f (Prog.store address value)
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.normal l g
          (fun current => if current == av then some (PanValue.word vv) else m current) f,
        panValueExpStepCost address + panValueExpStepCost value + 1) := by
  rw [evalPanValueFfiProgSteps, evalPanValueExpCounted, evalPanValueExpCounted,
    haddr, hvalue]
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
  rw [guest_store_word_total]
  rfl

/-- Termination of a word store, from `store_runs`. -/
theorem store_terminates (address value : Exp Word) (f : FfiState HostMemory)
    (av vv : Word)
    (haddr : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      address (some guestMemoryAccess) = some (PanValue.word av))
    (hvalue : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      value (some guestMemoryAccess) = some (PanValue.word vv)) :
    StepCalculus.Terminates context primitive handler structs functions baseAddress
      topAddress bytesInWord (some guestMemoryAccess) c mh l g m f
      (Prog.store address value) :=
  ⟨1, _, store_runs structs l g m baseAddress topAddress bytesInWord context primitive
    handler functions c mh address value f av vv haddr hvalue⟩

end Store

/-- **A two-argument operator.** Subsumes `eval_global_add_const` and composes
with any sub-expressions, which is what the guest's address and value
expressions actually need (`gl - amount`, `lds 1 (ev + 184) + amount`, ...).
The `hop` side condition is discharged by `rfl` for the total operators
(`add`, `and`, `or`, `xor`) and for `sub` at two arguments; `panRiscVWordOp`
declines `sub` at any other arity. -/
theorem eval_op2 (op : BinOp) (e1 e2 : Exp Word) (a b w : Word)
    (h1 : evalPanValueExp structs l g m baseAddress topAddress bytesInWord e1
      (some guestMemoryAccess) = some (PanValue.word a))
    (h2 : evalPanValueExp structs l g m baseAddress topAddress bytesInWord e2
      (some guestMemoryAccess) = some (PanValue.word b))
    (hop : RiscV.panRiscVWordOp op [a, b] = some w) :
    evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.op op [e1, e2]) (some guestMemoryAccess) = some (PanValue.word w) := by
  rw [evalPanValueExp]
  simp only [evalPanValueExp.evalPanValueExps, h1, h2, Option.bind_eq_bind,
    Option.bind_some]
  simpa [guestMemoryAccess, panValueMemoryAccessOfModel,
    RiscV.panRiscVMemoryModel] using hop

/-- `sub` of two words is total at two arguments. -/
theorem wordOp_sub (a b : Word) : RiscV.panRiscVWordOp BinOp.sub [a, b] = some (a - b) := rfl

/-- `add` of two words. -/
theorem wordOp_add (a b : Word) : RiscV.panRiscVWordOp BinOp.add [a, b] = some (a + b) := by
  simp [RiscV.panRiscVWordOp]

end Guest
