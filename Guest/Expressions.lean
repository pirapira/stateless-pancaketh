import Guest.Memory

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

end Guest
