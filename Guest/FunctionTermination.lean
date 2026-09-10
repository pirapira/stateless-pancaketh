import Guest.Termination
import Guest.Model
import Guest.Expressions
import Guest.Gas

/-!
# Termination of individual guest functions

Where per-function termination results accumulate, using the calculus in
`Guest.Termination` against the AST as committed in `Guest.Ast`.

`charge_gas` is first because it has no loop, so it exercises `dec`, `ite`,
`seq` and the leaves without needing a measure — the cleanest test of whether
the calculus is usable on real code. Two things it showed:

* the leaf rules really are one-liners at the use site (`skip` closes by
  `rw [evalPanValueFfiProgSteps]` alone), so not defining lemmas for them was
  right;
* **`raise` is not free.** `Prog.raise` evaluates its payload and then requires
  `panValueExceptionValid` and `panValuePayloadWithinLimit` against the
  program's contracts, returning `none` otherwise. Every `throw` in the guest
  therefore carries an obligation that the exception is declared with a
  matching shape. True for `guestAst` — `exception EvmErr : 1` — but it has to
  be supplied, and there is one at every raise site.

The remaining hypotheses of `charge_gas_terminates` are the interface for the
memory layer that did not exist when it was written: `Exp.load` and
`Prog.store` bottom out in `panValueFlatLoad` and `panValueStoreWithAccess`,
about which flapjack proves nothing. `Guest.Memory` and `Guest.Expressions`
now supply them, so `charge_gas_terminates_from_state` assumes nothing about
the evaluator at all.

The file then goes one step past termination. `charge_gas_runs_normal` gives
the *equation* for the normal branch — the memory `charge_gas` leaves — and
`charge_gas_decreases_gas` reads off that the gas counter strictly falls. That
is the shape every function on the `run_frames` measure will need: terminating
is not a measure step, decreasing is.
-/

open Flapjack Guest StepCalculus

namespace Guest

/-- The body of `charge_gas`, verbatim from `Guest.guestAst`. -/
def chargeGasBody : Prog Word :=
  match Guest.guestFn_charge_gas with
  | .function info => info.body
  | _ => Prog.skip

/-- The body is what we think it is, straight from the committed AST. -/
theorem chargeGasBody_eq : chargeGasBody =
    Prog.dec "gl" Shape.one
      (Exp.load Shape.one (Exp.op BinOp.add
        [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)]))
      (Prog.seq
        (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "gl")
            (Exp.var VarKind.local "amount"))
          (Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4)))
          Prog.skip)
        (Prog.seq
          (Prog.store (Exp.op BinOp.add
              [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)])
            (Exp.op BinOp.sub
              [Exp.var VarKind.local "gl", Exp.var VarKind.local "amount"]))
          (Prog.seq
            (Prog.store (Exp.op BinOp.add
                [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)])
              (Exp.op BinOp.add
                [Exp.load Shape.one (Exp.op BinOp.add
                  [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)]),
                 Exp.var VarKind.local "amount"]))
            (Prog.return (Exp.const (BitVec.ofNat 64 0)))))) := by
  rfl

/-- The `ev + 64` address expression and the `gl <+ amount` condition. -/
def evGasAddr : Exp Word :=
  Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)]
def gasCond : Exp Word :=
  Exp.cmp Cmp.lower (Exp.var VarKind.local "gl") (Exp.var VarKind.local "amount")
def chargeGasTail : Prog Word :=
  Prog.seq
    (Prog.store evGasAddr
      (Exp.op BinOp.sub [Exp.var VarKind.local "gl", Exp.var VarKind.local "amount"]))
    (Prog.seq
      (Prog.store (Exp.op BinOp.add
          [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)])
        (Exp.op BinOp.add
          [Exp.load Shape.one (Exp.op BinOp.add
            [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)]),
           Exp.var VarKind.local "amount"]))
      (Prog.return (Exp.const (BitVec.ofNat 64 0))))

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (ma : Option (PanValueMemoryAccess Word)) (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **`charge_gas` terminates.** The first end-to-end termination proof of a
real guest function, composed from `dec_terminates`, `ite_terminates` and
`seq_terminates` against the AST as committed (`chargeGasBody` is
`Guest.guestFn_charge_gas`'s body, checked by `rfl` above).

The hypotheses are exactly the four state facts the function needs: its gas
load evaluates and has word shape, its comparison evaluates, and its tail —
the two stores and the `return` — runs. Those are the interface for a memory
layer: `Exp.load` and `Prog.store` bottom out in `panValueFlatLoad` and
`panValueStoreWithAccess`, which have no lemmas yet. -/
theorem charge_gas_terminates
    (l g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState HostMemory)
    (glv : PanValue Word) (vs : Nat)
    (hload : evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      (Exp.load Shape.one evGasAddr) ma = some (glv, vs))
    (hshape : panShapeMatches (panValueShape structs glv) Shape.one = true)
    (cv : Word) (cs : Nat)
    (hcond : evalPanValueExpCounted structs (updatePanValueMap l "gl" glv) g m
      baseAddress topAddress bytesInWord gasCond ma = some (PanValue.word cv, cs))
    -- (see `charge_gas_terminates_of_state` below for the version whose gas
    -- load is derived rather than assumed)
    (hraise : ∀ l' : VarName → Option (PanValue Word),
      Terminates context primitive handler structs functions baseAddress topAddress
        bytesInWord ma c mh l' g m f (Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4))))
    (htail : ∀ l' g' m' f', Terminates context primitive handler structs functions
      baseAddress topAddress bytesInWord ma c mh l' g' m' f' chargeGasTail) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh l g m f chargeGasBody := by
  show Terminates _ _ _ _ _ _ _ _ _ _ _ l g m f (Prog.dec "gl" Shape.one _ _)
  refine dec_terminates context primitive handler structs functions baseAddress
    topAddress bytesInWord ma c mh "gl" Shape.one _ _ l g m f glv vs hload hshape ?_
  -- the body: `ite (gl <+ amount) (raise EvmErr 4) skip ; tail`
  have hite : Terminates context primitive handler structs functions baseAddress
      topAddress bytesInWord ma c mh (updatePanValueMap l "gl" glv) g m f
      (Prog.ite gasCond (Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4))) Prog.skip) := by
    refine ite_terminates context primitive handler structs functions baseAddress
      topAddress bytesInWord ma c mh gasCond _ _ (updatePanValueMap l "gl" glv) g m f
      cv cs hcond ?_ ?_
    · intro _
      exact hraise _
    · intro _
      exact ⟨1, _, by rw [evalPanValueFfiProgSteps]⟩
  obtain ⟨fuel1, r1, hr1⟩ := hite
  obtain ⟨r1a, r1b⟩ := r1
  exact seq_terminates context primitive handler structs functions baseAddress
    topAddress bytesInWord ma c mh _ _ (updatePanValueMap l "gl" glv) g m f
    fuel1 r1a r1b hr1 (fun l'' g'' m'' f'' _ => htail l'' g'' m'' f'')

end

/-- The gas load discharged from the state: if the global `ev` holds a word and
memory holds a word at `ev + 64`, `charge_gas`'s `lds 1 (ev + 64)` evaluates,
and its result has word shape. This is `Guest.Expressions` doing the work that
`charge_gas_terminates` previously assumed. -/
theorem charge_gas_load_of_state (structs : StructContext)
    (l g : VarName → Option (PanValue Word)) (m : Memory)
    (baseAddress topAddress bytesInWord : Word) (e gl : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hmem : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl)) :
    evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      (Exp.load Shape.one evGasAddr) (some guestMemoryAccess)
      = some (PanValue.word gl,
          panValueExpStepCost (Exp.load Shape.one evGasAddr)) :=
  evalCounted_load_global_add structs l g m baseAddress topAddress bytesInWord
    "ev" e (BitVec.ofNat 64 64) gl hev hmem

/-- A word always matches the one-word shape. -/
theorem word_shape_matches (structs : StructContext) (w : Word) :
    panShapeMatches (panValueShape structs (PanValue.word w)) Shape.one = true := by
  simp [panValueShape, panShapeMatches]

/-- **`charge_gas` terminates, with its gas load derived from the state.**
Two of the four obligations of `charge_gas_terminates` are now discharged: it
suffices that the global `ev` holds a word and that memory holds a word at
`ev + 64`. What remains assumed is the comparison (`Exp.cmp`, which the
expression layer does not cover yet) and the tail (two `Prog.store`s, which
need the store side of the expression layer). -/
theorem charge_gas_terminates_of_state
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e gl : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hmem : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (cv : Word) (cs : Nat)
    (hcond : evalPanValueExpCounted structs (updatePanValueMap l "gl" (PanValue.word gl)) g m
      baseAddress topAddress bytesInWord gasCond (some guestMemoryAccess)
      = some (PanValue.word cv, cs))
    (hraise : ∀ l' : VarName → Option (PanValue Word),
      StepCalculus.Terminates context primitive handler structs functions baseAddress
        topAddress bytesInWord (some guestMemoryAccess) c mh l' g m f
        (Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4))))
    (htail : ∀ l' g' m' f', Terminates context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh l' g' m' f'
      chargeGasTail) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord (some guestMemoryAccess) c mh l g m f chargeGasBody :=
  charge_gas_terminates context primitive handler structs functions baseAddress
    topAddress bytesInWord (some guestMemoryAccess) c mh l g m f
    (PanValue.word gl) _
    (charge_gas_load_of_state structs l g m baseAddress topAddress bytesInWord e gl hev hmem)
    (word_shape_matches structs gl) cv cs hcond hraise htail

/-- The tail of `charge_gas` — the two stores and the `return` — terminates,
from state alone.

The second store reads `ev + 184` *after* the first has written `ev + 64`, so
the proof needs the two addresses to be distinct; `hne` is that, and it is the
kind of side condition that only shows up once statements are composed for
real. `store_runs` is what makes it expressible: knowing the resulting memory,
rather than only that the store terminated, is what lets the next statement be
evaluated at all. -/
theorem charge_gas_tail_terminates
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e gl amount used : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hgl : l "gl" = some (PanValue.word gl))
    (hamount : l "amount" = some (PanValue.word amount))
    (hused : m (e + BitVec.ofNat 64 184) = some (PanValue.word used))
    (hne : ((e + BitVec.ofNat 64 184) == (e + BitVec.ofNat 64 64)) = false)
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true) :
    StepCalculus.Terminates context primitive handler structs functions baseAddress
      topAddress bytesInWord (some guestMemoryAccess) c mh l g m f chargeGasTail := by
  have haddr1 : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      evGasAddr (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 64)) :=
    eval_global_add_const structs l g m baseAddress topAddress bytesInWord "ev" e _ hev
  have hval1 : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.sub [Exp.var VarKind.local "gl", Exp.var VarKind.local "amount"])
      (some guestMemoryAccess) = some (PanValue.word (gl - amount)) := by
    refine eval_op2 structs l g m baseAddress topAddress bytesInWord BinOp.sub _ _ gl amount _
      ?_ ?_ (wordOp_sub gl amount)
    · rw [eval_var_local]; exact hgl
    · rw [eval_var_local]; exact hamount
  have hrun1 := store_runs structs l g m baseAddress topAddress bytesInWord context
    primitive handler functions c mh evGasAddr _ f _ _ haddr1 hval1
  refine StepCalculus.seq_terminates context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ l g m f
    1 _ _ hrun1 ?_
  intro l' g' m' f' heq
  -- the first store left locals, globals and ffi alone, and the memory updated
  -- at `ev + 64` only
  injection heq with hl' hg' hm' hf'
  subst hl'; subst hg'; subst hm'; subst hf'
  -- the memory after the first store still holds `used` at `ev + 184`
  have hused' : (fun current => if current == e + BitVec.ofNat 64 64
      then some (PanValue.word (gl - amount)) else m current)
      (e + BitVec.ofNat 64 184) = some (PanValue.word used) := by
    simp only [hne]
    exact hused
  have haddr2 : evalPanValueExp structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)])
      (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 184)) :=
    eval_global_add_const structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord "ev" e _ hev
  have hload2 : evalPanValueExp structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord
      (Exp.load Shape.one (Exp.op BinOp.add
        [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)]))
      (some guestMemoryAccess) = some (PanValue.word used) :=
    eval_load_global_add structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord "ev" e _ used
      hev hused'
  have hval2 : evalPanValueExp structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.load Shape.one (Exp.op BinOp.add
          [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)]),
        Exp.var VarKind.local "amount"])
      (some guestMemoryAccess) = some (PanValue.word (used + amount)) := by
    refine eval_op2 structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord BinOp.add _ _ used amount _
      hload2 ?_ (wordOp_add used amount)
    rw [eval_var_local]; exact hamount
  have hrun2 := store_runs structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr2 hval2
  refine StepCalculus.seq_terminates context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ l g _ f
    1 _ _ hrun2 ?_
  intro l'' g'' m'' f'' heq2
  injection heq2 with hl'' hg'' hm'' hf''
  subst hl''; subst hg''; subst hm''; subst hf''
  exact StepCalculus.return_terminates context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ l g _ f _ _
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimit


/-- **`charge_gas` terminates, from state alone.** No hypothesis about the
evaluator remains: it suffices that the global `ev` holds a word, that memory
holds words at the two fields `charge_gas` touches, that `amount` is bound to a
word, that those two addresses differ, and that the program declares `EvmErr`
with a matching shape and admits the payloads.

The last group is not incidental. `Prog.raise` and `Prog.return` check their
payload against the program's contracts and answer `none` otherwise, so a proof
about *any* guest function carries them — the control-flow analogue of the
no-wraparound conditions the loop measures need.

Both branches are taken: out of gas, where the `ite` raises and the tail never
runs; and the normal path, where the `ite` falls through with the state
unchanged and the tail does the two stores and the `return`. Joining them is
what needed the `_runs` layer of `Guest.Termination`: `seq` has to *know* the
`ite`'s result, not merely that it had one. -/
theorem charge_gas_terminates_from_state
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e gl amount used : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hgas : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hused : m (e + BitVec.ofNat 64 184) = some (PanValue.word used))
    (hamount : l "amount" = some (PanValue.word amount))
    (hne : ((e + BitVec.ofNat 64 184) == (e + BitVec.ofNat 64 64)) = false)
    (hraiseValid : (panValueExceptionValid structs c "EvmErr"
        (PanValue.word (BitVec.ofNat 64 4)) &&
      panValuePayloadWithinLimit structs (PanValue.word (BitVec.ofNat 64 4))) = true)
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true) :
    StepCalculus.Terminates context primitive handler structs functions baseAddress
      topAddress bytesInWord (some guestMemoryAccess) c mh l g m f chargeGasBody := by
  have hgl' : updatePanValueMap l "gl" (PanValue.word gl) "gl"
      = some (PanValue.word gl) := by simp [updatePanValueMap]
  have hamount' : updatePanValueMap l "gl" (PanValue.word gl) "amount"
      = some (PanValue.word amount) := by simp [updatePanValueMap, hamount]
  have hcond := evalCounted_cmp_locals structs (updatePanValueMap l "gl" (PanValue.word gl))
    g m baseAddress topAddress bytesInWord Cmp.lower "gl" "amount" gl amount hgl' hamount'
  refine StepCalculus.dec_terminates context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "gl" Shape.one _ _
    l g m f (PanValue.word gl) _
    (charge_gas_load_of_state structs l g m baseAddress topAddress bytesInWord e gl hev hgas)
    (word_shape_matches structs gl) ?_
  by_cases hz : ((RiscV.panRiscVCmp Cmp.lower gl amount) != 0) = true
  · -- out of gas: the `ite` raises, and the `seq` stops there
    have hraise := StepCalculus.raise_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
      "EvmErr" (Exp.const (BitVec.ofNat 64 4)) (updatePanValueMap l "gl" (PanValue.word gl))
      g m f _ _ 0 (by rw [evalPanValueExpCounted, eval_const]; rfl) hraiseValid
    have hite := StepCalculus.ite_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (thenBranch := Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4)))
      (elseBranch := Prog.skip)
      (updatePanValueMap l "gl" (PanValue.word gl)) g m f _ _ 1 _ _ hcond
      (by rw [if_pos hz]; exact hraise)
    exact ⟨3, _, StepCalculus.seq_runs_raised context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ _ _ _ _ _ _ _
      2 _ _ _ hite⟩
  · -- normal path: the `ite` falls through unchanged, then the tail runs
    have hskip := StepCalculus.skip_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
      (updatePanValueMap l "gl" (PanValue.word gl)) g m f 0
    have hite := StepCalculus.ite_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (thenBranch := Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4)))
      (elseBranch := Prog.skip)
      (updatePanValueMap l "gl" (PanValue.word gl)) g m f _ _ 1 _ _ hcond
      (by rw [if_neg hz]; exact hskip)
    exact StepCalculus.seq_terminates context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g m f
      2 _ _ hite
      (fun l'' g'' m'' f'' heq => by
        injection heq with h1 h2 h3 h4
        subst h1; subst h2; subst h3; subst h4
        exact charge_gas_tail_terminates
          (l := updatePanValueMap l "gl" (PanValue.word gl)) (g := g) (m := m) (f := f)
          (e := e) (gl := gl) (amount := amount) (used := used)
          (hev := hev) (hgl := hgl') (hamount := hamount') (hused := hused)
          (hne := hne) (hlimit := hlimit))

/-!
## `charge_gas` semantically: the gas goes down

Termination is not enough for `run_frames`. Its measure is the gas left, so
what the loop needs is that a charge *moves* it: an equation for the state
`charge_gas` leaves, not merely a witness that it left one.

`charge_gas_runs_normal` is that equation, on the branch the charge fits, and
`charge_gas_decreases_gas` reads the measure off it. The two together are the
semantic form of the census's "every opcode charges at least one gas or ends
its frame" — the half about charging.

Note where the wrap-around condition surfaces: `hfits` (`amount <= gl`
unsigned) is both what makes the guest's `ite` fall through and what makes
`gl - amount` an actual decrease. Those are the same fact, and
`Guest.Gas.cmp_lower_false_of_le` is the bridge.
-/

/-- The memory `charge_gas` leaves behind on its normal path. -/
def chargeGasMemory (m : Memory) (e gl amount used : Word) : Memory :=
  fun current =>
    if current == e + BitVec.ofNat 64 184 then some (PanValue.word (used + amount))
    else if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount))
    else m current

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **What `charge_gas`'s tail runs to** — `charge_gas_tail_terminates` with
the resulting state pinned down. Same hypotheses, strictly more information;
the terminating form stays because it is what the earlier composition proof
takes. -/
theorem charge_gas_tail_runs
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e gl amount used : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hgl : l "gl" = some (PanValue.word gl))
    (hamount : l "amount" = some (PanValue.word amount))
    (hused : m (e + BitVec.ofNat 64 184) = some (PanValue.word used))
    (hne : ((e + BitVec.ofNat 64 184) == (e + BitVec.ofNat 64 64)) = false)
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true) :
    ∃ steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 3 l g m f chargeGasTail
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned (fun _ => none) g
          (chargeGasMemory m e gl amount used) f
          [PanValue.word (BitVec.ofNat 64 0)], steps) := by
  -- the first store: `ev + 64 := gl - amount`
  have haddr1 : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      evGasAddr (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 64)) :=
    eval_global_add_const structs l g m baseAddress topAddress bytesInWord "ev" e _ hev
  have hval1 : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.sub [Exp.var VarKind.local "gl", Exp.var VarKind.local "amount"])
      (some guestMemoryAccess) = some (PanValue.word (gl - amount)) := by
    refine eval_op2 structs l g m baseAddress topAddress bytesInWord BinOp.sub _ _ gl amount _
      ?_ ?_ (wordOp_sub gl amount)
    · rw [eval_var_local]; exact hgl
    · rw [eval_var_local]; exact hamount
  have hrun1 := store_runs structs l g m baseAddress topAddress bytesInWord context
    primitive handler functions c mh evGasAddr _ f _ _ haddr1 hval1
  have hrun1' := progMono context primitive handler structs functions baseAddress
    topAddress bytesInWord 1 l g m f (Prog.store evGasAddr _) (some guestMemoryAccess) c mh
    2 _ (by omega) hrun1
  -- the memory after the first store
  -- the memory after the first store still holds `used` at `ev + 184`
  have hused' : (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) (e + BitVec.ofNat 64 184) = some (PanValue.word used) := by
    simp only [hne]; exact hused
  have haddr2 : evalPanValueExp structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)])
      (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 184)) :=
    eval_global_add_const structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord "ev" e _ hev
  have hload2 : evalPanValueExp structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord
      (Exp.load Shape.one (Exp.op BinOp.add
        [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)]))
      (some guestMemoryAccess) = some (PanValue.word used) :=
    eval_load_global_add structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord "ev" e _ used
      hev hused'
  have hval2 : evalPanValueExp structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.load Shape.one (Exp.op BinOp.add
          [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 184)]),
        Exp.var VarKind.local "amount"])
      (some guestMemoryAccess) = some (PanValue.word (used + amount)) := by
    refine eval_op2 structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord BinOp.add _ _ used
      amount _ hload2 ?_ (wordOp_add used amount)
    rw [eval_var_local]; exact hamount
  have hrun2 := store_runs structs l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr2 hval2
  -- the `return`
  have hret := StepCalculus.return_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (Exp.const (BitVec.ofNat 64 0)) l g
    (fun current => if current == e + BitVec.ofNat 64 184
      then some (PanValue.word (used + amount)) else (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) current) f _ _ 0
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimit
  have hinner := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) f
    l g _ f 1 _ _ _ hrun2 hret
  have houter := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ l g m f
    l g (fun current => if current == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - amount)) else m current) f 2 _ _ _ hrun1' hinner
  exact ⟨_, houter⟩


/-- **What `charge_gas` runs to when the charge fits.** The memory it leaves is
`chargeGasMemory`: `ev + 64` holds `gl - amount` and `ev + 184` holds
`used + amount`. This is the equation the `run_frames` measure needs — knowing
only that `charge_gas` terminates says nothing about the gas going down.

The locals are existential because `return` discards them and `dec` restores
`gl` over the discarded map; nothing downstream reads them. -/
theorem charge_gas_runs_normal
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e gl amount used : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hgas : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hused : m (e + BitVec.ofNat 64 184) = some (PanValue.word used))
    (hamount : l "amount" = some (PanValue.word amount))
    (hne : ((e + BitVec.ofNat 64 184) == (e + BitVec.ofNat 64 64)) = false)
    (hfits : amount.toNat ≤ gl.toNat)
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 5 l g m f chargeGasBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' g
          (chargeGasMemory m e gl amount used) f
          [PanValue.word (BitVec.ofNat 64 0)], steps) := by
  have hgl' : updatePanValueMap l "gl" (PanValue.word gl) "gl"
      = some (PanValue.word gl) := by simp [updatePanValueMap]
  have hamount' : updatePanValueMap l "gl" (PanValue.word gl) "amount"
      = some (PanValue.word amount) := by simp [updatePanValueMap, hamount]
  have hcond := evalCounted_cmp_locals structs (updatePanValueMap l "gl" (PanValue.word gl))
    g m baseAddress topAddress bytesInWord Cmp.lower "gl" "amount" gl amount hgl' hamount'
  -- the charge fits, so the `ite` falls through with the state unchanged
  have hz : ((RiscV.panRiscVCmp Cmp.lower gl amount) != 0) = false :=
    cmp_lower_false_of_le hfits
  have hskip := StepCalculus.skip_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f 1
  have hite := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4)))
    (elseBranch := Prog.skip)
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f _ _ 2 _ _ hcond
    (by rw [if_neg (by rw [hz]; simp)]; exact hskip)
  obtain ⟨ts, htail⟩ := charge_gas_tail_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord c mh
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f e gl amount used
    hev hgl' hamount' hused hne hlimit
  have hbody := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f 3 _ _ _ hite htail
  have hfinal := StepCalculus.dec_runs context primitive handler structs functions baseAddress topAddress
    bytesInWord (some guestMemoryAccess) c mh "gl" Shape.one _ _ l g m f
    (PanValue.word gl) _ 4 _ _
    (charge_gas_load_of_state structs l g m baseAddress topAddress bytesInWord e gl hev hgas)
    (word_shape_matches structs gl) hbody
  rw [chargeGasBody_eq]
  exact ⟨_, _, hfinal⟩

/-- **Charging strictly decreases the gas counter.** `charge_gas` leaves
`ev + 64` holding `gl - amount`, and unsigned subtraction that does not borrow
is a genuine decrease whenever the charge is at least one. Together with
`charge_gas_runs_normal` this is the step the `run_frames` measure rests on:
the opcode census says every handler either charges `>= 1` gas or ends its
frame, and this says charging `>= 1` gas moves the measure down. -/
theorem charge_gas_decreases_gas (m : Memory) (e gl amount used : Word)
    (hne : ((e + BitVec.ofNat 64 184) == (e + BitVec.ofNat 64 64)) = false)
    (hfits : amount.toNat ≤ gl.toNat) (hpos : 1 ≤ amount.toNat) :
    ∃ gl', chargeGasMemory m e gl amount used (e + BitVec.ofNat 64 64)
        = some (PanValue.word gl') ∧ gl'.toNat < gl.toNat := by
  have hne' : ((e + BitVec.ofNat 64 64) == (e + BitVec.ofNat 64 184)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq] at hne ⊢
    exact fun h => hne h.symm
  refine ⟨gl - amount, ?_, gas_strictly_decreases hfits hpos⟩
  simp [chargeGasMemory, hne']

end

end Guest
