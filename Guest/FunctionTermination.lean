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

/-!
## `add_sat`, the first callee

`charge_state_gas`'s spill path calls `add_sat`, so it is the first function
that has to be proved as a *callee* rather than entered at the top. Nothing
here is new machinery — it is the same `_runs` layer — but it is the first
place `seq_runs_returned` earns its keep twice over, and the first result
whose statement has to say that the callee left the heap alone, because
`decCall` runs its body in the callee's memory and FFI state.
-/

/-- The body of `add_sat`, verbatim from `Guest.guestAst`. -/
def addSatBody : Prog Word :=
  match Guest.guestFn_add_sat with
  | .function info => info.body
  | _ => Prog.skip

theorem addSatBody_eq : addSatBody =
    Prog.dec "s" Shape.one
      (Exp.op BinOp.add [Exp.var VarKind.local "a", Exp.var VarKind.local "b"])
      (Prog.seq
        (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "s")
            (Exp.var VarKind.local "a"))
          (Prog.return (Exp.const (BitVec.ofNat 64 18446744073709551615)))
          Prog.skip)
        (Prog.return (Exp.var VarKind.local "s"))) := by
  rfl

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **What `add_sat`'s body runs to.** The first callee proved end to end, and
the first use of the `_runs` layer on a function that is *called* rather than
entered at the top.

Both paths are here: a carry, where the `ite` returns `WORD_MAX` from inside
the `seq` (`seq_runs_returned` again), and no carry, where it falls through to
`return s`. Neither touches memory, which is why the result keeps `m` and `f`
unchanged — worth stating, because `decCall` runs its body in the *callee's*
heap and this says the callee left it alone. -/
theorem add_sat_runs
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (a b : Word)
    (ha : l "a" = some (PanValue.word a))
    (hb : l "b" = some (PanValue.word b))
    (hlimitMax : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 18446744073709551615)) = true)
    (hlimitSum : panValuePayloadWithinLimit structs
      (PanValue.word (a + b)) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 4 l g m f addSatBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' g m f
          [PanValue.word (addSatOf a b)], steps) := by
  have ha' : updatePanValueMap l "s" (PanValue.word (a + b)) "a"
      = some (PanValue.word a) := by simp [updatePanValueMap, ha]
  have hs' : updatePanValueMap l "s" (PanValue.word (a + b)) "s"
      = some (PanValue.word (a + b)) := by simp [updatePanValueMap]
  have hcond := evalCounted_cmp_locals structs (updatePanValueMap l "s" (PanValue.word (a + b)))
    g m baseAddress topAddress bytesInWord Cmp.lower "s" "a" (a + b) a hs' ha'
  -- the initialiser `s := a + b`
  have hadd : evalPanValueExp structs l g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.local "a", Exp.var VarKind.local "b"])
      (some guestMemoryAccess) = some (PanValue.word (a + b)) := by
    refine eval_op2 structs l g m baseAddress topAddress bytesInWord BinOp.add _ _ a b _
      ?_ ?_ (wordOp_add a b)
    · rw [eval_var_local]; exact ha
    · rw [eval_var_local]; exact hb
  have hinit : evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.local "a", Exp.var VarKind.local "b"])
      (some guestMemoryAccess)
      = some (PanValue.word (a + b),
          panValueExpStepCost
            (Exp.op BinOp.add [Exp.var VarKind.local "a", Exp.var VarKind.local "b"]
              : Exp Word)) := by
    rw [evalPanValueExpCounted, hadd]; rfl
  -- the tail `return s`
  have htail := StepCalculus.return_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (Exp.var VarKind.local "s")
    (updatePanValueMap l "s" (PanValue.word (a + b))) g m f _ _ 1
    (by rw [evalPanValueExpCounted, eval_var_local, hs']; rfl) hlimitSum
  by_cases hz : ((RiscV.panRiscVCmp Cmp.lower (a + b) a) != 0) = true
  · -- carry: the `ite` returns WORD_MAX and the `seq` stops there
    have hmax := StepCalculus.return_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
      (Exp.const (BitVec.ofNat 64 18446744073709551615))
      (updatePanValueMap l "s" (PanValue.word (a + b))) g m f _ _ 0
      (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimitMax
    have hite := StepCalculus.ite_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (thenBranch := Prog.return (Exp.const (BitVec.ofNat 64 18446744073709551615)))
      (elseBranch := Prog.skip)
      (updatePanValueMap l "s" (PanValue.word (a + b))) g m f _ _ 1 _ _ hcond
      (by rw [if_pos hz]; exact hmax)
    have hseq := StepCalculus.seq_runs_returned context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (second := Prog.return (Exp.var VarKind.local "s"))
      (updatePanValueMap l "s" (PanValue.word (a + b))) g m f _ g m f 2 _ _ hite
    have hfinal := StepCalculus.dec_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "s" Shape.one _ _
      l g m f (PanValue.word (a + b)) _ 3 _ _ hinit
      (word_shape_matches structs (a + b)) hseq
    have hsat : addSatOf a b = BitVec.ofNat 64 18446744073709551615 := by
      simp only [addSatOf, if_pos (cmp_lower_true_iff.mp hz)]
    rw [addSatBody_eq, hsat]
    exact ⟨_, _, hfinal⟩
  · -- no carry: the `ite` falls through and the tail returns `s`
    have hskip := StepCalculus.skip_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
      (updatePanValueMap l "s" (PanValue.word (a + b))) g m f 0
    have hite := StepCalculus.ite_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (thenBranch := Prog.return (Exp.const (BitVec.ofNat 64 18446744073709551615)))
      (elseBranch := Prog.skip)
      (updatePanValueMap l "s" (PanValue.word (a + b))) g m f _ _ 1 _ _ hcond
      (by rw [if_neg hz]; exact hskip)
    have hseq := StepCalculus.seq_runs_normal context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _
      (updatePanValueMap l "s" (PanValue.word (a + b))) g m f
      (updatePanValueMap l "s" (PanValue.word (a + b))) g m f 2 _ _ _ hite htail
    have hfinal := StepCalculus.dec_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "s" Shape.one _ _
      l g m f (PanValue.word (a + b)) _ 3 _ _ hinit
      (word_shape_matches structs (a + b)) hseq
    have hsat : addSatOf a b = a + b := by
      simp only [addSatOf, if_neg (fun hlt => hz (cmp_lower_true_iff.mpr hlt))]
    rw [addSatBody_eq, hsat]
    exact ⟨_, _, hfinal⟩

end

/-!
## The second gas counter: `charge_state_gas`

`charge_gas` only ever touches `EV_GAS_LEFT`. `charge_state_gas`
(`guest/src/evm.pnk:249`) draws from the `EV_STATE_GAS_LEFT` reservoir first
and spills into `EV_GAS_LEFT` only when the reservoir is short, so the
`run_frames` measure has to be the sum of the two and both of its paying paths
have to be accounted for.

The reservoir path is done here. It is the self-contained one: it returns
before reaching `add_sat`, so it needs no call rule, and
`charge_state_gas_decreases_sum_reservoir` reads the measure straight off the
resulting memory. The spill path (`chargeStateGasSpill`) does call `add_sat`,
which is what `callSteps_runs_returned` was added for.

Note the early `return` from inside a `seq` — the reservoir branch returns
while the `add_sat` half of the body is still syntactically ahead of it. That
is what `seq_runs_returned` is for; `seq_runs_raised` alone was not enough.
-/

/-- The body of `charge_state_gas`, verbatim from `Guest.guestAst`. -/
def chargeStateGasBody : Prog Word :=
  match Guest.guestFn_charge_state_gas with
  | .function info => info.body
  | _ => Prog.skip

/-- The `add_sat` spill branch — everything `charge_state_gas` does when the
reservoir is short. Named so the reservoir path can say what it *skips*. -/
def chargeStateGasSpill : Prog Word :=
  Prog.decCall "tot" Shape.one "add_sat"
    [Exp.var VarKind.local "sgl", Exp.var VarKind.local "gl"]
    (Prog.seq
      (Prog.ite (Exp.cmp Cmp.notLower (Exp.var VarKind.local "tot")
          (Exp.var VarKind.local "amount"))
        (Prog.dec "rem" Shape.one
          (Exp.op BinOp.sub [Exp.var VarKind.local "amount", Exp.var VarKind.local "sgl"])
          (Prog.seq
            (Prog.store (Exp.op BinOp.add
                [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 72)])
              (Exp.const (BitVec.ofNat 64 0)))
            (Prog.seq
              (Prog.store (Exp.op BinOp.add
                  [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)])
                (Exp.op BinOp.sub
                  [Exp.var VarKind.local "gl", Exp.var VarKind.local "rem"]))
              (Prog.seq
                (Prog.store (Exp.op BinOp.add
                    [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 192)])
                  (Exp.op BinOp.add
                    [Exp.load Shape.one (Exp.op BinOp.add
                      [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 192)]),
                     Exp.var VarKind.local "rem"]))
                (Prog.return (Exp.const (BitVec.ofNat 64 0)))))))
        Prog.skip)
      (Prog.seq
        (Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4)))
        (Prog.return (Exp.const (BitVec.ofNat 64 0)))))

/-- The reservoir branch: store `sgl - amount` at `ev + 72` and return. -/
def chargeStateGasReservoir : Prog Word :=
  Prog.seq
    (Prog.store (Exp.op BinOp.add
        [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 72)])
      (Exp.op BinOp.sub [Exp.var VarKind.local "sgl", Exp.var VarKind.local "amount"]))
    (Prog.return (Exp.const (BitVec.ofNat 64 0)))

/-- The body is what we think it is, straight from the committed AST. -/
theorem chargeStateGasBody_eq : chargeStateGasBody =
    Prog.dec "sgl" Shape.one
      (Exp.load Shape.one (Exp.op BinOp.add
        [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 72)]))
      (Prog.dec "gl" Shape.one
        (Exp.load Shape.one (Exp.op BinOp.add
          [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)]))
        (Prog.seq
          (Prog.ite (Exp.cmp Cmp.notLower (Exp.var VarKind.local "sgl")
              (Exp.var VarKind.local "amount"))
            chargeStateGasReservoir Prog.skip)
          chargeStateGasSpill)) := by
  rfl

/-- The reservoir branch's payload: store `sgl - amount` at `ev + 72`, return 0. -/
def chargeStateGasReservoirMemory (m : Memory) (e sgl amount : Word) : Memory :=
  fun current =>
    if current == e + BitVec.ofNat 64 72 then some (PanValue.word (sgl - amount))
    else m current

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

theorem charge_state_gas_runs_reservoir
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e sgl gl amount : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hsgl : m (e + BitVec.ofNat 64 72) = some (PanValue.word sgl))
    (hgl : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hamount : l "amount" = some (PanValue.word amount))
    (hfits : amount.toNat ≤ sgl.toNat)
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 6 l g m f chargeStateGasBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' g
          (chargeStateGasReservoirMemory m e sgl amount) f
          [PanValue.word (BitVec.ofNat 64 0)], steps) := by
  -- locals after the two `dec`s
  have hsgl' : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "sgl" = some (PanValue.word sgl) := by
    simp [updatePanValueMap]
  have hamount' : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "amount" = some (PanValue.word amount) := by
    simp [updatePanValueMap, hamount]
  have hev' : g "ev" = some (PanValue.word e) := hev
  -- the reservoir test is true
  have hz : ((RiscV.panRiscVCmp Cmp.notLower sgl amount) != 0) = true :=
    cmp_notLower_true_of_le hfits
  have hcond := evalCounted_cmp_locals structs
    (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl" (PanValue.word gl))
    g m baseAddress topAddress bytesInWord Cmp.notLower "sgl" "amount" sgl amount
    hsgl' hamount'
  -- the then-branch: store ev+72 := sgl - amount, then return 0
  have haddr : evalPanValueExp structs
      (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl" (PanValue.word gl))
      g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 72)])
      (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 72)) :=
    eval_global_add_const structs _ g m baseAddress topAddress bytesInWord "ev" e _ hev'
  have hval : evalPanValueExp structs
      (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl" (PanValue.word gl))
      g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.sub [Exp.var VarKind.local "sgl", Exp.var VarKind.local "amount"])
      (some guestMemoryAccess) = some (PanValue.word (sgl - amount)) := by
    refine eval_op2 structs _ g m baseAddress topAddress bytesInWord BinOp.sub _ _ sgl amount _
      ?_ ?_ (wordOp_sub sgl amount)
    · rw [eval_var_local]; exact hsgl'
    · rw [eval_var_local]; exact hamount'
  have hstore := store_runs structs _ g m baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr hval
  have hret := StepCalculus.return_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (Exp.const (BitVec.ofNat 64 0))
    (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl" (PanValue.word gl))
    g (chargeStateGasReservoirMemory m e sgl amount) f _ _ 0
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimit
  have hthen := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g m f
    _ g (chargeStateGasReservoirMemory m e sgl amount) f 1 _ _ _ hstore hret
  have hite := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := chargeStateGasReservoir)
    (elseBranch := Prog.skip)
    (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl)) g m f _ _ 2 _ _ hcond (by rw [if_pos hz]; exact hthen)
  have houter := StepCalculus.seq_runs_returned context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (second := chargeStateGasSpill) _ g m f
    _ g (chargeStateGasReservoirMemory m e sgl amount) f 3 _ _ hite
  -- the two `dec`s
  have hloadgl := evalCounted_load_global_add structs
    (updatePanValueMap l "sgl" (PanValue.word sgl)) g m baseAddress topAddress bytesInWord
    "ev" e (BitVec.ofNat 64 64) gl hev' hgl
  have hdecgl := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "gl" Shape.one _ _
    (updatePanValueMap l "sgl" (PanValue.word sgl)) g m f (PanValue.word gl) _ 4 _ _
    hloadgl (word_shape_matches structs gl) houter
  have hloadsgl := evalCounted_load_global_add structs l g m baseAddress topAddress
    bytesInWord "ev" e (BitVec.ofNat 64 72) sgl hev' hsgl
  have hfinal := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "sgl" Shape.one _ _
    l g m f (PanValue.word sgl) _ 5 _ _
    hloadsgl (word_shape_matches structs sgl) hdecgl
  rw [chargeStateGasBody_eq]
  exact ⟨_, _, hfinal⟩


/-- **The reservoir charge moves the measure down.** Reading the two counters
back out of the memory `charge_state_gas` leaves on its reservoir path: the
reservoir has fallen by `amount` and `EV_GAS_LEFT` is untouched, so the sum is
strictly smaller. `hne` is only the disjointness of the two fields. -/
theorem charge_state_gas_decreases_sum_reservoir
    (m : Memory) (e sgl gl amount : Word)
    (hgl : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hne : ((e + BitVec.ofNat 64 64) == (e + BitVec.ofNat 64 72)) = false)
    (hfits : amount.toNat ≤ sgl.toNat) (hpos : 1 ≤ amount.toNat) :
    ∃ sgl' gl',
      chargeStateGasReservoirMemory m e sgl amount (e + BitVec.ofNat 64 72)
          = some (PanValue.word sgl') ∧
      chargeStateGasReservoirMemory m e sgl amount (e + BitVec.ofNat 64 64)
          = some (PanValue.word gl') ∧
      sgl'.toNat + gl'.toNat < sgl.toNat + gl.toNat := by
  refine ⟨sgl - amount, gl, ?_, ?_, state_gas_sum_decreases_reservoir hfits hpos⟩
  · simp [chargeStateGasReservoirMemory]
  · simp [chargeStateGasReservoirMemory, hne, hgl]

end

/-!
## `charge_state_gas`, spill path

When the reservoir is short, `charge_state_gas` asks `add_sat` whether the two
counters *together* cover the charge, and if so empties the reservoir and
takes the remainder out of `EV_GAS_LEFT`.

This is the first path in the guest that leaves its own function and comes
back, so it is where `decCall_runs` and `callSteps_runs_returned_none` get
used for real. The rest is straight-line: three stores and a `return`, with
the last store *reading* `EV_STATE_GAS_SPILLED` after the first two have run —
which is the only reason disjointness hypotheses appear, and why they are only
about `ev + 192`.

`charge_state_gas_decreases_sum_spill` closes the measure argument for this
path. The link is `addSatOf_le_sum`: the guest's `tot >=+ amount` test bounds
`amount` by the *saturating* sum, and that bounds it by the true sum, which is
exactly the no-borrow condition `state_gas_sum_decreases_spill` wants.
-/

/-- `add_sat`'s parameters bind to its two arguments. Computed, not assumed. -/
theorem add_sat_binds (a b : Word) :
    bindPanValueParameters ["a", "b"] [PanValue.word a, PanValue.word b]
      = some (updatePanValueMap
          (updatePanValueMap (fun _ => none) "a" (PanValue.word a))
          "b" (PanValue.word b)) := by
  simp [bindPanValueParameters]

/-- The paying branch of the spill test: empty the reservoir, take the
remainder from `EV_GAS_LEFT`, record it in `EV_STATE_GAS_SPILLED`, return. -/
def chargeStateGasSpillStores : Prog Word :=
  (Prog.dec "rem" Shape.one
        (Exp.op BinOp.sub [Exp.var VarKind.local "amount", Exp.var VarKind.local "sgl"])
        (Prog.seq
          (Prog.store (Exp.op BinOp.add
              [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 72)])
            (Exp.const (BitVec.ofNat 64 0)))
          (Prog.seq
            (Prog.store (Exp.op BinOp.add
                [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)])
              (Exp.op BinOp.sub
                [Exp.var VarKind.local "gl", Exp.var VarKind.local "rem"]))
            (Prog.seq
              (Prog.store (Exp.op BinOp.add
                  [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 192)])
                (Exp.op BinOp.add
                  [Exp.load Shape.one (Exp.op BinOp.add
                    [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 192)]),
                   Exp.var VarKind.local "rem"]))
              (Prog.return (Exp.const (BitVec.ofNat 64 0)))))))

/-- The memory `charge_state_gas` leaves on its spill path: the reservoir is
emptied, the remainder comes out of `EV_GAS_LEFT`, and `EV_STATE_GAS_SPILLED`
records what was borrowed. -/
def chargeStateGasSpillMemory (m : Memory) (e sgl gl amount spilled : Word) : Memory :=
  fun current =>
    if current == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled + (amount - sgl)))
    else if current == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl - (amount - sgl)))
    else if current == e + BitVec.ofNat 64 72 then
      some (PanValue.word (BitVec.ofNat 64 0))
    else m current

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **The `add_sat` call inside `charge_state_gas`.** The only part of the
spill path that leaves the function, isolated so the rest is ordinary
straight-line reasoning. -/
theorem charge_state_gas_add_sat_call
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (sgl gl : Word)
    (hsgl : l "sgl" = some (PanValue.word sgl))
    (hgl : l "gl" = some (PanValue.word gl))
    (hlookup : lookupPanFunction "add_sat" functions = some (["a", "b"], addSatBody))
    (hlimitMax : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 18446744073709551615)) = true)
    (hlimitSum : panValuePayloadWithinLimit structs
      (PanValue.word (sgl + gl)) = true)
    (hparamsValid : panValueParametersValid structs c "add_sat"
      [PanValue.word sgl, PanValue.word gl] = true)
    (hretValid : (panValueReturnValid structs c "add_sat"
        [PanValue.word (addSatOf sgl gl)] &&
      panValueValuesWithinLimit structs [PanValue.word (addSatOf sgl gl)]) = true) :
    ∃ steps, evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 5 l g m f none "add_sat"
      [Exp.var VarKind.local "sgl", Exp.var VarKind.local "gl"]
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned (fun _ => none) g m f
          [PanValue.word (addSatOf sgl gl)], steps) := by
  have hcallee := add_sat_binds sgl gl
  have ha : updatePanValueMap (updatePanValueMap (fun _ => none) "a" (PanValue.word sgl))
      "b" (PanValue.word gl) "a" = some (PanValue.word sgl) := by
    simp [updatePanValueMap]
  have hb : updatePanValueMap (updatePanValueMap (fun _ => none) "a" (PanValue.word sgl))
      "b" (PanValue.word gl) "b" = some (PanValue.word gl) := by
    simp [updatePanValueMap]
  obtain ⟨cl, bsteps, hbody⟩ := add_sat_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord c mh _ g m f sgl gl ha hb hlimitMax hlimitSum
  exact ⟨_, StepCalculus.callSteps_runs_returned_none context primitive handler structs
    functions baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    "add_sat" _ l g m f _ _ ["a", "b"] addSatBody _ 4 _ cl g m f _
    (evalCounted_args_two_locals structs l g m baseAddress topAddress bytesInWord
      "sgl" "gl" sgl gl hsgl hgl)
    hlookup hparamsValid hcallee hbody hretValid⟩


/-- **What `charge_state_gas`'s spill body runs to**, from the point where
`tot`, `sgl`, `gl` and `amount` are all bound: empty the reservoir, take the
remainder out of `EV_GAS_LEFT`, and record it in `EV_STATE_GAS_SPILLED`.

The three stores are sequential and the last one *reads* `EV_STATE_GAS_SPILLED`
after the first two have run, which is why the two disjointness hypotheses are
needed and why they are only about `ev + 192`. -/
theorem charge_state_gas_spill_stores
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e sgl gl amount spilled : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hgl : l "gl" = some (PanValue.word gl))
    (hsgl : l "sgl" = some (PanValue.word sgl))
    (hamount : l "amount" = some (PanValue.word amount))
    (hspilled : m (e + BitVec.ofNat 64 192) = some (PanValue.word spilled))
    (hne72 : ((e + BitVec.ofNat 64 192) == (e + BitVec.ofNat 64 72)) = false)
    (hne64 : ((e + BitVec.ofNat 64 192) == (e + BitVec.ofNat 64 64)) = false)
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 5 l g m f
      chargeStateGasSpillStores
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' g
          (chargeStateGasSpillMemory m e sgl gl amount spilled) f
          [PanValue.word (BitVec.ofNat 64 0)], steps) := by
  -- `rem := amount - sgl`
  have hrem : evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.sub [Exp.var VarKind.local "amount", Exp.var VarKind.local "sgl"])
      (some guestMemoryAccess)
      = some (PanValue.word (amount - sgl),
          panValueExpStepCost (Exp.op BinOp.sub
            [Exp.var VarKind.local "amount", Exp.var VarKind.local "sgl"] : Exp Word)) := by
    rw [evalPanValueExpCounted]
    rw [eval_op2 structs l g m baseAddress topAddress bytesInWord BinOp.sub _ _ amount sgl _
      (by rw [eval_var_local]; exact hamount) (by rw [eval_var_local]; exact hsgl)
      (wordOp_sub amount sgl)]
    rfl
  -- locals with `rem` bound
  have hgl' : updatePanValueMap l "rem" (PanValue.word (amount - sgl)) "gl"
      = some (PanValue.word gl) := by simp [updatePanValueMap, hgl]
  have hrem' : updatePanValueMap l "rem" (PanValue.word (amount - sgl)) "rem"
      = some (PanValue.word (amount - sgl)) := by simp [updatePanValueMap]
  -- store 1: ev + 72 := 0
  have haddr72 : evalPanValueExp structs (updatePanValueMap l "rem" (PanValue.word (amount - sgl)))
      g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 72)])
      (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 72)) :=
    eval_global_add_const structs _ g m baseAddress topAddress bytesInWord "ev" e _ hev
  have hs1 := store_runs structs _ g m baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr72
    (by rw [eval_const] : evalPanValueExp structs
      (updatePanValueMap l "rem" (PanValue.word (amount - sgl))) g m baseAddress topAddress
      bytesInWord (Exp.const (BitVec.ofNat 64 0)) (some guestMemoryAccess)
      = some (PanValue.word (BitVec.ofNat 64 0)))
  -- store 2: ev + 64 := gl - rem, in the memory the first store left
  have haddr64 : evalPanValueExp structs (updatePanValueMap l "rem" (PanValue.word (amount - sgl)))
      g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)])
      (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 64)) :=
    eval_global_add_const structs _ g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) baseAddress topAddress bytesInWord "ev" e _ hev
  have hval64 : evalPanValueExp structs (updatePanValueMap l "rem" (PanValue.word (amount - sgl)))
      g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) baseAddress topAddress bytesInWord
      (Exp.op BinOp.sub [Exp.var VarKind.local "gl", Exp.var VarKind.local "rem"])
      (some guestMemoryAccess) = some (PanValue.word (gl - (amount - sgl))) := by
    refine eval_op2 structs _ g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) baseAddress topAddress bytesInWord BinOp.sub _ _ gl
      (amount - sgl) _ ?_ ?_ (wordOp_sub gl (amount - sgl))
    · rw [eval_var_local]; exact hgl'
    · rw [eval_var_local]; exact hrem'
  have hs2 := store_runs structs _ g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr64 hval64
  -- store 3: ev + 192 := (load ev + 192) + rem, reading past the first two
  have hsp2 : (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) (e + BitVec.ofNat 64 192) = some (PanValue.word spilled) := by
    simp only [hne64, hne72]
    exact hspilled
  have haddr192 : evalPanValueExp structs (updatePanValueMap l "rem" (PanValue.word (amount - sgl)))
      g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 192)])
      (some guestMemoryAccess) = some (PanValue.word (e + BitVec.ofNat 64 192)) :=
    eval_global_add_const structs _ g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) baseAddress topAddress bytesInWord "ev" e _ hev
  have hload192 : evalPanValueExp structs (updatePanValueMap l "rem" (PanValue.word (amount - sgl)))
      g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) baseAddress topAddress bytesInWord
      (Exp.load Shape.one (Exp.op BinOp.add
        [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 192)]))
      (some guestMemoryAccess) = some (PanValue.word spilled) :=
    eval_load_global_add structs _ g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) baseAddress topAddress bytesInWord "ev" e _ spilled
      hev hsp2
  have hval192 : evalPanValueExp structs (updatePanValueMap l "rem" (PanValue.word (amount - sgl)))
      g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.load Shape.one (Exp.op BinOp.add
          [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 192)]),
        Exp.var VarKind.local "rem"])
      (some guestMemoryAccess) = some (PanValue.word (spilled + (amount - sgl))) := by
    refine eval_op2 structs _ g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) baseAddress topAddress bytesInWord BinOp.add _ _ spilled
      (amount - sgl) _ hload192 ?_ (wordOp_add spilled (amount - sgl))
    rw [eval_var_local]; exact hrem'
  have hs3 := store_runs structs _ g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr192 hval192
  have hret := StepCalculus.return_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (Exp.const (BitVec.ofNat 64 0))
    (updatePanValueMap l "rem" (PanValue.word (amount - sgl))) g
    (chargeStateGasSpillMemory m e sgl gl amount spilled) f _ _ 0
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimit
  -- chain them: innermost first
  have hseq3 := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) f
    _ g (chargeStateGasSpillMemory m e sgl gl amount spilled) f 1 _ _ _ hs3 hret
  have hs2' := StepCalculus.progMono context primitive handler structs functions
    baseAddress topAddress bytesInWord 1 _ g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) f _ (some guestMemoryAccess) c mh 2 _
    (by omega) hs2
  have hseq2 := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) f
    _ g (fun cur => if cur == e + BitVec.ofNat 64 64 then some (PanValue.word (gl - (amount - sgl))) else (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) cur) f 2 _ _ _ hs2' hseq3
  have hs1' := StepCalculus.progMono context primitive handler structs functions
    baseAddress topAddress bytesInWord 1 _ g m f _ (some guestMemoryAccess) c mh 3 _
    (by omega) hs1
  have hseq1 := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g m f
    _ g (fun cur => if cur == e + BitVec.ofNat 64 72 then some (PanValue.word (BitVec.ofNat 64 0)) else m cur) f 3 _ _ _ hs1' hseq2
  have hfinal := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "rem" Shape.one _ _
    l g m f (PanValue.word (amount - sgl)) _ 4 _ _ hrem
    (word_shape_matches structs (amount - sgl)) hseq1
  exact ⟨_, _, hfinal⟩
/-- **What `charge_state_gas` runs to when the reservoir is short but the two
counters together cover the charge.** The spill path, end to end from the
committed AST: `add_sat` is called, the `tot >=+ amount` test passes, the
reservoir is emptied, and the remainder is taken from `EV_GAS_LEFT` and
recorded in `EV_STATE_GAS_SPILLED`.

`hshort` puts us on this path (the reservoir test fails) and `hcovers` takes
the paying branch of the spill test. Both are the guest's own comparisons,
restated on `Nat`. -/
theorem charge_state_gas_runs_spill
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e sgl gl amount spilled : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hsglM : m (e + BitVec.ofNat 64 72) = some (PanValue.word sgl))
    (hglM : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hspilled : m (e + BitVec.ofNat 64 192) = some (PanValue.word spilled))
    (hamount : l "amount" = some (PanValue.word amount))
    (hshort : sgl.toNat < amount.toNat)
    (hcovers : amount.toNat ≤ (addSatOf sgl gl).toNat)
    (hne72 : ((e + BitVec.ofNat 64 192) == (e + BitVec.ofNat 64 72)) = false)
    (hne64 : ((e + BitVec.ofNat 64 192) == (e + BitVec.ofNat 64 64)) = false)
    (hlookup : lookupPanFunction "add_sat" functions = some (["a", "b"], addSatBody))
    (hlimitMax : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 18446744073709551615)) = true)
    (hlimitSum : panValuePayloadWithinLimit structs (PanValue.word (sgl + gl)) = true)
    (hlimit0 : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true)
    (hparamsValid : panValueParametersValid structs c "add_sat"
      [PanValue.word sgl, PanValue.word gl] = true)
    (hretValid : (panValueReturnValid structs c "add_sat"
        [PanValue.word (addSatOf sgl gl)] &&
      panValueValuesWithinLimit structs [PanValue.word (addSatOf sgl gl)]) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 11 l g m f chargeStateGasBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' g
          (chargeStateGasSpillMemory m e sgl gl amount spilled) f
          [PanValue.word (BitVec.ofNat 64 0)], steps) := by
  have hL2sgl : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "sgl" = some (PanValue.word sgl) := by simp [updatePanValueMap]
  have hL2gl : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "gl" = some (PanValue.word gl) := by simp [updatePanValueMap]
  have hL2amount : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "amount" = some (PanValue.word amount) := by
    simp [updatePanValueMap, hamount]
  obtain ⟨csteps, hcall⟩ := charge_state_gas_add_sat_call context primitive handler structs
    functions baseAddress topAddress bytesInWord c mh _ g m f sgl gl hL2sgl hL2gl
    hlookup hlimitMax hlimitSum hparamsValid hretValid
  have hcall' := StepCalculus.callMono context primitive handler structs functions
    baseAddress topAddress bytesInWord 5 _ g m f none "add_sat" _
    (some guestMemoryAccess) c mh 7 _ (by omega) hcall
  have hL3tot : updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl"
      (PanValue.word sgl)) "gl" (PanValue.word gl)) "tot"
      (PanValue.word (addSatOf sgl gl)) "tot" = some (PanValue.word (addSatOf sgl gl)) := by
    simp [updatePanValueMap]
  have hL3amount : updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl"
      (PanValue.word sgl)) "gl" (PanValue.word gl)) "tot"
      (PanValue.word (addSatOf sgl gl)) "amount" = some (PanValue.word amount) := by
    simp [updatePanValueMap, hamount]
  have hL3gl : updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl"
      (PanValue.word sgl)) "gl" (PanValue.word gl)) "tot"
      (PanValue.word (addSatOf sgl gl)) "gl" = some (PanValue.word gl) := by
    simp [updatePanValueMap]
  have hL3sgl : updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl"
      (PanValue.word sgl)) "gl" (PanValue.word gl)) "tot"
      (PanValue.word (addSatOf sgl gl)) "sgl" = some (PanValue.word sgl) := by
    simp [updatePanValueMap]
  obtain ⟨l3, ssteps, hstores⟩ := charge_state_gas_spill_stores context primitive handler
    structs functions baseAddress topAddress bytesInWord c mh _ g m f e sgl gl amount
    spilled hev hL3gl hL3sgl hL3amount hspilled hne72 hne64 hlimit0
  have hzs : ((RiscV.panRiscVCmp Cmp.notLower (addSatOf sgl gl) amount) != 0) = true :=
    cmp_notLower_true_of_le hcovers
  have hconds := evalCounted_cmp_locals structs _ g m baseAddress topAddress bytesInWord
    Cmp.notLower "tot" "amount" (addSatOf sgl gl) amount hL3tot hL3amount
  have hites := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := chargeStateGasSpillStores) (elseBranch := Prog.skip)
    _ g m f _ _ 5 _ _ hconds (by rw [if_pos hzs]; exact hstores)
  have hbody := StepCalculus.seq_runs_returned context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (second := Prog.seq (Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4)))
      (Prog.return (Exp.const (BitVec.ofNat 64 0))))
    _ g m f _ g (chargeStateGasSpillMemory m e sgl gl amount spilled) f 6 _ _ hites
  have hdecCall := StepCalculus.decCall_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "tot" Shape.one
    "add_sat" _ _ _ g m f 7 _ _ _ g m f _ _ hcall'
    (word_shape_matches structs (addSatOf sgl gl)) hbody
  have hzr : ((RiscV.panRiscVCmp Cmp.notLower sgl amount) != 0) = false :=
    cmp_notLower_false_of_lt hshort
  have hcondr := evalCounted_cmp_locals structs _ g m baseAddress topAddress bytesInWord
    Cmp.notLower "sgl" "amount" sgl amount hL2sgl hL2amount
  have hskip := StepCalculus.skip_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl)) g m f 6
  have hiter := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := chargeStateGasReservoir) (elseBranch := Prog.skip)
    _ g m f _ _ 7 _ _ hcondr (by rw [if_neg (by rw [hzr]; simp)]; exact hskip)
  have houter := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (second := chargeStateGasSpill) _ g m f _ g m f 8 _ _ _ hiter hdecCall
  have hdecgl := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "gl" Shape.one _ _
    _ g m f (PanValue.word gl) _ 9 _ _
    (evalCounted_load_global_add structs _ g m baseAddress topAddress bytesInWord "ev" e
      (BitVec.ofNat 64 64) gl hev hglM)
    (word_shape_matches structs gl) houter
  have hfinal := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "sgl" Shape.one _ _
    l g m f (PanValue.word sgl) _ 10 _ _
    (evalCounted_load_global_add structs l g m baseAddress topAddress bytesInWord "ev" e
      (BitVec.ofNat 64 72) sgl hev hsglM)
    (word_shape_matches structs sgl) hdecgl
  rw [chargeStateGasBody_eq]
  exact ⟨_, _, hfinal⟩

/-- `add_sat` never exceeds the true sum — the other half of `add_sat_ge`.
Together they say it *is* `min (a + b) (2^64 - 1)` on `Nat`. This direction is
what turns `charge_state_gas`'s `tot >=+ amount` test into the arithmetic fact
the measure needs. -/
theorem addSatOf_le_sum (a b : Word) :
    (addSatOf a b).toNat ≤ a.toNat + b.toNat := by
  by_cases hc : (a + b) < a
  · have hsat : 2 ^ 64 ≤ a.toNat + b.toNat := (add_sat_saturates a b).mp hc
    have : (addSatOf a b).toNat = 2 ^ 64 - 1 := by
      simp only [addSatOf, if_pos hc]; decide
    omega
  · have hno : a.toNat + b.toNat < 2 ^ 64 := by
      cases Nat.lt_or_ge (a.toNat + b.toNat) (2 ^ 64) with
      | inl h => exact h
      | inr h => exact absurd ((add_sat_saturates a b).mpr h) hc
    have : (addSatOf a b).toNat = a.toNat + b.toNat := by
      simp only [addSatOf, if_neg hc]; exact add_no_carry hno
    omega

/-- **The spill charge moves the measure down.** Reading the two counters back
out of the memory the spill path leaves: the reservoir is empty and
`EV_GAS_LEFT` is short by `amount - sgl`, so the sum has fallen by exactly
`amount`.

`hcovers` is the guest's `tot >=+ amount`; `addSatOf_le_sum` is what turns it
into the no-borrow condition `state_gas_sum_decreases_spill` needs. -/
theorem charge_state_gas_decreases_sum_spill
    (m : Memory) (e sgl gl amount spilled : Word)
    (hshort : sgl.toNat < amount.toNat)
    (hcovers : amount.toNat ≤ (addSatOf sgl gl).toNat)
    (hpos : 1 ≤ amount.toNat)
    (h72_192 : ((e + BitVec.ofNat 64 72) == (e + BitVec.ofNat 64 192)) = false)
    (h72_64 : ((e + BitVec.ofNat 64 72) == (e + BitVec.ofNat 64 64)) = false)
    (h64_192 : ((e + BitVec.ofNat 64 64) == (e + BitVec.ofNat 64 192)) = false) :
    ∃ sgl' gl',
      chargeStateGasSpillMemory m e sgl gl amount spilled (e + BitVec.ofNat 64 72)
          = some (PanValue.word sgl') ∧
      chargeStateGasSpillMemory m e sgl gl amount spilled (e + BitVec.ofNat 64 64)
          = some (PanValue.word gl') ∧
      sgl'.toNat + gl'.toNat < sgl.toNat + gl.toNat := by
  have htot : amount.toNat ≤ sgl.toNat + gl.toNat :=
    Nat.le_trans hcovers (addSatOf_le_sum sgl gl)
  refine ⟨BitVec.ofNat 64 0, gl - (amount - sgl), ?_, ?_,
    state_gas_sum_decreases_spill hshort htot hpos⟩
  · simp [chargeStateGasSpillMemory, h72_192, h72_64]
  · simp [chargeStateGasSpillMemory, h64_192]

end

/-!
## The other half of the census claim: ending the frame

The census says every opcode handler either charges at least one gas **or ends
its frame**. The charging half is above. This is the other one, for the two
charge functions themselves: when the gas is not there, they raise
`EvmErr E_OUT_OF_GAS`.

Nothing inside either function catches it, so the raise leaves the function and
the frame is over — the caller gets a `.raised`, not a state it can continue
from. That is what makes "or ends its frame" a real alternative for the measure
rather than a gap in it: the run does not go on to execute another opcode from
a gas counter that did not move.

Between these and the paying paths, `charge_gas` and `charge_state_gas` are now
total on the cases the measure cares about — every reachable path through
either one is either a strict decrease or a frame end.
-/

/-- **What `charge_gas` runs to when the charge does not fit**: it raises
`EvmErr E_OUT_OF_GAS` and leaves memory untouched.

This is the other half of the census claim — "charges at least one gas **or
ends its frame**". Nothing catches `EvmErr` inside `charge_gas`, so the raise
propagates out of the function and the frame is over; the caller sees a
`.raised`, not a state it can carry on from. -/
theorem charge_gas_runs_raised
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e gl amount : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hgas : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hamount : l "amount" = some (PanValue.word amount))
    (hshort : gl.toNat < amount.toNat)
    (hraiseValid : (panValueExceptionValid structs c "EvmErr"
        (PanValue.word (BitVec.ofNat 64 4)) &&
      panValuePayloadWithinLimit structs (PanValue.word (BitVec.ofNat 64 4))) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 4 l g m f chargeGasBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.raised l' g m f "EvmErr"
          (PanValue.word (BitVec.ofNat 64 4)), steps) := by
  have hgl' : updatePanValueMap l "gl" (PanValue.word gl) "gl"
      = some (PanValue.word gl) := by simp [updatePanValueMap]
  have hamount' : updatePanValueMap l "gl" (PanValue.word gl) "amount"
      = some (PanValue.word amount) := by simp [updatePanValueMap, hamount]
  have hcond := evalCounted_cmp_locals structs (updatePanValueMap l "gl" (PanValue.word gl))
    g m baseAddress topAddress bytesInWord Cmp.lower "gl" "amount" gl amount hgl' hamount'
  have hz : ((RiscV.panRiscVCmp Cmp.lower gl amount) != 0) = true :=
    cmp_lower_true_iff.mpr (by simp only [BitVec.lt_def]; omega)
  have hraise := StepCalculus.raise_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    "EvmErr" (Exp.const (BitVec.ofNat 64 4))
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f _ _ 0
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hraiseValid
  have hite := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4)))
    (elseBranch := Prog.skip)
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f _ _ 1 _ _ hcond
    (by rw [if_pos hz]; exact hraise)
  have hseq := StepCalculus.seq_runs_raised context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (second := chargeGasTail)
    (updatePanValueMap l "gl" (PanValue.word gl)) g m f _ g m f 2 _ _ _ hite
  have hfinal := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "gl" Shape.one _ _
    l g m f (PanValue.word gl) _ 3 _ _
    (charge_gas_load_of_state structs l g m baseAddress topAddress bytesInWord e gl hev hgas)
    (word_shape_matches structs gl) hseq
  rw [chargeGasBody_eq]
  exact ⟨_, _, hfinal⟩

/-- **What `charge_state_gas` runs to when neither counter can cover the
charge**: `add_sat` says the two together are short, so the `ite` falls
through and the `raise` below it fires.

The `EvmErr` here is the same `E_OUT_OF_GAS`, and nothing in `charge_state_gas`
catches it either — so this is the "ends its frame" half for the state-gas
path, exactly as `charge_gas_runs_raised` is for the ordinary one. -/
theorem charge_state_gas_runs_raised
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e sgl gl amount : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hsglM : m (e + BitVec.ofNat 64 72) = some (PanValue.word sgl))
    (hglM : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hamount : l "amount" = some (PanValue.word amount))
    (hshort : sgl.toNat < amount.toNat)
    (hshortTot : (addSatOf sgl gl).toNat < amount.toNat)
    (hlookup : lookupPanFunction "add_sat" functions = some (["a", "b"], addSatBody))
    (hlimitMax : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 18446744073709551615)) = true)
    (hlimitSum : panValuePayloadWithinLimit structs (PanValue.word (sgl + gl)) = true)
    (hparamsValid : panValueParametersValid structs c "add_sat"
      [PanValue.word sgl, PanValue.word gl] = true)
    (hretValid : (panValueReturnValid structs c "add_sat"
        [PanValue.word (addSatOf sgl gl)] &&
      panValueValuesWithinLimit structs [PanValue.word (addSatOf sgl gl)]) = true)
    (hraiseValid : (panValueExceptionValid structs c "EvmErr"
        (PanValue.word (BitVec.ofNat 64 4)) &&
      panValuePayloadWithinLimit structs (PanValue.word (BitVec.ofNat 64 4))) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 9 l g m f chargeStateGasBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.raised l' g m f "EvmErr"
          (PanValue.word (BitVec.ofNat 64 4)), steps) := by
  have hL2sgl : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "sgl" = some (PanValue.word sgl) := by simp [updatePanValueMap]
  have hL2gl : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "gl" = some (PanValue.word gl) := by simp [updatePanValueMap]
  have hL2amount : updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl) "amount" = some (PanValue.word amount) := by
    simp [updatePanValueMap, hamount]
  obtain ⟨csteps, hcall⟩ := charge_state_gas_add_sat_call context primitive handler structs
    functions baseAddress topAddress bytesInWord c mh _ g m f sgl gl hL2sgl hL2gl
    hlookup hlimitMax hlimitSum hparamsValid hretValid
  have hL3tot : updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl"
      (PanValue.word sgl)) "gl" (PanValue.word gl)) "tot"
      (PanValue.word (addSatOf sgl gl)) "tot" = some (PanValue.word (addSatOf sgl gl)) := by
    simp [updatePanValueMap]
  have hL3amount : updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl"
      (PanValue.word sgl)) "gl" (PanValue.word gl)) "tot"
      (PanValue.word (addSatOf sgl gl)) "amount" = some (PanValue.word amount) := by
    simp [updatePanValueMap, hamount]
  -- the spill test fails too
  have hzs : ((RiscV.panRiscVCmp Cmp.notLower (addSatOf sgl gl) amount) != 0) = false :=
    cmp_notLower_false_of_lt hshortTot
  have hconds := evalCounted_cmp_locals structs _ g m baseAddress topAddress bytesInWord
    Cmp.notLower "tot" "amount" (addSatOf sgl gl) amount hL3tot hL3amount
  have hskips := StepCalculus.skip_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl))
      "gl" (PanValue.word gl)) "tot" (PanValue.word (addSatOf sgl gl))) g m f 0
  have hites := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := chargeStateGasSpillStores) (elseBranch := Prog.skip)
    _ g m f _ _ 1 _ _ hconds (by rw [if_neg (by rw [hzs]; simp)]; exact hskips)
  -- the raise below it
  have hraise := StepCalculus.raise_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    "EvmErr" (Exp.const (BitVec.ofNat 64 4))
    (updatePanValueMap (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl))
      "gl" (PanValue.word gl)) "tot" (PanValue.word (addSatOf sgl gl))) g m f _ _ 0
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hraiseValid
  have htail := StepCalculus.seq_runs_raised context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (second := Prog.return (Exp.const (BitVec.ofNat 64 0)))
    _ g m f _ g m f 1 _ _ _ hraise
  have hbody := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g m f
    _ g m f 2 _ _ _ hites htail
  have hbody' := StepCalculus.progMono context primitive handler structs functions
    baseAddress topAddress bytesInWord 3 _ g m f _ (some guestMemoryAccess) c mh 5 _
    (by omega) hbody
  have hdecCall := StepCalculus.decCall_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "tot" Shape.one
    "add_sat" _ _ _ g m f 5 _ _ _ g m f _ _ hcall
    (word_shape_matches structs (addSatOf sgl gl)) hbody'
  -- the reservoir test fails, so the outer `ite` falls through
  have hzr : ((RiscV.panRiscVCmp Cmp.notLower sgl amount) != 0) = false :=
    cmp_notLower_false_of_lt hshort
  have hcondr := evalCounted_cmp_locals structs _ g m baseAddress topAddress bytesInWord
    Cmp.notLower "sgl" "amount" sgl amount hL2sgl hL2amount
  have hskipr := StepCalculus.skip_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (updatePanValueMap (updatePanValueMap l "sgl" (PanValue.word sgl)) "gl"
      (PanValue.word gl)) g m f 4
  have hiter := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := chargeStateGasReservoir) (elseBranch := Prog.skip)
    _ g m f _ _ 5 _ _ hcondr (by rw [if_neg (by rw [hzr]; simp)]; exact hskipr)
  have houter := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (second := chargeStateGasSpill) _ g m f _ g m f 6 _ _ _ hiter hdecCall
  have hdecgl := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "gl" Shape.one _ _
    _ g m f (PanValue.word gl) _ 7 _ _
    (evalCounted_load_global_add structs _ g m baseAddress topAddress bytesInWord "ev" e
      (BitVec.ofNat 64 64) gl hev hglM)
    (word_shape_matches structs gl) houter
  have hfinal := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "sgl" Shape.one _ _
    l g m f (PanValue.word sgl) _ 8 _ _
    (evalCounted_load_global_add structs l g m baseAddress topAddress bytesInWord "ev" e
      (BitVec.ofNat 64 72) sgl hev hsglM)
    (word_shape_matches structs sgl) hdecgl
  rw [chargeStateGasBody_eq]
  exact ⟨_, _, hfinal⟩

/-- The body of `min`, verbatim from `Guest.guestAst`. -/
def minBody : Prog Word :=
  match Guest.guestFn_min with
  | .function info => info.body
  | _ => Prog.skip

theorem minBody_eq : minBody =
    Prog.seq
      (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "a") (Exp.var VarKind.local "b"))
        (Prog.return (Exp.var VarKind.local "a"))
        Prog.skip)
      (Prog.return (Exp.var VarKind.local "b")) := by
  rfl

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **What `min`'s body runs to.** The second callee, and the simplest one —
no `dec`, just the comparison and two returns. -/
theorem min_runs
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (a b : Word)
    (ha : l "a" = some (PanValue.word a))
    (hb : l "b" = some (PanValue.word b))
    (hlimitA : panValuePayloadWithinLimit structs (PanValue.word a) = true)
    (hlimitB : panValuePayloadWithinLimit structs (PanValue.word b) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 3 l g m f minBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' g m f
          [PanValue.word (minOf a b)], steps) := by
  have hcond := evalCounted_cmp_locals structs l g m baseAddress topAddress bytesInWord
    Cmp.lower "a" "b" a b ha hb
  by_cases hz : ((RiscV.panRiscVCmp Cmp.lower a b) != 0) = true
  · have hreta := StepCalculus.return_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
      (Exp.var VarKind.local "a") l g m f _ _ 0
      (by rw [evalPanValueExpCounted, eval_var_local, ha]; rfl) hlimitA
    have hite := StepCalculus.ite_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (thenBranch := Prog.return (Exp.var VarKind.local "a")) (elseBranch := Prog.skip)
      l g m f _ _ 1 _ _ hcond (by rw [if_pos hz]; exact hreta)
    have hfinal := StepCalculus.seq_runs_returned context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (second := Prog.return (Exp.var VarKind.local "b")) l g m f _ g m f 2 _ _ hite
    have hmin : minOf a b = a := by
      simp only [minOf, if_pos (cmp_lower_true_iff.mp hz)]
    rw [minBody_eq, hmin]
    exact ⟨_, _, hfinal⟩
  · have hskip := StepCalculus.skip_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh l g m f 0
    have hite := StepCalculus.ite_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
      (thenBranch := Prog.return (Exp.var VarKind.local "a")) (elseBranch := Prog.skip)
      l g m f _ _ 1 _ _ hcond (by rw [if_neg hz]; exact hskip)
    have hretb := StepCalculus.return_runs context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
      (Exp.var VarKind.local "b") l g m f _ _ 1
      (by rw [evalPanValueExpCounted, eval_var_local, hb]; rfl) hlimitB
    have hfinal := StepCalculus.seq_runs_normal context primitive handler structs functions
      baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ l g m f
      l g m f 2 _ _ _ hite hretb
    have hmin : minOf a b = b := by
      simp only [minOf, if_neg (fun hlt => hz (cmp_lower_true_iff.mpr hlt))]
    rw [minBody_eq, hmin]
    exact ⟨_, _, hfinal⟩

end

/-- The body of `credit_state_gas_refund`, verbatim from `Guest.guestAst`. -/
def creditStateGasBody : Prog Word :=
  match Guest.guestFn_credit_state_gas_refund with
  | .function info => info.body
  | _ => Prog.skip

/-- The memory `credit_state_gas_refund` leaves: `from_gl` of the refund goes
back to `EV_GAS_LEFT` and comes off `EV_STATE_GAS_SPILLED`, and the remainder
goes to the reservoir. -/
def creditStateGasMemory (m : Memory) (e gl sgl amount spilled : Word) : Memory :=
  fun current =>
    if current == e + BitVec.ofNat 64 72 then
      some (PanValue.word (sgl + (amount - minOf amount spilled)))
    else if current == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled - minOf amount spilled))
    else if current == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled))
    else m current

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **What `credit_state_gas_refund` runs to.** The counterpart to the charge
functions, and the one that moves the measure the *wrong* way — see
`credit_state_gas_refund_increases_sum`. Pinning down the state it leaves is
what the conservation argument will have to reason about.

Three stores, and the last reads `EV_STATE_GAS_LEFT` after the first two have
run, hence the two disjointness hypotheses. -/
theorem credit_state_gas_refund_runs
    (l g : VarName → Option (PanValue Word)) (m : Memory) (f : FfiState HostMemory)
    (e gl sgl amount spilled : Word)
    (hev : g "ev" = some (PanValue.word e))
    (hspilled : m (e + BitVec.ofNat 64 192) = some (PanValue.word spilled))
    (hglM : m (e + BitVec.ofNat 64 64) = some (PanValue.word gl))
    (hsglM : m (e + BitVec.ofNat 64 72) = some (PanValue.word sgl))
    (hamount : l "amount" = some (PanValue.word amount))
    (h72_192 : ((e + BitVec.ofNat 64 72) == (e + BitVec.ofNat 64 192)) = false)
    (h72_64 : ((e + BitVec.ofNat 64 72) == (e + BitVec.ofNat 64 64)) = false)
    (hlookup : lookupPanFunction "min" functions = some (["a", "b"], minBody))
    (hlimitAmount : panValuePayloadWithinLimit structs (PanValue.word amount) = true)
    (hlimitSpilled : panValuePayloadWithinLimit structs (PanValue.word spilled) = true)
    (hlimit0 : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 0)) = true)
    (hparamsValid : panValueParametersValid structs c "min"
      [PanValue.word amount, PanValue.word spilled] = true)
    (hretValid : (panValueReturnValid structs c "min"
        [PanValue.word (minOf amount spilled)] &&
      panValueValuesWithinLimit structs [PanValue.word (minOf amount spilled)]) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 6 l g m f creditStateGasBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' g
          (creditStateGasMemory m e gl sgl amount spilled) f
          [PanValue.word (BitVec.ofNat 64 0)], steps) := by
  -- locals after `dec spilled`
  have hL1spilled : updatePanValueMap l "spilled" (PanValue.word spilled) "spilled"
      = some (PanValue.word spilled) := by simp [updatePanValueMap]
  have hL1amount : updatePanValueMap l "spilled" (PanValue.word spilled) "amount"
      = some (PanValue.word amount) := by simp [updatePanValueMap, hamount]
  -- the `min` call
  have hbindMin := add_sat_binds amount spilled
  have hminA : updatePanValueMap (updatePanValueMap (fun _ => none) "a"
      (PanValue.word amount)) "b" (PanValue.word spilled) "a"
      = some (PanValue.word amount) := by simp [updatePanValueMap]
  have hminB : updatePanValueMap (updatePanValueMap (fun _ => none) "a"
      (PanValue.word amount)) "b" (PanValue.word spilled) "b"
      = some (PanValue.word spilled) := by simp [updatePanValueMap]
  obtain ⟨cl, bsteps, hminBody⟩ := min_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord c mh _ g m f amount spilled hminA hminB
    hlimitAmount hlimitSpilled
  have hcall := StepCalculus.callSteps_runs_returned_none context primitive handler structs
    functions baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    "min" _ _ g m f _ _ ["a", "b"] minBody _ 3 _ cl g m f _
    (evalCounted_args_two_locals structs _ g m baseAddress topAddress bytesInWord
      "amount" "spilled" amount spilled hL1amount hL1spilled)
    hlookup hparamsValid hbindMin hminBody hretValid
  -- locals with `from_gl` bound
  have hL2 : ∀ n v, updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled))
      "from_gl" (PanValue.word (minOf amount spilled)) n = v →
      updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled))
      "from_gl" (PanValue.word (minOf amount spilled)) n = v := fun _ _ h => h
  have hFfrom : updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled))
      "from_gl" (PanValue.word (minOf amount spilled)) "from_gl"
      = some (PanValue.word (minOf amount spilled)) := by simp [updatePanValueMap]
  have hFspilled : updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled))
      "from_gl" (PanValue.word (minOf amount spilled)) "spilled"
      = some (PanValue.word spilled) := by simp [updatePanValueMap]
  have hFamount : updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled))
      "from_gl" (PanValue.word (minOf amount spilled)) "amount"
      = some (PanValue.word amount) := by simp [updatePanValueMap, hamount]
  -- store 1: ev + 64 := (lds ev + 64) + from_gl
  have haddr64 := eval_global_add_const structs
    (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
      (PanValue.word (minOf amount spilled))) g m baseAddress topAddress bytesInWord
    "ev" e (BitVec.ofNat 64 64) hev
  have hload64 := eval_load_global_add structs
    (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
      (PanValue.word (minOf amount spilled))) g m baseAddress topAddress bytesInWord
    "ev" e (BitVec.ofNat 64 64) gl hev hglM
  have hval64 : evalPanValueExp structs
      (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
        (PanValue.word (minOf amount spilled))) g m baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.load Shape.one (Exp.op BinOp.add
          [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 64)]),
        Exp.var VarKind.local "from_gl"])
      (some guestMemoryAccess) = some (PanValue.word (gl + minOf amount spilled)) := by
    refine eval_op2 structs _ g m baseAddress topAddress bytesInWord BinOp.add _ _ gl
      (minOf amount spilled) _ hload64 ?_ (wordOp_add gl (minOf amount spilled))
    rw [eval_var_local]; exact hFfrom
  have hs1 := store_runs structs _ g m baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr64 hval64
  -- store 2: ev + 192 := spilled - from_gl, in the memory the first store left
  have haddr192 := eval_global_add_const structs
    (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
      (PanValue.word (minOf amount spilled))) g
    (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur)
    baseAddress topAddress bytesInWord "ev" e (BitVec.ofNat 64 192) hev
  have hval192 : evalPanValueExp structs
      (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
        (PanValue.word (minOf amount spilled))) g
      (fun cur => if cur == e + BitVec.ofNat 64 64 then
        some (PanValue.word (gl + minOf amount spilled)) else m cur)
      baseAddress topAddress bytesInWord
      (Exp.op BinOp.sub [Exp.var VarKind.local "spilled", Exp.var VarKind.local "from_gl"])
      (some guestMemoryAccess)
      = some (PanValue.word (spilled - minOf amount spilled)) := by
    refine eval_op2 structs _ g _ baseAddress topAddress bytesInWord BinOp.sub _ _ spilled
      (minOf amount spilled) _ ?_ ?_ (wordOp_sub spilled (minOf amount spilled))
    · rw [eval_var_local]; exact hFspilled
    · rw [eval_var_local]; exact hFfrom
  have hs2 := store_runs structs _ g
    (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur)
    baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr192 hval192
  -- store 3: ev + 72 := (load ev + 72) + (amount - from_gl), reading past the first two
  have hsgl2 : (fun cur => if cur == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled - minOf amount spilled))
    else (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) cur)
      (e + BitVec.ofNat 64 72) = some (PanValue.word sgl) := by
    simp only [h72_192, h72_64]
    exact hsglM
  have haddr72 := eval_global_add_const structs
    (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
      (PanValue.word (minOf amount spilled))) g
    (fun cur => if cur == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled - minOf amount spilled))
    else (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) cur)
    baseAddress topAddress bytesInWord "ev" e (BitVec.ofNat 64 72) hev
  have hload72 := eval_load_global_add structs
    (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
      (PanValue.word (minOf amount spilled))) g
    (fun cur => if cur == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled - minOf amount spilled))
    else (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) cur)
    baseAddress topAddress bytesInWord "ev" e (BitVec.ofNat 64 72) sgl hev hsgl2
  have hval72 : evalPanValueExp structs
      (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
        (PanValue.word (minOf amount spilled))) g
      (fun cur => if cur == e + BitVec.ofNat 64 192 then
        some (PanValue.word (spilled - minOf amount spilled))
      else (fun cur => if cur == e + BitVec.ofNat 64 64 then
        some (PanValue.word (gl + minOf amount spilled)) else m cur) cur)
      baseAddress topAddress bytesInWord
      (Exp.op BinOp.add [Exp.load Shape.one (Exp.op BinOp.add
          [Exp.var VarKind.global "ev", Exp.const (BitVec.ofNat 64 72)]),
        Exp.op BinOp.sub [Exp.var VarKind.local "amount", Exp.var VarKind.local "from_gl"]])
      (some guestMemoryAccess)
      = some (PanValue.word (sgl + (amount - minOf amount spilled))) := by
    refine eval_op2 structs _ g _ baseAddress topAddress bytesInWord BinOp.add _ _ sgl
      (amount - minOf amount spilled) _ hload72 ?_
      (wordOp_add sgl (amount - minOf amount spilled))
    refine eval_op2 structs _ g _ baseAddress topAddress bytesInWord BinOp.sub _ _ amount
      (minOf amount spilled) _ ?_ ?_ (wordOp_sub amount (minOf amount spilled))
    · rw [eval_var_local]; exact hFamount
    · rw [eval_var_local]; exact hFfrom
  have hs3 := store_runs structs _ g
    (fun cur => if cur == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled - minOf amount spilled))
    else (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) cur)
    baseAddress topAddress bytesInWord context
    primitive handler functions c mh _ _ f _ _ haddr72 hval72
  -- the return
  have hret := StepCalculus.return_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (Exp.const (BitVec.ofNat 64 0))
    (updatePanValueMap (updatePanValueMap l "spilled" (PanValue.word spilled)) "from_gl"
      (PanValue.word (minOf amount spilled))) g
    (creditStateGasMemory m e gl sgl amount spilled) f _ _ 0
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimit0
  -- chain the three stores and the return, innermost first
  have hseq3 := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g
    (fun cur => if cur == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled - minOf amount spilled))
    else (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) cur) f
    _ g (creditStateGasMemory m e gl sgl amount spilled) f 1 _ _ _ hs3 hret
  have hs2' := StepCalculus.progMono context primitive handler structs functions
    baseAddress topAddress bytesInWord 1 _ g
    (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) f _
    (some guestMemoryAccess) c mh 2 _ (by omega) hs2
  have hseq2 := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g
    (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) f
    _ g
    (fun cur => if cur == e + BitVec.ofNat 64 192 then
      some (PanValue.word (spilled - minOf amount spilled))
    else (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) cur) f 2 _ _ _ hs2' hseq3
  have hs1' := StepCalculus.progMono context primitive handler structs functions
    baseAddress topAddress bytesInWord 1 _ g m f _ (some guestMemoryAccess) c mh 3 _
    (by omega) hs1
  have hseq1 := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _ _ g m f
    _ g
    (fun cur => if cur == e + BitVec.ofNat 64 64 then
      some (PanValue.word (gl + minOf amount spilled)) else m cur) f 3 _ _ _ hs1' hseq2
  have hdecCall := StepCalculus.decCall_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    "from_gl" Shape.one "min"
    [Exp.var VarKind.local "amount", Exp.var VarKind.local "spilled"] _
    (updatePanValueMap l "spilled" (PanValue.word spilled)) g m f 4 _ _ _ g m f
    (PanValue.word (minOf amount spilled)) _ hcall
    (word_shape_matches structs (minOf amount spilled)) hseq1
  have hdecval := evalCounted_load_global_add structs l g m baseAddress topAddress
    bytesInWord "ev" e (BitVec.ofNat 64 192) spilled hev hspilled
  have hfinal := StepCalculus.dec_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh "spilled" Shape.one _ _
    l g m f (PanValue.word spilled) _ 5 _ _ hdecval
    (word_shape_matches structs spilled) hdecCall
  exact ⟨_, _, hfinal⟩

end

/-! ## `access_gas_cost`: the first computed charge proved positive

`lake exe opcode-census` leaves 17 handlers whose charge is computed rather
than literal. Three of them --- `op_balance`, `op_extcodesize`,
`op_extcodehash` --- charge `access_gas_cost(addr)`, so they share one
obligation, and this is it. -/

/-- The body of `access_gas_cost`, verbatim from `Guest.guestAst`. -/
def accessGasCostBody : Prog Word :=
  match Guest.guestFn_access_gas_cost with
  | .function info => info.body
  | _ => Prog.skip

theorem accessGasCostBody_eq : accessGasCostBody =
    Prog.decCall "w" Shape.one "is_warm_address" [Exp.var VarKind.local "addr"]
      (Prog.seq
        (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "w")
            (Exp.const (BitVec.ofNat 64 0)))
          (Prog.return (Exp.const (BitVec.ofNat 64 100)))
          Prog.skip)
        (Prog.seq
          (Prog.call (some (none, none)) "warm_address" [Exp.var VarKind.local "addr"])
          (Prog.return (Exp.const (BitVec.ofNat 64 3000))))) := by
  rfl

section
variable (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
  (handler : PanValueStatefulFfiHandler Word HostMemory) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog Word))
  (baseAddress topAddress bytesInWord : Word)
  (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler Word HostMemory))

/-- **`access_gas_cost` on the warm path.** -/
theorem access_gas_cost_runs_warm
    (l g cg : VarName → Option (PanValue Word)) (m cm : Memory)
    (f cf : FfiState HostMemory)
    (cl : VarName → Option (PanValue Word))
    (wv : Word) (k csteps : Nat)
    (hwv : wv ≠ 0)
    (hIsWarm : evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord k l g m f none "is_warm_address"
      [Exp.var VarKind.local "addr"] (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned cl cg cm cf [PanValue.word wv], csteps))
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 100)) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (k + 4) l g m f accessGasCostBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' cg cm cf
          [PanValue.word (BitVec.ofNat 64 100)], steps) := by
  have hw : updatePanValueMap l "w" (PanValue.word wv) "w" = some (PanValue.word wv) := by
    simp [updatePanValueMap]
  have hcond := evalCounted_cmp_local_const structs
    (updatePanValueMap l "w" (PanValue.word wv)) cg cm baseAddress topAddress bytesInWord
    Cmp.notEqual "w" wv (BitVec.ofNat 64 0) hw
  have hz : ((RiscV.panRiscVCmp Cmp.notEqual wv (BitVec.ofNat 64 0)) != 0) = true :=
    cmp_notEqual_true_iff.mpr (by simpa using hwv)
  have hret := StepCalculus.return_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (Exp.const (BitVec.ofNat 64 100))
    (updatePanValueMap l "w" (PanValue.word wv)) cg cm cf _ _ k
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimit
  have hite := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := Prog.return (Exp.const (BitVec.ofNat 64 100))) (elseBranch := Prog.skip)
    (updatePanValueMap l "w" (PanValue.word wv)) cg cm cf _ _ (k + 1) _ _ hcond
    (by rw [if_pos hz]; exact hret)
  have hseq := StepCalculus.seq_runs_returned context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (second := Prog.seq
      (Prog.call (some (none, none)) "warm_address" [Exp.var VarKind.local "addr"])
      (Prog.return (Exp.const (BitVec.ofNat 64 3000))))
    (updatePanValueMap l "w" (PanValue.word wv)) cg cm cf _ cg cm cf (k + 2) _ _ hite
  have hIsWarm' := StepCalculus.callMono context primitive handler structs functions
    baseAddress topAddress bytesInWord k l g m f none "is_warm_address" _
    (some guestMemoryAccess) c mh (k + 3) _ (by omega) hIsWarm
  have hfinal := StepCalculus.decCall_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    "w" Shape.one "is_warm_address" [Exp.var VarKind.local "addr"] _
    l g m f (k + 3) _ _ cl cg cm cf (PanValue.word wv) _ hIsWarm'
    (word_shape_matches structs wv) hseq
  rw [accessGasCostBody_eq]
  exact ⟨_, _, hfinal⟩

/-- **`access_gas_cost` on the cold path.** -/
theorem access_gas_cost_runs_cold
    (l g cg : VarName → Option (PanValue Word)) (m cm : Memory)
    (f cf : FfiState HostMemory)
    (cl nl ng : VarName → Option (PanValue Word)) (nm : Memory) (nf : FfiState HostMemory)
    (k csteps wsteps : Nat)
    (hIsWarm : evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord k l g m f none "is_warm_address"
      [Exp.var VarKind.local "addr"] (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned cl cg cm cf
          [PanValue.word (BitVec.ofNat 64 0)], csteps))
    (hWarm : evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord k
      (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf
      (some (none, none)) "warm_address" [Exp.var VarKind.local "addr"]
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.normal nl ng nm nf, wsteps))
    (hlimit : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 3000)) = true) :
    ∃ l' steps, evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (k + 4) l g m f accessGasCostBody
      (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned l' ng nm nf
          [PanValue.word (BitVec.ofNat 64 3000)], steps) := by
  have hw : updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0)) "w"
      = some (PanValue.word (BitVec.ofNat 64 0)) := by simp [updatePanValueMap]
  have hcond := evalCounted_cmp_local_const structs
    (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm
    baseAddress topAddress bytesInWord Cmp.notEqual "w" (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 0) hw
  have hz : ((RiscV.panRiscVCmp Cmp.notEqual (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0)) != 0) = true → False := by
    intro h
    exact (cmp_notEqual_true_iff.mp h) rfl
  have hskip := StepCalculus.skip_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf k
  have hite := StepCalculus.ite_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _
    (thenBranch := Prog.return (Exp.const (BitVec.ofNat 64 100))) (elseBranch := Prog.skip)
    (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf _ _ (k + 1) _ _
    hcond (by rw [if_neg (fun h => hz h)]; exact hskip)
  have hcall := StepCalculus.call_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (some (none, none)) "warm_address" [Exp.var VarKind.local "addr"]
    (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf k _ _ hWarm
  have hret := StepCalculus.return_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    (Exp.const (BitVec.ofNat 64 3000)) nl ng nm nf _ _ k
    (by rw [evalPanValueExpCounted, eval_const]; rfl) hlimit
  have hinner := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _
    (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf
    nl ng nm nf (k + 1) _ _ _ hcall hret
  have hseq := StepCalculus.seq_runs_normal context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh _ _
    (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf
    (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf
    (k + 2) _ _ _ hite hinner
  have hIsWarm' := StepCalculus.callMono context primitive handler structs functions
    baseAddress topAddress bytesInWord k l g m f none "is_warm_address" _
    (some guestMemoryAccess) c mh (k + 3) _ (by omega) hIsWarm
  have hfinal := StepCalculus.decCall_runs context primitive handler structs functions
    baseAddress topAddress bytesInWord (some guestMemoryAccess) c mh
    "w" Shape.one "is_warm_address" [Exp.var VarKind.local "addr"] _
    l g m f (k + 3) _ _ cl cg cm cf (PanValue.word (BitVec.ofNat 64 0)) _ hIsWarm'
    (word_shape_matches structs (BitVec.ofNat 64 0)) hseq
  rw [accessGasCostBody_eq]
  exact ⟨_, _, hfinal⟩

/-- **`access_gas_cost` always charges something.** Whichever branch it takes
it returns a positive word --- 100 warm, 3000 cold --- which is the `1 <= amount`
hypothesis `charge_gas_decreases_gas` wants, for the three handlers that charge
`access_gas_cost(addr)` directly (`op_balance`, `op_extcodesize`,
`op_extcodehash`).

The two callees are still hypotheses: `is_warm_address` and `warm_address` are
`htab` probes, which need the load-factor invariant before they can be
discharged. What is settled here is that nothing *between* them can make the
charge zero. -/
theorem access_gas_cost_charge_pos
    (l g cg : VarName → Option (PanValue Word)) (m cm : Memory)
    (f cf : FfiState HostMemory)
    (cl : VarName → Option (PanValue Word))
    (wv : Word) (k csteps : Nat)
    (hIsWarm : evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord k l g m f none "is_warm_address"
      [Exp.var VarKind.local "addr"] (some guestMemoryAccess) c mh
      = some (PanValueFfiControlResult.returned cl cg cm cf [PanValue.word wv], csteps))
    (hWarm : wv = BitVec.ofNat 64 0 →
      ∃ nl ng nm nf wsteps, evalPanValueFfiCallSteps context primitive handler structs
        functions baseAddress topAddress bytesInWord k
        (updatePanValueMap l "w" (PanValue.word (BitVec.ofNat 64 0))) cg cm cf
        (some (none, none)) "warm_address" [Exp.var VarKind.local "addr"]
        (some guestMemoryAccess) c mh
        = some (PanValueFfiControlResult.normal nl ng nm nf, wsteps))
    (hlimit100 : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 100)) = true)
    (hlimit3000 : panValuePayloadWithinLimit structs
      (PanValue.word (BitVec.ofNat 64 3000)) = true) :
    ∃ l' g' m' f' cost steps,
      evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord (k + 4) l g m f accessGasCostBody
        (some guestMemoryAccess) c mh
        = some (PanValueFfiControlResult.returned l' g' m' f' [PanValue.word cost], steps)
      ∧ 1 ≤ cost.toNat := by
  by_cases hzero : wv = BitVec.ofNat 64 0
  · subst hzero
    obtain ⟨nl, ng, nm, nf, wsteps, hw⟩ := hWarm rfl
    obtain ⟨l', steps, hrun⟩ := access_gas_cost_runs_cold context primitive handler structs
      functions baseAddress topAddress bytesInWord c mh l g cg m cm f cf cl nl ng nm nf
      k csteps wsteps hIsWarm hw hlimit3000
    exact ⟨l', ng, nm, nf, _, steps, hrun, by decide⟩
  · obtain ⟨l', steps, hrun⟩ := access_gas_cost_runs_warm context primitive handler structs
      functions baseAddress topAddress bytesInWord c mh l g cg m cm f cf cl wv k csteps
      (by simpa using hzero) hIsWarm hlimit100
    exact ⟨l', cg, cm, cf, _, steps, hrun, by decide⟩

end

end Guest
