import Guest.Termination
import Guest.Model

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
memory layer that does not exist yet: `Exp.load` and `Prog.store` bottom out in
`panValueFlatLoad` and `panValueStoreWithAccess`, about which flapjack proves
nothing, so for now the load, the comparison and the tail are assumed rather
than derived from the state.
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
    (hraise : ∀ l' : VarName → Option (PanValue Word),
      ∃ r, evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord 1 l' g m f
        (Prog.raise "EvmErr" (Exp.const (BitVec.ofNat 64 4))) ma c mh = some r)
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
      exact ⟨1, hraise _⟩
    · intro _
      exact ⟨1, _, by rw [evalPanValueFfiProgSteps]⟩
  obtain ⟨fuel1, r1, hr1⟩ := hite
  obtain ⟨r1a, r1b⟩ := r1
  exact seq_terminates context primitive handler structs functions baseAddress
    topAddress bytesInWord ma c mh _ _ (updatePanValueMap l "gl" glv) g m f
    fuel1 r1a r1b hr1 (fun l'' g'' m'' f'' _ => htail l'' g'' m'' f'')

end

end Guest
