import Flapjack.PanValueFfiSemantics

/-!
# A step calculus for the stepped stateful-FFI semantics

`Guest.StepBound.TerminatesWithin` asks for *some* fuel at which the run
returns. To get that compositionally — a cost lemma per function, combined
along the call graph — sub-proofs carried at different fuels have to be brought
to a common fuel, and that needs **fuel monotonicity**: a successful run is
unchanged, same control result *and* same step count, by any larger fuel.

Flapjack does not have it. `Flapjack.PanSteppedSemantics` proves the `_fst`/
`_snd` projections relating the stepped evaluator to the unstepped one, but
nothing about varying the fuel, so no two cost lemmas can currently be combined.
This module supplies it, for the evaluator `Guest.Model` actually uses:

* `progMono` / `callMono` — the mutually recursive
  `Flapjack.evalPanValueFfiProgSteps` and `evalPanValueFfiCallSteps`, by the
  functional-induction principle `evalPanValueFfiProgSteps.induct`;
* `evalPanValueFfiProgramStepped_fuel_mono` — the public entry point, which is
  what `Guest.runGuestStepped` is.

Note that fuel here is a *depth* budget, not a work budget: `.seq first second`
at `fuel + 1` evaluates both halves at `fuel`, so it bounds syntactic nesting
and call depth as well as loop iterations. Monotonicity is what makes that
usable — a bound proved for a sub-program stays true in any larger context.

This belongs upstream in flapjack; it lives here so that the pinned revision in
`lakefile.toml` does not have to move. The namespace is `Guest.StepCalculus`
rather than `Flapjack.*` so that a future re-pin cannot collide with it.
-/

open Flapjack

namespace Guest
namespace StepCalculus

variable {α σ : Type}
  [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
  [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
  [LT α] [DecidableRel (fun left right : α => left < right)]

section
variable (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
  (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
  (functions : List (FunName × List VarName × Prog α))
  (baseAddress topAddress bytesInWord : α)

/-- Monotonicity statement for the call evaluator (`motive1`). -/
def CallMono (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) : Prop :=
  ∀ fuel' result, fuel ≤ fuel' →
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi info function
      arguments ma c mh = some result →
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi info function
      arguments ma c mh = some result

/-- Monotonicity statement for the program evaluator (`motive2`). -/
def ProgMono (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) : Prop :=
  ∀ fuel' result, fuel ≤ fuel' →
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi program
      ma c mh = some result →
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi program
      ma c mh = some result


/-- The successor case of the call evaluator, as a standalone lemma: it is
shared between `progMono`'s `case2` and `callMono`, which differ only in where
the two program-evaluator induction hypotheses come from. -/
theorem call_succ_mono (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (ihBody : ∀ (body : Prog α) (calleeLocals : VarName → Option (PanValue α)),
      ProgMono context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel calleeLocals globals memory ffi body ma c mh)
    (ihHandler : ∀ (calleeGlobals : VarName → Option (PanValue α))
      (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
      (value : PanValue α) (handlerVariable : VarName) (handlerProgram : Prog α),
      ProgMono context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel (updatePanValueMap locals handlerVariable value) calleeGlobals
        calleeMemory calleeFfi handlerProgram ma c mh) :
    CallMono context primitive handler structs functions baseAddress topAddress
      bytesInWord (fuel + 1) locals globals memory ffi info function arguments ma c mh := by
  intro fuel' result hle h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiCallSteps] at h
  rw [evalPanValueFfiCallSteps]
  cases hargs : evalPanValueExpsCounted structs locals globals memory baseAddress
      topAddress bytesInWord arguments ma with
  | none => rw [hargs] at h; simp at h
  | some ap =>
    obtain ⟨values, argumentSteps⟩ := ap
    rw [hargs] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    cases hlk : lookupPanFunction function functions with
    | none => rw [hlk] at h; simp at h
    | some pb =>
      obtain ⟨parameters, body⟩ := pb
      rw [hlk] at h
      simp only [Option.bind_some] at h ⊢
      cases hbind : bindPanValueParameters parameters values with
      | none => rw [hbind] at h; simp at h
      | some calleeLocals =>
        rw [hbind] at h
        simp only [Option.bind_some] at h ⊢
        cases hbody : evalPanValueFfiProgSteps context primitive handler structs functions
            baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body ma c mh with
        | none => rw [hbody] at h; simp at h
        | some rp =>
          obtain ⟨res, steps⟩ := rp
          rw [hbody] at h
          rw [ihBody body calleeLocals _ _ hfk hbody]
          simp only [Option.bind_some] at h ⊢
          cases res with
          | normal l cg cm cf => exact h
          | returned l cg cm cf vs => exact h
          | broke l cg cm cf => exact h
          | continued l cg cm cf => exact h
          | finalFfi l cg cm cf ev => exact h
          | raised l cg cm cf e v =>
            dsimp only at h ⊢
            by_cases hvalid :
                (panValueExceptionValid structs c e v && panValuePayloadWithinLimit structs v) = true
            · rw [if_pos hvalid] at h ⊢
              cases info with
              | none => exact h
              | some pr =>
                obtain ⟨destination, handlerInfo⟩ := pr
                cases handlerInfo with
                | none => exact h
                | some triple =>
                  obtain ⟨caught, handlerVariable, handlerProgram⟩ := triple
                  dsimp only at h ⊢
                  by_cases hcaught : (caught == e) = true
                  · rw [if_pos hcaught] at h ⊢
                    by_cases hhv : panValueHandlerValid structs c locals handlerVariable v
                    · rw [if_pos hhv] at h ⊢
                      cases hh : evalPanValueFfiProgSteps context primitive handler structs functions
                          baseAddress topAddress bytesInWord fuel (updatePanValueMap locals handlerVariable v)
                          cg cm cf handlerProgram ma c mh with
                      | none => rw [hh] at h; simp at h
                      | some q =>
                        rw [hh] at h
                        rw [ihHandler _ _ _ _ _ _ _ _ hfk hh]
                        exact h
                    · rw [if_neg hhv] at h; simp at h
                  · rw [if_neg hcaught] at h ⊢; exact h
            · rw [if_neg hvalid] at h; simp at h

theorem progMono : ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)),
    ProgMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel locals globals memory ffi program ma c mh := by
  intro fuel locals globals memory ffi program ma c mh
  induction fuel, locals, globals, memory, ffi, program, ma, c, mh using
    evalPanValueFfiProgSteps.induct (motive1 := CallMono context primitive handler
      structs functions baseAddress topAddress bytesInWord) with
  | case1 =>
    intro fuel' result hle h
    rw [evalPanValueFfiCallSteps] at h
    simp at h
  | case2 fuel locals globals memory ffi info function arguments ma c mh ihBody ihHandler =>
    exact call_succ_mono context primitive handler structs functions baseAddress
      topAddress bytesInWord fuel locals globals memory ffi info function arguments
      ma c mh ihBody ihHandler
  | case3 =>
    intro fuel' result hle h
    rw [evalPanValueFfiProgSteps] at h
    simp at h
  | case4 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case5 fuel locals globals memory ffi name shape valueExp body ma c mh ihBody =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    cases hv : evalPanValueExpCounted structs locals globals memory baseAddress topAddress
        bytesInWord valueExp ma with
    | none => rw [hv] at h; simp at h
    | some pair =>
      obtain ⟨value, valueSteps⟩ := pair
      rw [hv] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      by_cases hshape : panShapeMatches (panValueShape structs value) shape
      · rw [if_pos hshape] at h ⊢
        cases hb : evalPanValueFfiProgSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value) globals memory ffi body
            ma c mh with
        | none => rw [hb] at h; simp at h
        | some q =>
          rw [hb] at h
          rw [ihBody value _ _ hfk hb]
          exact h
      · rw [if_neg hshape] at h; simp at h
  | case6 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case7 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case8 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case9 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case10 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case11 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case12 fuel locals globals memory ffi first second ma c mh ihFirst ihSecond =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    cases hf : evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi first ma c mh with
    | none => rw [hf] at h; simp at h
    | some p =>
      obtain ⟨firstResult, firstSteps⟩ := p
      rw [hf] at h
      rw [ihFirst _ _ hfk hf]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases firstResult with
      | normal l g m f =>
        dsimp only at h ⊢
        cases hs : evalPanValueFfiProgSteps context primitive handler structs functions
            baseAddress topAddress bytesInWord fuel l g m f second ma c mh with
        | none => rw [hs] at h; simp at h
        | some q =>
          rw [hs] at h
          rw [ihSecond _ _ _ _ _ _ hfk hs]
          exact h
      | returned l g m f vs => exact h
      | raised l g m f e v => exact h
      | broke l g m f => exact h
      | continued l g m f => exact h
      | finalFfi l g m f ev => exact h
  | case13 fuel locals globals memory ffi condition thenBranch elseBranch ma c mh ihThen ihElse =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    cases hc : evalPanValueExpCounted structs locals globals memory baseAddress topAddress
        bytesInWord condition ma with
    | none => rw [hc] at h; simp at h
    | some pair =>
      obtain ⟨cvalue, conditionSteps⟩ := pair
      rw [hc] at h
      cases cvalue with
      | word w =>
        simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
        by_cases hz : (w != 0) = true
        · rw [if_pos hz] at h ⊢
          cases ht : evalPanValueFfiProgSteps context primitive handler structs functions
            baseAddress topAddress bytesInWord fuel locals globals memory ffi thenBranch ma c mh with
          | none => rw [ht] at h; simp at h
          | some q =>
            rw [ht] at h
            rw [ihThen _ _ hfk ht]
            exact h
        · rw [if_neg hz] at h ⊢
          cases te : evalPanValueFfiProgSteps context primitive handler structs functions
            baseAddress topAddress bytesInWord fuel locals globals memory ffi elseBranch ma c mh with
          | none => rw [te] at h; simp at h
          | some q =>
            rw [te] at h
            rw [ihElse _ _ hfk te]
            exact h
      | _ => simp at h
  | case14 fuel locals globals memory ffi info function arguments ma c mh ihCall =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    cases hcall : evalPanValueFfiCallSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi info function arguments ma c mh with
    | none => rw [hcall] at h; simp at h
    | some q =>
      rw [hcall] at h
      rw [ihCall _ _ hfk hcall]
      exact h
  | case15 fuel locals globals memory ffi name shape function arguments body ma c mh
      ihCall ihBody =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    cases hcall : evalPanValueFfiCallSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi none function arguments ma c mh with
    | none => rw [hcall] at h; simp at h
    | some p =>
      obtain ⟨callResult, callSteps⟩ := p
      rw [hcall] at h
      rw [ihCall _ _ hfk hcall]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases callResult with
      | returned l g m f vs =>
        cases vs with
        | nil => simp at h
        | cons value rest =>
          cases rest with
          | cons _ _ => simp at h
          | nil =>
            dsimp only at h ⊢
            by_cases hshape : panShapeMatches (panValueShape structs value) shape
            · rw [if_pos hshape] at h ⊢
              cases hb : evalPanValueFfiProgSteps context primitive handler structs functions
                baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value) g m f body ma c mh with
              | none => rw [hb] at h; simp at h
              | some q =>
                rw [hb] at h
                rw [ihBody _ _ _ _ _ _ hfk hb]
                exact h
            · rw [if_neg hshape] at h; simp at h
      | raised l g m f e v => exact h
      | normal l g m f => simp at h
      | broke l g m f => simp at h
      | continued l g m f => simp at h
      | finalFfi l g m f ev => simp at h
  | case16 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case17 fuel locals globals memory ffi conditionExp body ma c mh ihBody ihLoop =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    cases hc : evalPanValueExpCounted structs locals globals memory baseAddress topAddress
        bytesInWord conditionExp ma with
    | none => rw [hc] at h; simp at h
    | some pair =>
      obtain ⟨condition, conditionSteps⟩ := pair
      rw [hc] at h
      cases condition with
      | word cv =>
        simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
        by_cases hz : (cv == 0) = true
        · rw [if_pos hz] at h ⊢; exact h
        · rw [if_neg hz] at h ⊢
          cases hb : evalPanValueFfiProgSteps context primitive handler structs functions
            baseAddress topAddress bytesInWord fuel locals globals memory ffi body ma c mh with
          | none => rw [hb] at h; simp at h
          | some bodyPair =>
            obtain ⟨bodyResult, bodySteps⟩ := bodyPair
            rw [hb] at h
            rw [ihBody _ _ hfk hb]
            simp only [Option.bind_some] at h ⊢
            cases bodyResult with
            | normal l g m f =>
              dsimp only at h ⊢
              cases hl : evalPanValueFfiProgSteps context primitive handler structs functions
                baseAddress topAddress bytesInWord fuel l g m f (Prog.while conditionExp body) ma c mh with
              | none => rw [hl] at h; simp at h
              | some loopPair =>
                rw [hl] at h
                rw [ihLoop _ _ _ _ _ _ hfk hl]
                exact h
            | continued l g m f =>
              dsimp only at h ⊢
              cases hl : evalPanValueFfiProgSteps context primitive handler structs functions
                baseAddress topAddress bytesInWord fuel l g m f (Prog.while conditionExp body) ma c mh with
              | none => rw [hl] at h; simp at h
              | some loopPair =>
                rw [hl] at h
                rw [ihLoop _ _ _ _ _ _ hfk hl]
                exact h
            | returned l g m f vs => exact h
            | raised l g m f e v => exact h
            | broke l g m f => exact h
            | finalFfi l g m f ev => exact h
      | _ => simp at h
  | case18 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case19 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case20 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case21 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case22 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case23 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case24 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h
  | case25 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiProgSteps] at h
    rw [evalPanValueFfiProgSteps]
    exact h

/-- Fuel monotonicity for the call evaluator, from `progMono`. -/
theorem callMono : ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)),
    CallMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel locals globals memory ffi info function arguments ma c mh := by
  intro fuel locals globals memory ffi info function arguments ma c mh
  cases fuel with
  | zero =>
    intro fuel' result hle h
    rw [evalPanValueFfiCallSteps] at h
    simp at h
  | succ n =>
    exact call_succ_mono context primitive handler structs functions baseAddress topAddress
      bytesInWord n locals globals memory ffi info function arguments ma c mh
      (fun body calleeLocals => progMono context primitive handler structs functions
        baseAddress topAddress bytesInWord n calleeLocals globals memory ffi body ma c mh)
      (fun cg cm cf value hv hp => progMono context primitive handler structs functions
        baseAddress topAddress bytesInWord n (updatePanValueMap locals hv value) cg cm cf
        hp ma c mh)

end

section
variable {α σ : Type}
  [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
  [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
  [LT α] [DecidableRel (fun left right : α => left < right)]

/-- **Fuel monotonicity for the public stepped evaluator.** A successful run is
unchanged — same control result, same step count — by any larger fuel. This is
what lets per-function cost lemmas compose: two sub-runs proved at their own
fuels can be brought to a common fuel by taking the maximum. -/
theorem evalPanValueFfiProgramStepped_fuel_mono
    (context : PanValueFfiContext α) (initial : PanValueFfiProgramState α σ)
    (primitive : PanPrimitiveHandler α) (handler : PanValueStatefulFfiHandler α σ)
    {fuel fuel' : Nat} (hfuel : fuel ≤ fuel') (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    {ma : Option (PanValueMemoryAccess α)}
    {mh : Option (PanValueMemoryFfiHandler α σ)}
    {result : PanValueFfiSteppedResult α σ}
    (hrun : evalPanValueFfiProgramStepped context initial primitive handler fuel
      declarations entry arguments (memoryAccess := ma) (memoryHandler := mh) = some result) :
    evalPanValueFfiProgramStepped context initial primitive handler fuel'
      declarations entry arguments (memoryAccess := ma) (memoryHandler := mh) = some result := by
  unfold evalPanValueFfiProgramStepped at hrun ⊢
  cases hstate : evalPanValueDeclarations initial.source declarations (memoryAccess := ma) with
  | none => rw [hstate] at hrun; simp at hrun
  | some state =>
    rw [hstate] at hrun
    simp only [Option.bind_eq_bind, Option.bind_some] at hrun ⊢
    cases hcall : evalPanValueFfiCallSteps context primitive handler state.structs
        state.functions state.baseAddress state.topAddress state.bytesInWord fuel
        (fun _ => none) state.globals state.memory initial.ffi none entry arguments ma
        (some (PanValueCallContracts.mk state.returnShapes state.exceptions)) mh with
    | none => rw [hcall] at hrun; simp at hrun
    | some callResult =>
      rw [hcall] at hrun
      rw [callMono context primitive handler state.structs state.functions state.baseAddress
        state.topAddress state.bytesInWord fuel (fun _ => none) state.globals state.memory
        initial.ffi none entry arguments ma
        (some (PanValueCallContracts.mk state.returnShapes state.exceptions)) mh _ _ hfuel hcall]
      exact hrun

end
end StepCalculus
end Guest
