import Guest.StepCalculus

/-!
# Structural termination rules for the stepped stateful-FFI semantics

`Guest.StepBound.TerminatesWithin` needs the guest run to *return* at some
fuel. `Guest.StepCalculus` supplies fuel monotonicity, which is what lets two
sub-proofs carried at different fuels be brought to a common fuel; this module
uses it to turn that into a termination calculus, so that a whole-program
termination proof can be assembled from per-construct facts.

* `while_terminates` — **the one that matters.** A loop whose condition always
  evaluates and whose body, whenever entered, terminates and strictly decreases
  a measure `μ` on the states it continues from, terminates. Proved by strong
  induction on `μ`, taking `max` of the body's fuel and the tail's and lifting
  both with `progMono`. The guest has 257 `while` loops and no recursion
  (#71), so with this each loop reduces to exhibiting a measure.
* `seq_terminates`, `ite_terminates`, `dec_terminates`, `call_terminates` — the
  compositional rules for assembling a function body.
* `callSteps_terminates` — the call evaluator itself: arguments evaluate, the
  callee is found and binds, the body returns, and whatever the body's result
  requires of the caller holds. Those last hypotheses are not bureaucracy: they
  are exactly the evaluator's own `none` branches (the return- and
  exception-validity checks, the destination assignment, a matching handler),
  and a call cannot terminate without them.

The leaf constructors need no rule of their own: `Terminates` for `skip`,
`assign`, `store`, `return`, `raise`, `break`, `continue`, `tick` and `annot`
is discharged at the point of use by exhibiting the one-step run, e.g.
`⟨1, _, by rw [evalPanValueFfiProgSteps, hexp]; rfl⟩`. Their only content is
whether the expressions evaluate, which is an expression-level question.

What is left is therefore the *measures* for the guest's loops;
`docs/STEP-BOUND.md` records which of the 257 are substantive.
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
  (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
  (mh : Option (PanValueMemoryFfiHandler α σ))

/-- `prog` returns at some fuel from the state `(l, g, m, f)`. -/
def Terminates (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α))
    (f : FfiState σ) (prog : Prog α) : Prop :=
  ∃ fuel result, evalPanValueFfiProgSteps context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel l g m f prog ma c mh = some result

/-- A loop whose condition always evaluates and whose body, whenever it is
entered, terminates and strictly decreases `μ` on the states it continues from,
terminates. -/
theorem while_terminates (cond : Exp α) (body : Prog α)
    (μ : (VarName → Option (PanValue α)) → (VarName → Option (PanValue α)) →
      (α → Option (PanValue α)) → FfiState σ → Nat)
    (hcond : ∀ (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)),
      ∃ n cs, evalPanValueExpCounted structs l g m
        baseAddress topAddress bytesInWord cond ma = some (PanValue.word n, cs))
    (hbody : ∀ l g m f n cs,
      evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord cond ma
        = some (PanValue.word n, cs) → (n == 0) = false →
      ∃ fuel result steps,
        evalPanValueFfiProgSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel l g m f body ma c mh
          = some (result, steps) ∧
        ∀ l' g' m' f', result = .normal l' g' m' f' ∨ result = .continued l' g' m' f' →
          μ l' g' m' f' < μ l g m f) :
    ∀ l g m f, Terminates context primitive handler structs functions baseAddress
      topAddress bytesInWord ma c mh l g m f (Prog.while cond body) := by
  suffices H : ∀ n l g m f, μ l g m f = n →
      Terminates context primitive handler structs functions baseAddress topAddress
        bytesInWord ma c mh l g m f (Prog.while cond body) by
    intro l g m f; exact H _ l g m f rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro l g m f hmu
    obtain ⟨cv, cs, hc⟩ := hcond l g m
    unfold Terminates
    by_cases hz : (cv == 0) = true
    · refine ⟨1, (PanValueFfiControlResult.normal l g m f, cs + 1), ?_⟩
      rw [evalPanValueFfiProgSteps, hc]
      simp only [Option.bind_eq_bind, Option.bind_some, if_pos hz]
      rfl
    · obtain ⟨bfuel, bres, bsteps, hb, hdec⟩ := hbody l g m f cv cs hc (by simpa using hz)
      have hmono : ∀ (k : Nat), bfuel ≤ k →
          evalPanValueFfiProgSteps context primitive handler structs functions
            baseAddress topAddress bytesInWord k l g m f body ma c mh = some (bres, bsteps) :=
        fun k hk => progMono context primitive handler structs functions baseAddress topAddress
            bytesInWord bfuel l g m f body ma c mh k (bres, bsteps) hk hb
      cases bres with
      | normal l' g' m' f' =>
        have hlt : μ l' g' m' f' < n := by
          rw [← hmu]; exact hdec l' g' m' f' (Or.inl rfl)
        obtain ⟨lfuel, lres, hl⟩ := ih _ hlt l' g' m' f' rfl
        obtain ⟨lres1, lres2⟩ := lres
        refine ⟨max bfuel lfuel + 1, (lres1, cs + bsteps + lres2 + 1), ?_⟩
        rw [evalPanValueFfiProgSteps, hc]
        simp only [Option.bind_eq_bind, Option.bind_some, if_neg hz]
        rw [hmono _ (Nat.le_max_left _ _)]
        simp only [Option.bind_some]
        rw [progMono context primitive handler structs functions baseAddress topAddress
            bytesInWord lfuel l' g' m' f' (Prog.while cond body) ma c mh
          (max bfuel lfuel) (lres1, lres2) (Nat.le_max_right _ _) hl]
        rfl
      | continued l' g' m' f' =>
        have hlt : μ l' g' m' f' < n := by
          rw [← hmu]; exact hdec l' g' m' f' (Or.inr rfl)
        obtain ⟨lfuel, lres, hl⟩ := ih _ hlt l' g' m' f' rfl
        obtain ⟨lres1, lres2⟩ := lres
        refine ⟨max bfuel lfuel + 1, (lres1, cs + bsteps + lres2 + 1), ?_⟩
        rw [evalPanValueFfiProgSteps, hc]
        simp only [Option.bind_eq_bind, Option.bind_some, if_neg hz]
        rw [hmono _ (Nat.le_max_left _ _)]
        simp only [Option.bind_some]
        rw [progMono context primitive handler structs functions baseAddress topAddress
            bytesInWord lfuel l' g' m' f' (Prog.while cond body) ma c mh
          (max bfuel lfuel) (lres1, lres2) (Nat.le_max_right _ _) hl]
        rfl
      | broke l' g' m' f' =>
        refine ⟨bfuel + 1, (PanValueFfiControlResult.normal l' g' m' f', cs + bsteps + 1), ?_⟩
        rw [evalPanValueFfiProgSteps, hc]
        simp only [Option.bind_eq_bind, Option.bind_some, if_neg hz]
        rw [hmono _ (Nat.le_refl _)]
        rfl
      | returned l' g' m' f' vs =>
        refine ⟨bfuel + 1, (PanValueFfiControlResult.returned l' g' m' f' vs, cs + bsteps + 1), ?_⟩
        rw [evalPanValueFfiProgSteps, hc]
        simp only [Option.bind_eq_bind, Option.bind_some, if_neg hz]
        rw [hmono _ (Nat.le_refl _)]
        rfl
      | raised l' g' m' f' e v =>
        refine ⟨bfuel + 1, (PanValueFfiControlResult.raised l' g' m' f' e v, cs + bsteps + 1), ?_⟩
        rw [evalPanValueFfiProgSteps, hc]
        simp only [Option.bind_eq_bind, Option.bind_some, if_neg hz]
        rw [hmono _ (Nat.le_refl _)]
        rfl
      | finalFfi l' g' m' f' ev =>
        refine ⟨bfuel + 1, (PanValueFfiControlResult.finalFfi l' g' m' f' ev, cs + bsteps + 1), ?_⟩
        rw [evalPanValueFfiProgSteps, hc]
        simp only [Option.bind_eq_bind, Option.bind_some, if_neg hz]
        rw [hmono _ (Nat.le_refl _)]
        rfl

/-- `seq`: exhibit a run of `first`, then handle the case where it falls
through. -/
theorem seq_terminates (first second : Prog α)
    (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)) (f : FfiState σ)
    (fuel1 : Nat) (r1 : PanValueFfiControlResult α σ) (s1 : Nat)
    (hfirst : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel1 l g m f first ma c mh = some (r1, s1))
    (hsecond : ∀ l' g' m' f', r1 = .normal l' g' m' f' →
      Terminates context primitive handler structs functions baseAddress topAddress
        bytesInWord ma c mh l' g' m' f' second) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh l g m f (Prog.seq first second) := by
  unfold Terminates
  have hmono : ∀ k, fuel1 ≤ k → evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord k l g m f first ma c mh = some (r1, s1) :=
    fun k hk => progMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel1 l g m f first ma c mh k (r1, s1) hk hfirst
  cases r1 with
  | normal l' g' m' f' =>
    obtain ⟨fuel2, r2, h2⟩ := hsecond l' g' m' f' rfl
    obtain ⟨r2a, r2b⟩ := r2
    refine ⟨max fuel1 fuel2 + 1, (r2a, s1 + r2b + 1), ?_⟩
    rw [evalPanValueFfiProgSteps, hmono _ (Nat.le_max_left _ _)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [progMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel2 l' g' m' f' second ma c mh (max fuel1 fuel2) (r2a, r2b)
      (Nat.le_max_right _ _) h2]
    rfl
  | returned l' g' m' f' vs =>
    exact ⟨fuel1 + 1, _, by rw [evalPanValueFfiProgSteps, hmono _ (Nat.le_refl _)]; rfl⟩
  | raised l' g' m' f' e v =>
    exact ⟨fuel1 + 1, _, by rw [evalPanValueFfiProgSteps, hmono _ (Nat.le_refl _)]; rfl⟩
  | broke l' g' m' f' =>
    exact ⟨fuel1 + 1, _, by rw [evalPanValueFfiProgSteps, hmono _ (Nat.le_refl _)]; rfl⟩
  | continued l' g' m' f' =>
    exact ⟨fuel1 + 1, _, by rw [evalPanValueFfiProgSteps, hmono _ (Nat.le_refl _)]; rfl⟩
  | finalFfi l' g' m' f' ev =>
    exact ⟨fuel1 + 1, _, by rw [evalPanValueFfiProgSteps, hmono _ (Nat.le_refl _)]; rfl⟩

/-- `call`: a call statement terminates exactly when the call evaluator does. -/
theorem call_terminates
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)) (f : FfiState σ)
    (fuel : Nat) (r : PanValueFfiSteppedResult α σ)
    (hcall : evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel l g m f info function arguments ma c mh
      = some r) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh l g m f (Prog.call info function arguments) := by
  unfold Terminates
  obtain ⟨ra, rb⟩ := r
  exact ⟨fuel + 1, (ra, rb + 1), by rw [evalPanValueFfiProgSteps, hcall]; rfl⟩

/-- `ite`: whichever branch the condition selects. -/
theorem ite_terminates (condition : Exp α) (thenBranch elseBranch : Prog α)
    (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)) (f : FfiState σ)
    (cv : α) (cs : Nat)
    (hc : evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      condition ma = some (PanValue.word cv, cs))
    (hthen : (cv != 0) = true →
      Terminates context primitive handler structs functions baseAddress topAddress
        bytesInWord ma c mh l g m f thenBranch)
    (helse : (cv != 0) = false →
      Terminates context primitive handler structs functions baseAddress topAddress
        bytesInWord ma c mh l g m f elseBranch) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh l g m f (Prog.ite condition thenBranch elseBranch) := by
  unfold Terminates
  by_cases hz : (cv != 0) = true
  · obtain ⟨fuel, r, h⟩ := hthen hz
    obtain ⟨ra, rb⟩ := r
    refine ⟨fuel + 1, (ra, cs + rb + 1), ?_⟩
    rw [evalPanValueFfiProgSteps, hc]
    simp only [Option.bind_eq_bind, Option.bind_some, if_pos hz, h]
    rfl
  · obtain ⟨fuel, r, h⟩ := helse (by simpa using hz)
    obtain ⟨ra, rb⟩ := r
    refine ⟨fuel + 1, (ra, cs + rb + 1), ?_⟩
    rw [evalPanValueFfiProgSteps, hc]
    simp only [Option.bind_eq_bind, Option.bind_some, if_neg hz, h]
    rfl

/-- `dec`: the initialiser evaluates and matches its shape, and the body
terminates with the new binding in scope. -/
theorem dec_terminates (name : VarName) (shape : Shape) (valueExp : Exp α) (body : Prog α)
    (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)) (f : FfiState σ)
    (value : PanValue α) (vs : Nat)
    (hv : evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord
      valueExp ma = some (value, vs))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hbody : Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh (updatePanValueMap l name value) g m f body) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh l g m f (Prog.dec name shape valueExp body) := by
  unfold Terminates
  obtain ⟨fuel, r, h⟩ := hbody
  obtain ⟨ra, rb⟩ := r
  refine ⟨fuel + 1, (restorePanValueFfiLocal name (l name) ra, vs + rb + 1), ?_⟩
  rw [evalPanValueFfiProgSteps, hv]
  simp only [Option.bind_eq_bind, Option.bind_some, if_pos hshape, h]
  rfl


/-- `evalPanValueFfiCallSteps`: a call returns when its arguments evaluate, the
callee is found and its parameters bind, the body returns, and whatever the
body's result requires of the caller holds — the return/exception validity
checks the evaluator makes, the destination assignment, and termination of a
matching handler. Those hypotheses are the evaluator's own `none` branches; a
call cannot terminate without them. -/
theorem callSteps_terminates
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)) (f : FfiState σ)
    (values : List (PanValue α)) (argSteps : Nat)
    (parameters : List VarName) (body : Prog α)
    (calleeLocals : VarName → Option (PanValue α))
    (bfuel : Nat) (res : PanValueFfiControlResult α σ) (bsteps : Nat)
    (hargs : evalPanValueExpsCounted structs l g m baseAddress topAddress bytesInWord
      arguments ma = some (values, argSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hbody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord bfuel calleeLocals g m f body ma c mh = some (res, bsteps))
    (hret : ∀ cl cg cm cf vs, res = .returned cl cg cm cf vs →
      (panValueReturnValid structs c function vs &&
        panValueValuesWithinLimit structs vs) = true ∧
      ∀ destination handlerInfo, info = some (destination, handlerInfo) →
        ∃ lg, assignPanValueCallResult l cg destination vs (structs := structs) = some lg)
    (hraise : ∀ cl cg cm cf e v, res = .raised cl cg cm cf e v →
      (panValueExceptionValid structs c e v &&
        panValuePayloadWithinLimit structs v) = true ∧
      ∀ destination caught handlerVariable handlerProgram,
        info = some (destination, some (caught, handlerVariable, handlerProgram)) →
        (caught == e) = true →
        panValueHandlerValid structs c l handlerVariable v = true ∧
        Terminates context primitive handler structs functions baseAddress topAddress
          bytesInWord ma c mh (updatePanValueMap l handlerVariable v) cg cm cf handlerProgram) :
    ∃ fuel r, evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel l g m f info function arguments ma c mh
      = some r := by
  cases res with
  | normal cl cg cm cf =>
    refine ⟨bfuel + 1, (.normal l cg cm cf, argSteps + bsteps), ?_⟩
    rw [evalPanValueFfiCallSteps, hargs]
    simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody]
    rfl
  | broke cl cg cm cf =>
    refine ⟨bfuel + 1, (.broke l cg cm cf, argSteps + bsteps), ?_⟩
    rw [evalPanValueFfiCallSteps, hargs]
    simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody]
    rfl
  | continued cl cg cm cf =>
    refine ⟨bfuel + 1, (.continued l cg cm cf, argSteps + bsteps), ?_⟩
    rw [evalPanValueFfiCallSteps, hargs]
    simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody]
    rfl
  | finalFfi cl cg cm cf ev =>
    refine ⟨bfuel + 1, (.finalFfi (fun _ => none) cg cm cf ev, argSteps + bsteps), ?_⟩
    rw [evalPanValueFfiCallSteps, hargs]
    simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody]
    rfl
  | returned cl cg cm cf vs =>
    obtain ⟨hvalid, hassign⟩ := hret cl cg cm cf vs rfl
    cases info with
    | none =>
      refine ⟨bfuel + 1, (.returned (fun _ => none) cg cm cf vs, argSteps + bsteps), ?_⟩
      rw [evalPanValueFfiCallSteps, hargs]
      simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody, if_pos hvalid]
      rfl
    | some pr =>
      obtain ⟨destination, handlerInfo⟩ := pr
      obtain ⟨lg, hlg⟩ := hassign destination handlerInfo rfl
      obtain ⟨nl, ng⟩ := lg
      refine ⟨bfuel + 1, (.normal nl ng cm cf, argSteps + bsteps), ?_⟩
      rw [evalPanValueFfiCallSteps, hargs]
      simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody, if_pos hvalid, hlg]
      rfl
  | raised cl cg cm cf e v =>
    obtain ⟨hvalid, hhandler⟩ := hraise cl cg cm cf e v rfl
    cases info with
    | none =>
      refine ⟨bfuel + 1, (.raised (fun _ => none) cg cm cf e v, argSteps + bsteps), ?_⟩
      rw [evalPanValueFfiCallSteps, hargs]
      simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody, if_pos hvalid]
      rfl
    | some pr =>
      obtain ⟨destination, handlerInfo⟩ := pr
      cases handlerInfo with
      | none =>
        refine ⟨bfuel + 1, (.raised (fun _ => none) cg cm cf e v, argSteps + bsteps), ?_⟩
        rw [evalPanValueFfiCallSteps, hargs]
        simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody, if_pos hvalid]
        rfl
      | some triple =>
        obtain ⟨caught, hvar, hprog⟩ := triple
        by_cases hcaught : (caught == e) = true
        · obtain ⟨hvalidh, hterm⟩ := hhandler destination caught hvar hprog rfl hcaught
          obtain ⟨hfuel, hres, hh⟩ := hterm
          obtain ⟨hra, hrb⟩ := hres
          refine ⟨max bfuel hfuel + 1, (hra, argSteps + bsteps + hrb), ?_⟩
          rw [evalPanValueFfiCallSteps, hargs]
          simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind]
          rw [progMono context primitive handler structs functions baseAddress topAddress
        bytesInWord bfuel calleeLocals g m f body ma c mh (max bfuel hfuel) (_, bsteps)
            (Nat.le_max_left _ _) hbody]
          simp only [Option.bind_some, if_pos hvalid, if_pos hcaught, if_pos hvalidh]
          rw [progMono context primitive handler structs functions baseAddress topAddress
        bytesInWord hfuel (updatePanValueMap l hvar v) cg cm cf hprog ma c mh
            (max bfuel hfuel) (hra, hrb) (Nat.le_max_right _ _) hh]
          rfl
        · refine ⟨bfuel + 1, (.raised (fun _ => none) cg cm cf e v, argSteps + bsteps), ?_⟩
          rw [evalPanValueFfiCallSteps, hargs]
          simp only [Option.bind_eq_bind, Option.bind_some, hlookup, hbind, hbody, if_pos hvalid, if_neg hcaught]
          rfl

end
end StepCalculus
end Guest
