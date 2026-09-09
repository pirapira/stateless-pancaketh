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

Most leaf constructors need no rule of their own: `Terminates` for `skip`,
`assign`, `store`, `break`, `continue`, `tick` and `annot` is discharged at the
point of use by exhibiting the one-step run, e.g.
`⟨1, _, by rw [evalPanValueFfiProgSteps, hexp]; rfl⟩`, and their only content is
whether the expressions evaluate.

**Two leaves are not like that**, which an earlier version of this docstring got
wrong: `return` and `raise` each carry a *validity* obligation beyond evaluating
their payload — `panValuePayloadWithinLimit`, and for `raise` also
`panValueExceptionValid` against the program's declared exceptions. The
evaluator answers `none` when either fails. `return_terminates` and
`raise_terminates` name them, since every guest function ends in one and most
error paths raise.

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

/-- **The loop rule.** A loop terminates when an invariant `I` holds on entry
and is preserved, the condition evaluates on every state satisfying `I`, and
the body — whenever entered — terminates and strictly decreases `μ` on the
states it continues from.

The invariant is not decoration. A loop condition mentioning a local can only
be shown to evaluate on states where that local is bound, so without `I` the
rule is unusable on real code: that is what trying it on the guest's
`rlp_be_len` showed. `while_terminates` below is this with `I := True`. -/
theorem while_terminates_inv (cond : Exp α) (body : Prog α)
    (I : (VarName → Option (PanValue α)) → (VarName → Option (PanValue α)) →
      (α → Option (PanValue α)) → FfiState σ → Prop)
    (μ : (VarName → Option (PanValue α)) → (VarName → Option (PanValue α)) →
      (α → Option (PanValue α)) → FfiState σ → Nat)
    (hcond : ∀ l g m f, I l g m f → ∃ n cs, evalPanValueExpCounted structs l g m
      baseAddress topAddress bytesInWord cond ma = some (PanValue.word n, cs))
    (hbody : ∀ l g m f, I l g m f → ∀ n cs,
      evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord cond ma
        = some (PanValue.word n, cs) → (n == 0) = false →
      ∃ fuel result steps,
        evalPanValueFfiProgSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel l g m f body ma c mh = some (result, steps) ∧
        ∀ l' g' m' f', result = .normal l' g' m' f' ∨ result = .continued l' g' m' f' →
          I l' g' m' f' ∧ μ l' g' m' f' < μ l g m f) :
    ∀ l g m f, I l g m f → Terminates context primitive handler structs functions
      baseAddress topAddress bytesInWord ma c mh l g m f (Prog.while cond body) := by
  suffices H : ∀ k l g m f, I l g m f → μ l g m f = k →
      Terminates context primitive handler structs functions baseAddress topAddress
        bytesInWord ma c mh l g m f (Prog.while cond body) by
    intro l g m f hI; exact H _ l g m f hI rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro l g m f hI hmu
    obtain ⟨cv, cs, hc⟩ := hcond l g m f hI
    unfold Terminates
    by_cases hz : (cv == 0) = true
    · refine ⟨1, (PanValueFfiControlResult.normal l g m f, cs + 1), ?_⟩
      rw [evalPanValueFfiProgSteps, hc]
      simp only [Option.bind_eq_bind, Option.bind_some, if_pos hz]
      rfl
    · obtain ⟨bfuel, bres, bsteps, hb, hdec⟩ :=
        hbody l g m f hI cv cs hc (by simpa using hz)
      have hmono : ∀ (j : Nat), bfuel ≤ j →
          evalPanValueFfiProgSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord j l g m f body ma c mh = some (bres, bsteps) :=
        fun j hj => progMono context primitive handler structs functions baseAddress topAddress
            bytesInWord bfuel l g m f body ma c mh j (bres, bsteps) hj hb
      cases bres with
      | normal l' g' m' f' =>
        obtain ⟨hI', hlt'⟩ := hdec l' g' m' f' (Or.inl rfl)
        have hlt : μ l' g' m' f' < k := by rw [← hmu]; exact hlt'
        obtain ⟨lfuel, lres, hl⟩ := ih _ hlt l' g' m' f' hI' rfl
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
        obtain ⟨hI', hlt'⟩ := hdec l' g' m' f' (Or.inr rfl)
        have hlt : μ l' g' m' f' < k := by rw [← hmu]; exact hlt'
        obtain ⟨lfuel, lres, hl⟩ := ih _ hlt l' g' m' f' hI' rfl
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

/-- `while_terminates_inv` with a trivial invariant. -/
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
          baseAddress topAddress bytesInWord fuel l g m f body ma c mh = some (result, steps) ∧
        ∀ l' g' m' f', result = .normal l' g' m' f' ∨ result = .continued l' g' m' f' →
          μ l' g' m' f' < μ l g m f) :
    ∀ l g m f, Terminates context primitive handler structs functions baseAddress
      topAddress bytesInWord ma c mh l g m f (Prog.while cond body) := by
  intro l g m f
  refine while_terminates_inv context primitive handler structs functions baseAddress
    topAddress bytesInWord ma c mh cond body (fun _ _ _ _ => True) μ
    (fun l g m _ _ => hcond l g m) ?_ l g m f trivial
  intro l g m f _ n cs hc hnz
  obtain ⟨fuel, result, steps, hrun, hdec⟩ := hbody l g m f n cs hc hnz
  exact ⟨fuel, result, steps, hrun, fun l' g' m' f' hres => ⟨trivial, hdec l' g' m' f' hres⟩⟩

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


/-- The shape most of the guest's loops have: a counter the body strictly
increases, against a bound. Around 200 of the 257 `while` loops are of this
form (`i <+ n`, `i < cap`, `i < 8`, ...), and this does the truncated
subtraction once instead of per loop — note the counter need not stay below
`N`, since overshooting sends the measure to zero, which is still a decrease.

`counter` is a `Nat`, deliberately. The guest's counters are `BitVec 64` and
its `+` wraps, so "the body increases the counter" is a real obligation, not a
formality: `memzero`'s `while i + 32 <=+ n` does not terminate for
`n ≥ 2^64 - 32`, because `i + 32` wraps to `0` and the counter restarts. Making
the hypothesis an increase in `ℕ` is what forces that to be discharged. -/
theorem while_terminates_of_increasing_counter (cond : Exp α) (body : Prog α)
    (I : (VarName → Option (PanValue α)) → (VarName → Option (PanValue α)) →
      (α → Option (PanValue α)) → FfiState σ → Prop)
    (counter : (VarName → Option (PanValue α)) → Nat) (N : Nat)
    (hcond : ∀ l g m f, I l g m f → ∃ n cs, evalPanValueExpCounted structs l g m
      baseAddress topAddress bytesInWord cond ma = some (PanValue.word n, cs))
    (hentered : ∀ l g m f, I l g m f → ∀ n cs,
      evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord cond ma
        = some (PanValue.word n, cs) → (n == 0) = false → counter l < N)
    (hbody : ∀ l g m f, I l g m f → ∀ n cs,
      evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord cond ma
        = some (PanValue.word n, cs) → (n == 0) = false →
      ∃ fuel result steps,
        evalPanValueFfiProgSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel l g m f body ma c mh = some (result, steps) ∧
        ∀ l' g' m' f', result = .normal l' g' m' f' ∨ result = .continued l' g' m' f' →
          I l' g' m' f' ∧ counter l < counter l') :
    ∀ l g m f, I l g m f → Terminates context primitive handler structs functions
      baseAddress topAddress bytesInWord ma c mh l g m f (Prog.while cond body) := by
  refine while_terminates_inv context primitive handler structs functions baseAddress
    topAddress bytesInWord ma c mh cond body I (fun l _ _ _ => N - counter l) hcond ?_
  intro l g m f hI n cs hc hnz
  obtain ⟨fuel, result, steps, hrun, hstep⟩ := hbody l g m f hI n cs hc hnz
  refine ⟨fuel, result, steps, hrun, fun l' g' m' f' hres => ?_⟩
  obtain ⟨hI', hinc⟩ := hstep l' g' m' f' hres
  have h1 : counter l < N := hentered l g m f hI n cs hc hnz
  exact ⟨hI', by omega⟩

/-- `return`: the payload evaluates and is within the limit. -/
theorem return_terminates (value : Exp α)
    (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)) (f : FfiState σ)
    (v : PanValue α) (vs : Nat)
    (hvalue : evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord value ma = some (v, vs))
    (hlimit : panValuePayloadWithinLimit structs v = true) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh l g m f (Prog.return value) := by
  refine ⟨1, (PanValueFfiControlResult.returned (fun _ => none) g m f [v], vs + 1), ?_⟩
  rw [evalPanValueFfiProgSteps, hvalue]
  simp only [Option.bind_eq_bind, Option.bind_some, if_pos hlimit]
  rfl

/-- `raise`: the payload evaluates, the exception is declared with a matching
shape, and the payload is within the limit. -/
theorem raise_terminates (exception : ExceptionId) (value : Exp α)
    (l g : VarName → Option (PanValue α)) (m : α → Option (PanValue α)) (f : FfiState σ)
    (v : PanValue α) (vs : Nat)
    (hvalue : evalPanValueExpCounted structs l g m baseAddress topAddress bytesInWord value ma = some (v, vs))
    (hvalid : (panValueExceptionValid structs c exception v &&
      panValuePayloadWithinLimit structs v) = true) :
    Terminates context primitive handler structs functions baseAddress topAddress
      bytesInWord ma c mh l g m f (Prog.raise exception value) := by
  refine ⟨1, (PanValueFfiControlResult.raised (fun _ => none) g m f exception v, vs + 1), ?_⟩
  rw [evalPanValueFfiProgSteps, hvalue]
  simp only [Option.bind_eq_bind, Option.bind_some, if_pos hvalid]
  rfl

end
end StepCalculus
end Guest
