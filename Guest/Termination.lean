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

Not here yet: the leaf constructors (`skip`, `assign`, `store`, `return`,
`raise`, `break`, `continue`, `tick`, `annot`), which terminate as soon as
their expressions evaluate, and the call evaluator's own rule. Those are
mechanical; the measures for the guest's loops are the real remaining work, and
`docs/STEP-BOUND.md` records which ones are substantive.
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

end
end StepCalculus
end Guest
