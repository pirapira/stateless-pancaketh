import Lean
import Flapjack.Language

/-!
Decidable equality for flapjack's Pancake syntax, so that the parse result can
be compared with the committed AST by evaluation (`Guest.AstParse`).

`Shape`, `Exp` and `Prog` are nested inductives (through `List`, `Prod` and
`Option`), which the `DecidableEq` deriving handler refuses. The instances
below follow the shape of the derived code by hand: a `ctorIdx` comparison
first, then core's `casesOnSameCtor` matcher, which has one alternative per
constructor, so that only matching constructor pairs need to be written out.
-/

-- Core has no `DecidableEq` for `Except`; needed to compare parse results.
deriving instance DecidableEq for Except

open Lean Meta in
run_meta mkCasesOnSameCtor `Flapjack.Shape.match_on_same_ctor `Flapjack.Shape
open Lean Meta in
run_meta mkCasesOnSameCtor `Flapjack.Exp.match_on_same_ctor `Flapjack.Exp
open Lean Meta in
run_meta mkCasesOnSameCtor `Flapjack.Prog.match_on_same_ctor `Flapjack.Prog

namespace Flapjack

/-! ### `Shape` -/

mutual
def Shape.decEq (a b : Shape) : Decidable (a = b) :=
  match Nat.decEq a.ctorIdx b.ctorIdx with
  | .isFalse h => isFalse (fun h' => h (congrArg Shape.ctorIdx h'))
  | .isTrue h =>
    Shape.match_on_same_ctor (motive := fun a b _ => Decidable (a = b)) a b h
      (fun _ => isTrue rfl)
      (fun xs ys =>
        haveI := Shape.decEqList xs ys
        decidable_of_iff (xs = ys) ⟨by rintro rfl; rfl, Shape.comb.inj⟩)
      (fun x y => decidable_of_iff (x = y) ⟨by rintro rfl; rfl, Shape.named.inj⟩)
termination_by structural a

def Shape.decEqList : (xs ys : List Shape) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      haveI := Shape.decEq x y
      haveI := Shape.decEqList xs ys
      decidable_of_iff (x = y ∧ xs = ys) ⟨by rintro ⟨rfl, rfl⟩; rfl, List.cons.inj⟩
  | [], _ :: _ => isFalse (by intro h; injection h)
  | _ :: _, [] => isFalse (by intro h; injection h)
termination_by structural xs _ => xs
end

instance : DecidableEq Shape := Shape.decEq

/-! ### `Exp` -/

section Exp
variable {α : Type u} [DecidableEq α]

mutual
def Exp.decEq (a b : Exp α) : Decidable (a = b) :=
  match Nat.decEq a.ctorIdx b.ctorIdx with
  | .isFalse h => isFalse (fun h' => h (congrArg Exp.ctorIdx h'))
  | .isTrue h =>
    Exp.match_on_same_ctor (motive := fun a b _ => Decidable (a = b)) a b h
      (fun x y => decidable_of_iff (x = y) ⟨by rintro rfl; rfl, Exp.const.inj⟩)
      (fun k x k' y =>
        decidable_of_iff (k = k' ∧ x = y) ⟨by rintro ⟨rfl, rfl⟩; rfl, Exp.var.inj⟩)
      (fun xs ys =>
        haveI := Exp.decEqList xs ys
        decidable_of_iff (xs = ys) ⟨by rintro rfl; rfl, Exp.rStruct.inj⟩)
      (fun i x j y =>
        haveI := Exp.decEq x y
        decidable_of_iff (i = j ∧ x = y) ⟨by rintro ⟨rfl, rfl⟩; rfl, Exp.rField.inj⟩)
      (fun n xs n' ys =>
        haveI := Exp.decEqFields xs ys
        decidable_of_iff (n = n' ∧ xs = ys) ⟨by rintro ⟨rfl, rfl⟩; rfl, Exp.nStruct.inj⟩)
      (fun n x n' y =>
        haveI := Exp.decEq x y
        decidable_of_iff (n = n' ∧ x = y) ⟨by rintro ⟨rfl, rfl⟩; rfl, Exp.nField.inj⟩)
      (fun s x s' y =>
        haveI := Exp.decEq x y
        decidable_of_iff (s = s' ∧ x = y) ⟨by rintro ⟨rfl, rfl⟩; rfl, Exp.load.inj⟩)
      (fun x y =>
        haveI := Exp.decEq x y
        decidable_of_iff (x = y) ⟨by rintro rfl; rfl, Exp.load32.inj⟩)
      (fun x y =>
        haveI := Exp.decEq x y
        decidable_of_iff (x = y) ⟨by rintro rfl; rfl, Exp.loadByte.inj⟩)
      (fun o xs o' ys =>
        haveI := Exp.decEqList xs ys
        decidable_of_iff (o = o' ∧ xs = ys) ⟨by rintro ⟨rfl, rfl⟩; rfl, Exp.op.inj⟩)
      (fun o xs o' ys =>
        haveI := Exp.decEqList xs ys
        decidable_of_iff (o = o' ∧ xs = ys) ⟨by rintro ⟨rfl, rfl⟩; rfl, Exp.panOp.inj⟩)
      (fun c l r c' l' r' =>
        haveI := Exp.decEq l l'
        haveI := Exp.decEq r r'
        decidable_of_iff (c = c' ∧ l = l' ∧ r = r')
          ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl, Exp.cmp.inj⟩)
      (fun s l r s' l' r' =>
        haveI := Exp.decEq l l'
        haveI := Exp.decEq r r'
        decidable_of_iff (s = s' ∧ l = l' ∧ r = r')
          ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl, Exp.shift.inj⟩)
      (fun _ => isTrue rfl)
      (fun _ => isTrue rfl)
      (fun _ => isTrue rfl)
termination_by structural a

def Exp.decEqList : (xs ys : List (Exp α)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      haveI := Exp.decEq x y
      haveI := Exp.decEqList xs ys
      decidable_of_iff (x = y ∧ xs = ys) ⟨by rintro ⟨rfl, rfl⟩; rfl, List.cons.inj⟩
  | [], _ :: _ => isFalse (by intro h; injection h)
  | _ :: _, [] => isFalse (by intro h; injection h)
termination_by structural xs _ => xs

def Exp.decEqFields : (xs ys : List (FieldName × Exp α)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | (f, x) :: xs, (g, y) :: ys =>
      haveI := Exp.decEq x y
      haveI := Exp.decEqFields xs ys
      decidable_of_iff (f = g ∧ x = y ∧ xs = ys)
        ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl,
         fun h => by
           injection h with h1 h2
           injection h1 with h3 h4
           exact ⟨h3, h4, h2⟩⟩
  | [], _ :: _ => isFalse (by intro h; injection h)
  | _ :: _, [] => isFalse (by intro h; injection h)
termination_by structural xs _ => xs
end

instance : DecidableEq (Exp α) := Exp.decEq

end Exp

/-! ### `Prog` -/

section Prog
variable {α : Type u} [DecidableEq α]

mutual
def Prog.decEq (a b : Prog α) : Decidable (a = b) :=
  match Nat.decEq a.ctorIdx b.ctorIdx with
  | .isFalse h => isFalse (fun h' => h (congrArg Prog.ctorIdx h'))
  | .isTrue h =>
    Prog.match_on_same_ctor (motive := fun a b _ => Decidable (a = b)) a b h
      (fun _ => isTrue rfl)
      (fun n s v p n' s' v' p' =>
        haveI := Prog.decEq p p'
        decidable_of_iff (n = n' ∧ s = s' ∧ v = v' ∧ p = p')
          ⟨by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl, Prog.dec.inj⟩)
      (fun k n v k' n' v' =>
        decidable_of_iff (k = k' ∧ n = n' ∧ v = v')
          ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl, Prog.assign.inj⟩)
      (fun n o xs n' o' xs' =>
        decidable_of_iff (n = n' ∧ o = o' ∧ xs = xs')
          ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl, Prog.primitive.inj⟩)
      (fun a v a' v' =>
        decidable_of_iff (a = a' ∧ v = v') ⟨by rintro ⟨rfl, rfl⟩; rfl, Prog.store.inj⟩)
      (fun a v a' v' =>
        decidable_of_iff (a = a' ∧ v = v') ⟨by rintro ⟨rfl, rfl⟩; rfl, Prog.store32.inj⟩)
      (fun a v a' v' =>
        decidable_of_iff (a = a' ∧ v = v') ⟨by rintro ⟨rfl, rfl⟩; rfl, Prog.storeByte.inj⟩)
      (fun p q p' q' =>
        haveI := Prog.decEq p p'
        haveI := Prog.decEq q q'
        decidable_of_iff (p = p' ∧ q = q') ⟨by rintro ⟨rfl, rfl⟩; rfl, Prog.seq.inj⟩)
      (fun c p q c' p' q' =>
        haveI := Prog.decEq p p'
        haveI := Prog.decEq q q'
        decidable_of_iff (c = c' ∧ p = p' ∧ q = q')
          ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl, Prog.ite.inj⟩)
      (fun c p c' p' =>
        haveI := Prog.decEq p p'
        decidable_of_iff (c = c' ∧ p = p') ⟨by rintro ⟨rfl, rfl⟩; rfl, Prog.while.inj⟩)
      (fun _ => isTrue rfl)
      (fun _ => isTrue rfl)
      (fun i n xs i' n' xs' =>
        haveI := Prog.decEqCallInfo i i'
        decidable_of_iff (i = i' ∧ n = n' ∧ xs = xs')
          ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl, Prog.call.inj⟩)
      (fun n s f xs p n' s' f' xs' p' =>
        haveI := Prog.decEq p p'
        decidable_of_iff (n = n' ∧ s = s' ∧ f = f' ∧ xs = xs' ∧ p = p')
          ⟨by rintro ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl, Prog.decCall.inj⟩)
      (fun f c cl a al f' c' cl' a' al' =>
        decidable_of_iff (f = f' ∧ c = c' ∧ cl = cl' ∧ a = a' ∧ al = al')
          ⟨by rintro ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl, Prog.extCall.inj⟩)
      (fun e v e' v' =>
        decidable_of_iff (e = e' ∧ v = v') ⟨by rintro ⟨rfl, rfl⟩; rfl, Prog.raise.inj⟩)
      (fun v v' => decidable_of_iff (v = v') ⟨by rintro rfl; rfl, Prog.return.inj⟩)
      (fun s k n a s' k' n' a' =>
        decidable_of_iff (s = s' ∧ k = k' ∧ n = n' ∧ a = a')
          ⟨by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl, Prog.shMemLoad.inj⟩)
      (fun s a v s' a' v' =>
        decidable_of_iff (s = s' ∧ a = a' ∧ v = v')
          ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl, Prog.shMemStore.inj⟩)
      (fun _ => isTrue rfl)
      (fun t x t' x' =>
        decidable_of_iff (t = t' ∧ x = x') ⟨by rintro ⟨rfl, rfl⟩; rfl, Prog.annot.inj⟩)
termination_by structural a

def Prog.decEqCallInfo :
    (i i' : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α))) →
      Decidable (i = i')
  | none, none => isTrue rfl
  | some (r, h), some (r', h') =>
      haveI := Prog.decEqHandler h h'
      decidable_of_iff (r = r' ∧ h = h')
        ⟨by rintro ⟨rfl, rfl⟩; rfl,
         fun e => by
           injection e with e1
           injection e1 with e2 e3
           exact ⟨e2, e3⟩⟩
  | none, some _ => isFalse (by intro h; injection h)
  | some _, none => isFalse (by intro h; injection h)
termination_by structural i _ => i

def Prog.decEqHandler : (h h' : Option (ExceptionId × VarName × Prog α)) → Decidable (h = h')
  | none, none => isTrue rfl
  | some (e, v, p), some (e', v', p') =>
      haveI := Prog.decEq p p'
      decidable_of_iff (e = e' ∧ v = v' ∧ p = p')
        ⟨by rintro ⟨rfl, rfl, rfl⟩; rfl,
         fun x => by
           injection x with x1
           injection x1 with x2 x3
           injection x3 with x4 x5
           exact ⟨x2, x4, x5⟩⟩
  | none, some _ => isFalse (by intro h; injection h)
  | some _, none => isFalse (by intro h; injection h)
termination_by structural h _ => h
end

instance : DecidableEq (Prog α) := Prog.decEq

end Prog

/-! ### `FunDecl` and `Decl` -/

deriving instance DecidableEq for FunDecl
deriving instance DecidableEq for Decl

end Flapjack
