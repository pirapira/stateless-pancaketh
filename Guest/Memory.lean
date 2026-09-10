import Guest.Model

/-!
# A memory layer for the guest's word accesses

`Guest.FunctionTermination` could not discharge `charge_gas`'s load and store
obligations because `Exp.load` and `Prog.store` bottom out in
`panValueFlatLoad` and `panValueStoreWithAccess`, about which flapjack proves
nothing. This module supplies the word-shaped cases, which is what the guest
uses everywhere `lds 1` / `st` appear.

* `panValueFlatLoad_one`, `panValueStoreWithAccess_word` — generic: a
  `Shape.one` load is exactly one underlying word read, a `.word` store exactly
  one underlying word write.
* `guest_readWord`, `guest_storeWord`, `guest_store_word_total` — the same
  under `Guest.guestMemoryAccess`.

The asymmetry in the last of these is worth stating plainly, because it is the
one that bit before: **a word store always succeeds.** The guest's access model
is `panValueMemoryAccessOfModel` with the default `domain := fun _ => true`, so
`st` *extends* the memory map rather than failing outside it. Byte accesses do
not — `ld8`/`st8` go through the model and fail on an absent cell — and that
asymmetry is exactly why heap exhaustion turned into an evaluation failure
rather than a clean stop before PR #76.

Still missing for a function's obligations to be discharged from state alone:
an expression layer, giving `Exp.var`, `Exp.const` and `Exp.op` under the
access model's `wordOp`.
-/

open Flapjack
namespace Guest

section Generic
variable {α : Type} [BEq α] [Add α]

/-- Reading a one-word shape is exactly the underlying word read. -/
theorem panValueFlatLoad_one (structs : StructContext)
    (memory : α → Option (PanValue α)) (bytesInWord address : α)
    (ma : Option (PanValueMemoryAccess α)) :
    panValueFlatLoad structs memory bytesInWord address Shape.one ma =
      (panValueFlatReadWord memory bytesInWord ma address).map PanValue.word := by
  unfold panValueFlatLoad
  simp [isWfShape, panValueFlatLoadFuel]

/-- Storing a one-word value is exactly one underlying word write. -/
theorem panValueStoreWithAccess_word (memory : α → Option (PanValue α))
    (bytesInWord address value : α) (access : PanValueMemoryAccess α) :
    panValueStoreWithAccess memory bytesInWord address (PanValue.word value) (some access) =
      access.storeWord access.domain memory bytesInWord address value := by
  unfold panValueStoreWithAccess
  simp [panValueFlatWords, panValueFlatWordsFuel, panValueFlatStoreWords]

end Generic

/-- A word load under the guest's access model succeeds exactly when the cell
holds a word. -/
theorem guest_readWord (memory : Memory) (bytesInWord address : Word) :
    panValueFlatReadWord memory bytesInWord (some guestMemoryAccess) address =
      match memory address with
      | some (.word v) => some v
      | _ => none := by
  simp only [panValueFlatReadWord, guestMemoryAccess, panValueMemoryAccessOfModel]
  cases memory address with
  | none => rfl
  | some v => cases v <;> rfl

/-- A word store under the guest's access model always succeeds — the domain is
`fun _ => true`, so a word store *extends* the map rather than failing outside
it. (Byte accesses do not: `ld8`/`st8` go through the model and fail on an
absent cell. That asymmetry is what made heap exhaustion an evaluation failure
before PR #76.) -/
theorem guest_storeWord (memory : Memory) (bytesInWord address value : Word) :
    guestMemoryAccess.storeWord guestMemoryAccess.domain memory bytesInWord address value =
      some (fun current => if current == address then some (.word value) else memory current) := by
  simp [guestMemoryAccess, panValueMemoryAccessOfModel]

/-- Combining: storing a word is total, and reads it back. -/
theorem guest_store_word_total (memory : Memory) (bytesInWord address value : Word) :
    panValueStoreWithAccess memory bytesInWord address (PanValue.word value)
      (some guestMemoryAccess) =
      some (fun current => if current == address then some (.word value) else memory current) := by
  rw [panValueStoreWithAccess_word]
  exact guest_storeWord memory bytesInWord address value

end Guest
