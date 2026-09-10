import Guest.Basic
import Flapjack.RiscV.PanMemory

/-!
# Gas arithmetic

The guest's gas counters are `BitVec 64` words, and it charges with `-`, which
wraps. Everything the `run_frames` measure needs about a charge is here, and it
is all conditional on the charge fitting — which is exactly what the guest's own
`gl <+ amount` test decides before it stores.

* `toNat_sub_of_le` — unsigned subtraction that does not borrow is subtraction.
* `gas_strictly_decreases` — the measure step: charging at least one gas moves
  `toNat` of the counter strictly down.
* `cmp_lower_false_of_le` — `Cmp.lower` is unsigned `<`, so the guest's
  out-of-gas test is false exactly when the charge fits. This is what turns the
  branch condition into the arithmetic side condition above.

Keeping these separate from the evaluator matters: the wrap-around hypothesis is
the *interesting* half of every gas argument, and it should be visible rather
than buried in a proof about `Prog.store`.
-/

open Flapjack

namespace Guest

/-- Unsigned subtraction with no borrow. -/
theorem toNat_sub_of_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have hb := b.isLt
  simp [BitVec.toNat_sub]
  omega

/-- **Charging at least one gas strictly decreases the counter**, provided the
charge does not exceed what is left. Without the `hle` hypothesis this is false:
`0 - 1` is `2^64 - 1`, and the measure would go *up*. -/
theorem gas_strictly_decreases {gl amount : BitVec 64}
    (hle : amount.toNat ≤ gl.toNat) (hpos : 1 ≤ amount.toNat) :
    (gl - amount).toNat < gl.toNat := by
  rw [toNat_sub_of_le hle]
  omega

/-- `Cmp.lower` is unsigned `<`: the guest's out-of-gas test is false exactly
when the charge fits. -/
theorem cmp_lower_false_of_le {a b : Word} (h : b.toNat ≤ a.toNat) :
    ((RiscV.panRiscVCmp Cmp.lower a b) != 0) = false := by
  have : ¬ (a < b) := by
    simp only [BitVec.lt_def]
    omega
  simp [RiscV.panRiscVCmp, this]

end Guest
