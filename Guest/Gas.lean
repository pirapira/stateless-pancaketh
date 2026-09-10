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

/-! ## The second counter

Gas lives in two places. `charge_state_gas` (`guest/src/evm.pnk:249`) draws
from `EV_STATE_GAS_LEFT` and only spills into `EV_GAS_LEFT` when the state-gas
reservoir runs dry, so no measure can be read off `EV_GAS_LEFT` alone. Both of
its paying paths take the **sum** down by exactly the amount charged, which is
what these two lemmas say — one per path, with the guest's own branch condition
as the hypothesis in each case, exactly as in `gas_strictly_decreases`.
-/

/-- `charge_state_gas`'s first path: the reservoir covers the charge, so only
`EV_STATE_GAS_LEFT` moves. -/
theorem state_gas_sum_decreases_reservoir {sgl gl amount : Word}
    (hfits : amount.toNat ≤ sgl.toNat) (hpos : 1 ≤ amount.toNat) :
    (sgl - amount).toNat + gl.toNat < sgl.toNat + gl.toNat := by
  rw [toNat_sub_of_le hfits]
  omega

/-- `charge_state_gas`'s spill path: the reservoir is short, so it empties and
the remainder `amount - sgl` comes out of `EV_GAS_LEFT`. The sum still falls by
exactly `amount`.

`htot` is the guest's `add_sat(sgl, gl) >=+ amount`, restated on `Nat`;
saturation is harmless because a saturated `add_sat` is `2^64 - 1`, which
dominates any `amount`. That is also what rules out a borrow in `gl - rem`. -/
theorem state_gas_sum_decreases_spill {sgl gl amount : Word}
    (hshort : sgl.toNat < amount.toNat)
    (htot : amount.toNat ≤ sgl.toNat + gl.toNat) (hpos : 1 ≤ amount.toNat) :
    (0 : Word).toNat + (gl - (amount - sgl)).toNat < sgl.toNat + gl.toNat := by
  have hrem : (amount - sgl).toNat = amount.toNat - sgl.toNat :=
    toNat_sub_of_le (by omega)
  have hgl : (gl - (amount - sgl)).toNat = gl.toNat - (amount - sgl).toNat :=
    toNat_sub_of_le (by omega)
  rw [hgl, hrem]
  have hzero : (0 : Word).toNat = 0 := rfl
  rw [hzero]
  omega

/-- **`credit_state_gas_refund` moves the sum the wrong way.**
`guest/src/evm.pnk:268` adds `min(amount, spilled)` to `EV_GAS_LEFT` and the
rest of `amount` to `EV_STATE_GAS_LEFT`, so the sum grows by exactly `amount` —
whatever `spilled` is. It is stated here rather than left as prose because it
is the reason `run_frames` cannot simply use the gas sum as its measure; see
`docs/STEP-BOUND.md`. -/
theorem credit_state_gas_refund_increases_sum {gl sgl amount fromGl : Word}
    (hfrom : fromGl.toNat ≤ amount.toNat)
    (hgl : gl.toNat + fromGl.toNat < 2 ^ 64)
    (hsgl : sgl.toNat + (amount.toNat - fromGl.toNat) < 2 ^ 64)
    (hpos : 1 ≤ amount.toNat) :
    sgl.toNat + gl.toNat
      < (sgl + (amount - fromGl)).toNat + (gl + fromGl).toNat := by
  have hrem : (amount - fromGl).toNat = amount.toNat - fromGl.toNat :=
    toNat_sub_of_le hfrom
  have h1 : (gl + fromGl).toNat = gl.toNat + fromGl.toNat := by
    rw [BitVec.toNat_add]
    omega
  have h2 : (sgl + (amount - fromGl)).toNat = sgl.toNat + (amount.toNat - fromGl.toNat) := by
    rw [BitVec.toNat_add, hrem]
    omega
  omega

/-- `Cmp.notLower` is unsigned `>=`: `charge_state_gas`'s reservoir test is
true exactly when the reservoir covers the charge. The mirror of
`cmp_lower_false_of_le`, and the same observation — the guest branches on the
borrow before it subtracts. -/
theorem cmp_notLower_true_of_le {a b : Word} (h : b.toNat ≤ a.toNat) :
    ((RiscV.panRiscVCmp Cmp.notLower a b) != 0) = true := by
  have : ¬ (a < b) := by
    simp only [BitVec.lt_def]
    omega
  simp [RiscV.panRiscVCmp, this]

/-- `Cmp.lower` as a proposition. The `iff` companion to
`cmp_lower_false_of_le`, for the places that need to *read* a taken branch
rather than establish one — `add_sat`'s carry test, for instance. -/
theorem cmp_lower_true_iff {a b : Word} :
    ((RiscV.panRiscVCmp Cmp.lower a b) != 0) = true ↔ a < b := by
  constructor
  · intro h
    by_cases hlt : a < b
    · exact hlt
    · simp [RiscV.panRiscVCmp, hlt] at h
  · intro h
    simp [RiscV.panRiscVCmp, h]

/-! ## `add_sat`

The guest's saturating add, used by `charge_state_gas` to decide whether the
two counters together can cover a charge. Its whole point is that it never
wraps, so the comparison downstream is meaningful.
-/

/-- **`add_sat` saturates exactly when the sum wraps.** `a + b` on `BitVec 64`
wraps, and the guest detects that by `s <+ a` — the sum coming out below one
of its own summands is precisely an unsigned carry. So the value returned is
`a + b` when `a.toNat + b.toNat < 2^64`, and `2^64 - 1` otherwise. -/
theorem add_sat_saturates (a b : Word) :
    (a + b) < a ↔ 2 ^ 64 ≤ a.toNat + b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add, Nat.reducePow]
  omega

/-- No carry: the machine sum is the real sum. -/
theorem add_no_carry {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp only [BitVec.toNat_add, Nat.reducePow]
  omega

/-- What `add_sat` is *for*: its result dominates the true sum, capped at the
word size. This is the only property `charge_state_gas` needs of it — the
`tot >=+ amount` test then rules out a borrow in `gl - rem`. -/
theorem add_sat_ge (a b : Word) :
    min (a.toNat + b.toNat) (2 ^ 64 - 1)
      ≤ (if (a + b) < a then (BitVec.ofNat 64 18446744073709551615) else a + b).toNat := by
  by_cases hc : (a + b) < a
  · rw [if_pos hc]
    have : (BitVec.ofNat 64 18446744073709551615).toNat = 2 ^ 64 - 1 := by decide
    omega
  · rw [if_neg hc]
    have hno : a.toNat + b.toNat < 2 ^ 64 := by
      cases Nat.lt_or_ge (a.toNat + b.toNat) (2 ^ 64) with
      | inl h => exact h
      | inr h => exact absurd ((add_sat_saturates a b).mpr h) hc
    rw [add_no_carry hno]
    omega

/-- `Cmp.notLower` is false exactly when the charge exceeds what is there —
the spill path's entry condition, and the complement of
`cmp_notLower_true_of_le`. -/
theorem cmp_notLower_false_of_lt {a b : Word} (h : a.toNat < b.toNat) :
    ((RiscV.panRiscVCmp Cmp.notLower a b) != 0) = false := by
  have hlt : a < b := by
    simp only [BitVec.lt_def]
    omega
  simp [RiscV.panRiscVCmp, hlt]


end Guest
