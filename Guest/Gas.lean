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

/-- The value `min` yields. Unsigned, like the guest's `<+`, and the pivot of
the credit path: `credit_state_gas_refund` gives back `min(amount, spilled)`
from the spill reservoir and the rest from the state reservoir. -/
def minOf (a b : Word) : Word := if a < b then a else b

theorem minOf_le_left (a b : Word) : (minOf a b).toNat ≤ a.toNat := by
  unfold minOf
  by_cases h : a < b
  · rw [if_pos h]; omega
  · rw [if_neg h]
    simp only [BitVec.lt_def] at h
    omega

theorem minOf_le_right (a b : Word) : (minOf a b).toNat ≤ b.toNat := by
  unfold minOf
  by_cases h : a < b
  · rw [if_pos h]
    simp only [BitVec.lt_def] at h
    omega
  · rw [if_neg h]; omega

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

/-- The credit with its argument taken at the guest's own `min`, so the
no-overflow side conditions are all that is left. `hfrom` is discharged by
`minOf_le_left`: the guest never gives back more than it was asked for. -/
theorem credit_state_gas_refund_increases_sum_min {gl sgl amount spilled : Word}
    (hgl : gl.toNat + (minOf amount spilled).toNat < 2 ^ 64)
    (hsgl : sgl.toNat + (amount.toNat - (minOf amount spilled).toNat) < 2 ^ 64)
    (hpos : 1 ≤ amount.toNat) :
    sgl.toNat + gl.toNat
      < (sgl + (amount - minOf amount spilled)).toNat + (gl + minOf amount spilled).toNat :=
  credit_state_gas_refund_increases_sum (minOf_le_left amount spilled) hgl hsgl hpos

/-- **The half of the credit that *is* conserved.** Whatever goes back to
`EV_GAS_LEFT` comes out of `EV_STATE_GAS_SPILLED`, exactly. So the credit only
breaks the measure by the part it routes to the state reservoir --- the
`amount - min(amount, spilled)` half --- and the spill counter alone is a
sound (non-increasing) component. -/
theorem credit_state_gas_refund_conserves_spill (amount spilled : Word) :
    (spilled - minOf amount spilled).toNat + (minOf amount spilled).toNat
      = spilled.toNat := by
  have hle := minOf_le_right amount spilled
  rw [toNat_sub_of_le hle]
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

/-- What `add_sat` computes: the true sum, or `WORD_MAX` if that carried. The
guest's own overflow test is `s <+ a`, which `add_sat_saturates` shows detects
exactly the carry. -/
def addSatOf (a b : Word) : Word :=
  if (a + b) < a then BitVec.ofNat 64 18446744073709551615 else a + b

/-- What `add_sat` is *for*: its result dominates the true sum, capped at the
word size. This is the only property `charge_state_gas` needs of it — the
`tot >=+ amount` test then rules out a borrow in `gl - rem`. -/
theorem add_sat_ge (a b : Word) :
    min (a.toNat + b.toNat) (2 ^ 64 - 1) ≤ (addSatOf a b).toNat := by
  unfold addSatOf
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

/-! ## Positivity of a computed charge

`charge_gas_decreases_gas` needs `1 <= amount`. `lake exe opcode-census`
settles that for 70 of the 87 handlers because they charge a literal; the
remaining 17 *compute* their charge, and every one of them has one of two
shapes:

* `add_sat(base + per * w, x.0)` --- `op_keccak`, `op_extcodecopy`,
  `op_returndatacopy`, `op_mcopy`, `op_log`;
* a plain sum whose first summand is a function result --- `op_balance`,
  `op_extcodesize`, `op_extcodehash`, all three `access_gas_cost(addr)`.

Both reduce to **the base cost survives**, which is what these three lemmas
say. What they do not settle is the *range* facts about the inputs, which are
per-handler and belong with each handler. -/

/-- **Saturating addition never loses its left summand.** So a charge of the
form `add_sat(base, extra)` is at least `base`, whatever `extra` is and
whether or not the sum carried --- which is exactly the point of `add_sat`. -/
theorem add_sat_ge_left (a b : Word) : a.toNat ≤ (addSatOf a b).toNat := by
  have h := add_sat_ge a b
  have ha : a.toNat < 2 ^ 64 := a.isLt
  omega

/-- **A positive base cost survives `add_sat`.** The `1 <= amount` half of the
census claim, for every handler that charges through `add_sat`. -/
theorem add_sat_pos {a b : Word} (h : 1 ≤ a.toNat) : 1 ≤ (addSatOf a b).toNat := by
  have := add_sat_ge_left a b
  omega

/-- **A positive base cost survives a plain `+`, given no carry.** Unlike
`add_sat_pos` this one has a side condition, because a plain `+` wraps: with
`a = 1` and `b = 2^64 - 1` the sum is `0`. That is the whole reason the guest
uses `add_sat` wherever the second summand is attacker-influenced. -/
theorem add_pos_of_no_carry {a b : Word} (hpos : 1 ≤ a.toNat)
    (hno : a.toNat + b.toNat < 2 ^ 64) : 1 ≤ (a + b).toNat := by
  rw [add_no_carry hno]
  omega

/-- **A `base + per * count` charge is positive when the base is.** The shape
of `op_keccak`'s `G_KECCAK256_BASE + G_KECCAK256_PER_WORD * w` and
`op_exp`'s `G_EXP_BASE + G_EXP_PER_BYTE * nb`, before `add_sat` sees it. The
side condition is a genuine obligation, not bookkeeping: `per * count` wraps
for a large enough `count`, and the bound on `count` is what each handler has
to supply about its own input. -/
theorem linear_cost_pos {base per count : Word} (hbase : 1 ≤ base.toNat)
    (hfits : base.toNat + per.toNat * count.toNat < 2 ^ 64) :
    1 ≤ (base + per * count).toNat := by
  have hmul : (per * count).toNat = per.toNat * count.toNat := by
    rw [BitVec.toNat_mul]
    omega
  rw [BitVec.toNat_add, hmul]
  omega

/-- `Cmp.notEqual` as a proposition: the guest's `w != 0` test. -/
theorem cmp_notEqual_true_iff {a b : Word} :
    ((RiscV.panRiscVCmp Cmp.notEqual a b) != 0) = true ↔ a ≠ b := by
  simp [RiscV.panRiscVCmp]
  constructor
  · intro h hab; simp [hab] at h
  · intro h; simp [h]

/-! ### The word count is bounded by its own shift

`words_of n` is `ceil32(n) >>> 5`, so **whatever it is handed, its result is
below `2^59`** --- no fact about `ceil32` is needed, and in particular no
no-wrap assumption about the `n + 31` inside it. That is what makes the
word-metered charges positive *unconditionally*, which was not obvious before
looking: the obvious route is to bound `n`, and `n` is attacker-controlled. -/

theorem shiftRight_lt (x : Word) (n : Nat) (h : n ≤ 64) :
    (x >>> n).toNat < 2 ^ (64 - n) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hsplit : (2 : Nat) ^ 64 = 2 ^ n * 2 ^ (64 - n) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  refine Nat.div_lt_of_lt_mul ?_
  rw [← hsplit]
  exact hx

theorem shiftRight_five_lt (x : Word) : (x >>> 5).toNat < 2 ^ 59 :=
  shiftRight_lt x 5 (by omega)

/-- **The word-metered base cost is positive.** `base + perWord * words_of(n)`,
for any `base` that is positive and not absurdly large and any small
per-word rate. Covers `op_keccak`'s `30 + 6 * w`, the copy handlers' `3 + 3 * w`
and `op_extcodecopy`'s `acc + 100 + 3 * w`. -/
theorem word_metered_cost_pos {base perWord x : Word}
    (hpos : 1 ≤ base.toNat) (hsmall : base.toNat < 2 ^ 62) (hper : perWord.toNat ≤ 8) :
    1 ≤ (base + perWord * (x >>> 5)).toNat := by
  have hw := shiftRight_five_lt x
  refine linear_cost_pos hpos ?_
  have : perWord.toNat * (x >>> 5).toNat ≤ 8 * 2 ^ 59 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- ... and it survives the `add_sat` against the memory-extension cost, which
is the form the handlers actually charge. -/
theorem word_metered_charge_pos {base perWord x extra : Word}
    (hpos : 1 ≤ base.toNat) (hsmall : base.toNat < 2 ^ 62) (hper : perWord.toNat ≤ 8) :
    1 ≤ (addSatOf (base + perWord * (x >>> 5)) extra).toNat :=
  add_sat_pos (word_metered_cost_pos hpos hsmall hper)

/-- `op_keccak`: `add_sat(G_KECCAK256_BASE + G_KECCAK256_PER_WORD * w, x.0)`,
positive with no side condition at all. -/
theorem keccak_charge_pos (x extra : Word) :
    1 ≤ (addSatOf (BitVec.ofNat 64 30 + BitVec.ofNat 64 6 * (x >>> 5)) extra).toNat :=
  word_metered_charge_pos (by decide) (by decide) (by decide)

/-- `op_returndatacopy` and `op_mcopy`:
`add_sat(3 + G_COPY_PER_WORD * w, x.0)`, likewise unconditional. -/
theorem copy_charge_pos (x extra : Word) :
    1 ≤ (addSatOf (BitVec.ofNat 64 3 + BitVec.ofNat 64 3 * (x >>> 5)) extra).toNat :=
  word_metered_charge_pos (by decide) (by decide) (by decide)

/-- `op_extcodecopy`: the base is `acc + G_WARM_ACCESS`, with `acc` coming from
`access_gas_cost`, so the bound on it comes from that function rather than
from a literal. -/
theorem extcodecopy_charge_pos {acc x extra : Word} (hacc : acc.toNat ≤ 3000) :
    1 ≤ (addSatOf (acc + BitVec.ofNat 64 100 + BitVec.ofNat 64 3 * (x >>> 5))
      extra).toNat := by
  refine word_metered_charge_pos ?_ ?_ (by decide)
  · rw [BitVec.toNat_add]
    have : (BitVec.ofNat 64 100 : Word).toNat = 100 := by decide
    omega
  · rw [BitVec.toNat_add]
    have : (BitVec.ofNat 64 100 : Word).toNat = 100 := by decide
    omega

/-- `op_log`: `add_sat(G_LOG_BASE + G_LOG_TOPIC * ntopics, x.0)`. `ntopics` is
read off the opcode byte, so its bound is a fact about `op_dispatch` rather
than about arithmetic --- hence the hypothesis. -/
theorem log_charge_pos {ntopics extra : Word} (h : ntopics.toNat ≤ 4) :
    1 ≤ (addSatOf (BitVec.ofNat 64 375 + BitVec.ofNat 64 375 * ntopics) extra).toNat := by
  refine add_sat_pos (linear_cost_pos (by decide) ?_)
  have h375 : (BitVec.ofNat 64 375 : Word).toNat = 375 := by decide
  have : (375 : Nat) * ntopics.toNat ≤ 375 * 4 := Nat.mul_le_mul_left _ h
  rw [h375]
  omega

/-- `op_exp`: `G_EXP_BASE + G_EXP_PER_BYTE * nb`, with **no** `add_sat` --- so
unlike the copy handlers this one genuinely needs its input bounded, and
`nb <= 32` is a fact about `u256_byte_length`. -/
theorem exp_charge_pos {nb : Word} (h : nb.toNat ≤ 32) :
    1 ≤ (BitVec.ofNat 64 10 + BitVec.ofNat 64 50 * nb).toNat := by
  refine linear_cost_pos (by decide) ?_
  have h10 : (BitVec.ofNat 64 10 : Word).toNat = 10 := by decide
  have h50 : (BitVec.ofNat 64 50 : Word).toNat = 50 := by decide
  have : (50 : Nat) * nb.toNat ≤ 50 * 32 := Nat.mul_le_mul_left _ h
  rw [h10, h50]
  omega

/-- `op_extcodesize`: `access_gas_cost(addr) + G_WARM_ACCESS`. -/
theorem access_plus_warm_pos {acc : Word} (hpos : 1 ≤ acc.toNat)
    (hsmall : acc.toNat ≤ 3000) : 1 ≤ (acc + BitVec.ofNat 64 100).toNat := by
  refine add_pos_of_no_carry hpos ?_
  have : (BitVec.ofNat 64 100 : Word).toNat = 100 := by decide
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
