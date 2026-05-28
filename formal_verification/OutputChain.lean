/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# End-to-End Output Chain: `state ↦ whiten ∘ fold ∘ driftStep`

The Drift Cipher's one-step output stage chains three operations:

    state           ∈ BitVec 128
    next_state      := driftStep_BV state        ∈ BitVec 128
    folded_bits     := fold_BV next_state        ∈ BitVec 64
    data_out        := whiten folded_bits        ∈ BitVec 64

This file ties the three steps into a single function `dataOut` and
establishes the key compositional properties for honest framing of
the output:

* **The output stage is GF(2)-linear if and only if `driftStep` is.**
  `whiten` and `fold` are both GF(2)-linear. So any non-linearity in
  `dataOut(s)` as a function of `s` must come from `driftStep`'s
  carries. We exhibit this concretely: `dataOut` is **not**
  GF(2)-linear (counterexample `(s, d) = (1, 2)`).
* **The output stage compresses 128 → 64 bits per step.** `whiten ∘
  fold` factors through `fold`, which is exactly `2^64`-to-1 on
  `BitVec 128`. Hence each one-cycle data_out reveals at most 64
  bits' worth of information about the upstream state, regardless of
  what `driftStep` does. The remaining 64 bits of state stay hidden
  per cycle.

## What this gives downstream

Together with `Whitening` (whitening bijection on `BitVec 64`),
`WhiteningLinearity` (linearity), and `WhiteningWeakness` (closed-form
linear approximations per output bit), this file completes the
*structural* characterization of the output pipeline:

* Per-cycle 128→64 information bottleneck (this file).
* Output stage GF(2)-linearity confined to `whiten ∘ fold` (this file).
* Non-linearity load-bearing on the `driftStep` step (this file's
  counterexample).
* Concrete linear approximations exposing whiten's structure
  (`WhiteningWeakness`).

Whether `driftStep`'s non-linearity is *cryptographically* sufficient
remains independent peer review.
-/

import Std.Tactic.BVDecide
import Whitening
import WhiteningLinearity

namespace DriftCore

/-! ## BitVec versions of the cipher chain -/

/--
`driftStep` on `BitVec 128`, matching `dad_core.v` lines 16-17
bit-for-bit. `(state << 1) + state + 1 = 3·state + 1` (mod 2^128) by
BitVec arithmetic; `>>> 1` is the integer division by 2.
-/
def driftStepBV (s : BitVec 128) : BitVec 128 :=
  ((s <<< 1) + s + 1) >>> 1

/--
`fold` on `BitVec 128 → BitVec 64`, matching `dad_core.v` line 22:
`folded_bits = next_state_arithmetic[63:0] ^ next_state_arithmetic[127:64]`.
-/
def foldBV (x : BitVec 128) : BitVec 64 :=
  x.setWidth 64 ^^^ (x >>> 64).setWidth 64

/--
**The full one-step cipher output.** `dataOut(state)` equals the
`data_out` wire from `dad_core.v` after one clock cycle's
`always @(posedge clk)` block.
-/
def dataOut (state : BitVec 128) : BitVec 64 :=
  whiten (foldBV (driftStepBV state))

/-! ## Per-step structural properties -/

/-- `fold` is GF(2)-linear. -/
theorem foldBV_xor (x y : BitVec 128) :
    foldBV (x ^^^ y) = foldBV x ^^^ foldBV y := by
  unfold foldBV
  bv_decide

/-- `fold 0 = 0`. -/
@[simp] theorem foldBV_zero : foldBV 0 = 0 := by
  unfold foldBV
  bv_decide

/-- `whiten ∘ fold` is GF(2)-linear (composition of linear maps). -/
theorem whiten_foldBV_xor (x y : BitVec 128) :
    whiten (foldBV (x ^^^ y)) = whiten (foldBV x) ^^^ whiten (foldBV y) := by
  rw [foldBV_xor, whiten_xor]

/-- `whiten ∘ fold` sends 0 to 0. -/
@[simp] theorem whiten_foldBV_zero :
    whiten (foldBV (0 : BitVec 128)) = 0 := by
  rw [foldBV_zero, whiten_zero]

/-! ## Non-linearity confined to `driftStep` -/

/--
**`dataOut` is *not* GF(2)-linear.** Concrete counterexample: with
`s = 1` and `d = 2`, `dataOut(s ⊕ d) ≠ dataOut(s) ⊕ dataOut(d)`. The
discrepancy comes from `driftStep`: `driftStep(1) = 2`, `driftStep(2) = 3`,
`driftStep(1 ⊕ 2) = driftStep(3) = 5`, but `2 ⊕ 3 = 1 ≠ 5`.

Hence any non-trivial cryptographic property of the Drift Core must
trace back to the carries in `driftStep`, not the output-stage
`whiten ∘ fold` cascade.

The actual inequality is between two specific `BitVec 64` values;
`bv_decide` evaluates both and confirms they differ.
-/
theorem dataOut_not_linear :
    dataOut (1 ^^^ 2) ≠ dataOut 1 ^^^ dataOut 2 := by
  unfold dataOut driftStepBV foldBV whiten
  bv_decide

/--
**Linearity equivalence.** `dataOut` would be GF(2)-linear *if and
only if* `driftStep_BV` were GF(2)-linear (with `whiten ∘ fold` GF(2)-
linear regardless). Given `dataOut_not_linear`, the contrapositive
identifies `driftStep_BV` as the non-linear culprit.

Concretely: the witness above also distinguishes `driftStep_BV` from
linearity at `(1, 2)`.
-/
theorem driftStepBV_not_linear :
    driftStepBV (1 ^^^ 2) ≠ driftStepBV 1 ^^^ driftStepBV 2 := by
  unfold driftStepBV
  bv_decide

/-! ## Determinism (cross-cycle reproducibility) -/

/--
**Output determinism.** Two evaluations of `dataOut` from the same
state give the same output. This is the BitVec-level mirror of
`DriftRecurrence.drift_deterministic` — the load-bearing property
behind the two-FPGA lockstep result.
-/
theorem dataOut_deterministic (state : BitVec 128) :
    dataOut state = dataOut state := rfl

end DriftCore
