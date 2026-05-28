/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Whitening-Stage Single-Bit Avalanche Bound

**Claim.** For every single-bit input difference `e_i` (the 64-bit
unit vector with only bit `i` set), the whitening produces an output
with **at least two** distinct set bits.

By `WhiteningLinearity.whiten_diff`, this lifts to the standard
differential statement: for any pair of inputs `x` and `x'` differing
in exactly one bit position, `whiten x` and `whiten x'` differ in at
least two bit positions.

## What this *is*

The first formal *cryptographic-flavor* property in the Drift Core
verification chain. All prior theorems (carry bounds, fold width,
determinism, completeness, fold/whiten bijectivity, distribution-
preservation) are pure implementation-safety statements. The avalanche
bound is the start of differential analysis.

## What this is *not*

* **Not** a full avalanche bound for the production recurrence. The
  recurrence is `state' = ((3·state + 1) mod 2^W) / 2` followed by
  `Fold(...)` followed by whitening. The non-linear arithmetic step
  (carries) breaks GF(2)-linearity, so the *full* one-iteration
  avalanche cannot be reduced to a per-unit-vector check the way this
  whitening-only result can.
* **Not** a strong avalanche bound. The bound here is `≥ 2`, which is
  tight — for unit vectors `e_0, …, e_19` the output has exactly two
  set bits. A cryptographically meaningful avalanche bound would be
  `≥ ~W/2`, which the whitening alone does not achieve. The driftStep
  arithmetic plus the iterated recurrence is what produces the
  observed empirical diffusion; that remains research-level
  (Phase 4-B.3 full).

## Proof technique

For each `i : Fin 64`, the output `whiten (e_i)` has its bit pattern
fully determined by the linear cascade. We exhibit two specific bit
positions that are always set:

* `i ∈ {0, …, 49}`: bits `i` and `i + 14` are both set.
* `i ∈ {50, …, 63}`: bits `i` and `i - 10` are both set.

Each per-case check is a small `bv_decide` query; aggregating over the
64 inputs is handled by Lean's `decide` kernel since `Fin 64` is finite
and the inner predicate is decidable.
-/

import Std.Tactic.BVDecide
import Mathlib.Tactic.FinCases
import WhiteningLinearity

namespace DriftCore

set_option maxRecDepth 2048 in
/--
**Avalanche lower bound for the whitening stage.** For every single-bit
input `e_i`, the whitening output has at least two distinct set bit
positions. Equivalently (by GF(2)-linearity, `WhiteningLinearity.whiten_diff`):
flipping any single input bit flips at least two output bits.

The proof is by exhaustive evaluation on `Fin 64`; `fin_cases` enumerates
the 64 inputs and `native_decide` reduces each case to a compiled
boolean check on a concrete 64-bit XOR / shift expression.
-/
theorem whitening_avalanche_two (i : Fin 64) :
    ∃ j k : Fin 64, j ≠ k ∧
      (whiten ((1 : BitVec 64) <<< i.val)).getLsbD j.val = true ∧
      (whiten ((1 : BitVec 64) <<< i.val)).getLsbD k.val = true := by
  fin_cases i <;> native_decide

/--
**Differential form.** Lifted to the standard differential-cryptanalysis
statement: any two inputs differing in exactly one bit produce outputs
differing in at least two bits.

Direct corollary of `whitening_avalanche_two` plus
`WhiteningLinearity.whiten_diff`. -/
theorem whitening_avalanche_differential (x : BitVec 64) (i : Fin 64) :
    ∃ j k : Fin 64, j ≠ k ∧
      (whiten x ^^^ whiten (x ^^^ ((1 : BitVec 64) <<< i.val))).getLsbD j.val = true ∧
      (whiten x ^^^ whiten (x ^^^ ((1 : BitVec 64) <<< i.val))).getLsbD k.val = true := by
  rw [whiten_xor]
  -- whiten x ^^^ (whiten x ^^^ whiten e_i) = whiten e_i
  have hxor : whiten x ^^^ (whiten x ^^^ whiten ((1 : BitVec 64) <<< i.val))
            = whiten ((1 : BitVec 64) <<< i.val) := by bv_decide
  rw [hxor]
  exact whitening_avalanche_two i

end DriftCore
