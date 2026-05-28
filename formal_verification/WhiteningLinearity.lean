/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Whitening Cascade is GF(2)-Linear

Each step of the production whitening is of the form `x ↦ x ⊕ L(x)`
where `L` is a single shift (right or left). Shift and XOR are both
GF(2)-linear, so each step is GF(2)-linear; composition of GF(2)-linear
maps is GF(2)-linear; hence `whiten` is GF(2)-linear.

## Result

`whiten_xor` — `whiten (x ⊕ y) = whiten x ⊕ whiten y`.

`whiten_zero` — `whiten 0 = 0`. Standard consequence (and a cheap
sanity check for any linearity claim).

## Why this matters

GF(2)-linearity reduces *every* differential question about the
whitening to a question about `whiten` applied to the input difference.
In particular, the avalanche property — "single-bit input difference
produces at least `k` output bit differences" — is exactly the claim
"`popcount(whiten(eᵢ)) ≥ k` for every unit vector `eᵢ`" once linearity
is in hand. See `Avalanche.lean`.

## Caveat

GF(2)-linearity is an *implementation* property. Cryptographic ciphers
typically destroy GF(2)-linearity on purpose (S-boxes, modular addition
in ARX) precisely because it makes differential and linear cryptanalysis
easier. The Drift Core's *full* recurrence is non-linear (the affine
`3·s + 1 mod 2^W` step has carries that break GF(2)-linearity), but the
output-stage whitening alone is linear.
-/

import Std.Tactic.BVDecide
import Whitening

namespace DriftCore

/--
**The whitening is GF(2)-linear.** `whiten (x ⊕ y) = whiten x ⊕ whiten y`
for all 64-bit inputs.

Discharged by `bv_decide` (Std SAT-backed BitVec decision procedure) in
under a second; the underlying SAT instance is small because both sides
unfold to a fixed XOR/shift expression in `x` and `y`.
-/
theorem whiten_xor (x y : BitVec 64) : whiten (x ^^^ y) = whiten x ^^^ whiten y := by
  unfold whiten
  bv_decide

/-- **The whitening fixes zero.** Direct consequence of GF(2)-linearity
(`whiten 0 = whiten (0 ⊕ 0) = whiten 0 ⊕ whiten 0`, so `whiten 0 = 0`).
Proved directly here via `bv_decide` for speed. -/
@[simp] theorem whiten_zero : whiten (0 : BitVec 64) = 0 := by
  unfold whiten
  bv_decide

/--
**Differential propagation.** A consequence of linearity stated in the
differential cryptanalysis form: for any two inputs `x` and `x'`, the
output difference equals the whitening of the input difference.

This is the key reduction used in `Avalanche.lean` to convert
"single-bit input flip → ≥ k output flips" into the per-bit claim
"`popcount(whiten(eᵢ)) ≥ k`."
-/
theorem whiten_diff (x x' : BitVec 64) :
    whiten x ^^^ whiten x' = whiten (x ^^^ x') := by
  rw [whiten_xor]

end DriftCore
