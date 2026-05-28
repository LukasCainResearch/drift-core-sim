/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Whitening Output-Stage Bijectivity

The Drift Core's output stage runs a three-step XOR-shift cascade on the
post-fold 64-bit value. In silicon (`dad_core.v`, lines 22-26):

    whitened_val = folded_bits;
    whitened_val = whitened_val ^ (whitened_val >> 24);
    whitened_val = whitened_val ^ (whitened_val << 14);
    whitened_val = whitened_val ^ (whitened_val >> 34);
    data_out = whitened_val;

This file proves the cascade is a **bijection** on `BitVec 64`.
Consequence: the whitening is information-preserving — every 64-bit output
corresponds to a unique 64-bit input — so the cascade does not lose,
collapse, or alias any state from the upstream fold step.

## Bijection structure

Each individual XOR-shift step `x ↦ x ⊕ (x ≫ k)` is a GF(2)-linear map
with a nilpotent perturbation. Its inverse is the Neumann series
`y ↦ y ⊕ (y ≫ k) ⊕ (y ≫ 2k) ⊕ …`, terminating when the shift exhausts
the width. For our `(a, b, c) = (24, 14, 34)` at `W = 64`:

* Right-shift 24 inverse: `y ⊕ (y ≫ 24) ⊕ (y ≫ 48)` (3 terms; `y ≫ 72 = 0`).
* Left-shift 14 inverse:  `y ⊕ (y ≪ 14) ⊕ (y ≪ 28) ⊕ (y ≪ 42) ⊕ (y ≪ 56)`.
* Right-shift 34 inverse: `y ⊕ (y ≫ 34)` (2 terms; `y ≫ 68 = 0`).

The bijection is established by discharging both directions of the
left/right-inverse identity via `bv_decide` (SAT-backed BitVec decision
procedure).

## Site claim

This file underwrites the "output-stage bijectivity" claim on compute.html:
the whitening cascade preserves information from input to output. Combined
with `Fold.lean` (which bounds the output width), it certifies the output
pipeline is structurally well-formed.

**Caveat (per honest-framing rules).** Bijectivity is an
*implementation-safety* property, not a cryptographic-security claim. A
bijective map can be far from cryptographically strong (e.g., the identity
map is bijective). The whitening's resistance to cryptanalysis remains a
separate question pursued via independent peer review.
-/

import Std.Tactic.BVDecide
import Mathlib.Data.BitVec

namespace DriftCore

/-! ## Production whitening (matches `dad_core.v` exactly) -/

/-- The Drift Core production whitening: three chained XOR-shift steps
with the production triple `(a, b, c) = (24, 14, 34)` on `BitVec 64`.
Matches `dad_core.v` line-for-line. -/
def whiten (x : BitVec 64) : BitVec 64 :=
  let y1 := x  ^^^ (x  >>> 24)
  let y2 := y1 ^^^ (y1 <<< 14)
  let y3 := y2 ^^^ (y2 >>> 34)
  y3

/-- Inverse of the production whitening, built by undoing each step in
reverse order via the Neumann-series formula. The number of terms in
each sum is `⌈W / k⌉` (the smallest `n` with `nk ≥ W`). -/
def unwhiten (y : BitVec 64) : BitVec 64 :=
  -- Step 3 inverse (right-shift 34): `2 * 34 = 68 ≥ 64`, so 2 terms.
  let z2 := y  ^^^ (y  >>> 34)
  -- Step 2 inverse (left-shift 14):  `⌈64 / 14⌉ = 5` terms.
  let z1 := z2 ^^^ (z2 <<< 14) ^^^ (z2 <<< 28) ^^^ (z2 <<< 42) ^^^ (z2 <<< 56)
  -- Step 1 inverse (right-shift 24): `⌈64 / 24⌉ = 3` terms.
  let z0 := z1 ^^^ (z1 >>> 24) ^^^ (z1 >>> 48)
  z0

/-- **Left inverse.** Applying `unwhiten` after `whiten` recovers the input. -/
theorem unwhiten_whiten (x : BitVec 64) : unwhiten (whiten x) = x := by
  unfold unwhiten whiten
  bv_decide

/-- **Right inverse.** Applying `whiten` after `unwhiten` recovers the input. -/
theorem whiten_unwhiten (y : BitVec 64) : whiten (unwhiten y) = y := by
  unfold whiten unwhiten
  bv_decide

/-- **Bijection.** The production whitening is a bijection of `BitVec 64`.

Consequence: every 64-bit output of the whitening cascade has a unique
64-bit pre-image, so the cascade cannot collapse, alias, or lose any
state delivered by the upstream fold step. -/
theorem whiten_bijective : Function.Bijective whiten := by
  refine ⟨?_, ?_⟩
  · intro a b h
    have := congrArg unwhiten h
    rwa [unwhiten_whiten, unwhiten_whiten] at this
  · intro y
    exact ⟨unwhiten y, whiten_unwhiten y⟩

/-- The whitening as an `Equiv.Perm`. Useful when downstream consumers
want to compose with other bijections or invoke `Finset` / `Fintype`
machinery for distribution-preservation arguments. -/
def whitenEquiv : Equiv.Perm (BitVec 64) where
  toFun := whiten
  invFun := unwhiten
  left_inv := unwhiten_whiten
  right_inv := whiten_unwhiten

end DriftCore
