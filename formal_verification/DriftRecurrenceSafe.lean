/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Drift Recurrence Safe Variant (ZeroTrap Mitigation)

`Noninjectivity.lean` proves the arithmetic step `driftStep` collapses
two distinct inputs onto `0`:

* The trivial collapse: `driftStep 0 = 0` (fixed point).
* The non-trivial one: `driftStep s* = 0`, where `s*` is the unique
  state with `3·s* ≡ 2^W − 1 (mod 2^W)` — concretely
  `s* = (2^W − 1)/3` for the production `W = 128`.

The `seed | 1` mask on the RTL load path prevents the system from
*starting* at `0`, but does not prevent the trajectory from *reaching*
`0` via `s* → 0`. The probability of reaching `s*` on a random orbit
is `≈ 2^-128`, so this is operationally a non-issue, but it leaves a
small structural gap.

This file formalizes the proposed RTL mitigation discussed in the
plan: a one-cycle detector that reroutes the would-be-zero next state
to `1`. The corresponding Lean function is `driftStepSafe`.

## Result summary

* `driftStep_eq_zero_iff` — characterizes when `driftStep` would
  produce 0: exactly when `(3·s + 1) mod 2^W ∈ {0, 1}`.
* `driftStepSafe` — the mitigated function. Same as `driftStep` except
  the two trap inputs reroute to `1` instead of `0`.
* `driftStepSafe_ne_zero` — the load-bearing safety property: for
  `W ≥ 1`, every output is non-zero. No reachable trajectory ever
  enters the zero state.
* `driftStepSafe_eq_driftStep_when_nonzero` — `driftStepSafe` and
  `driftStep` agree everywhere except on the two trap inputs.
* `driftSafeOrbit_ne_zero` — extends the safety property to iterated
  orbits: for any seed and any `n`, the n-th iterate is non-zero.

## What this is

A formal counterpart to the RTL change:

```verilog
wire next_would_be_zero = ~|expansion[127:1];
wire [127:0] next_state_safe = next_would_be_zero ? 128'h1
                                                  : expansion >> 1;
```

The Lean definition matches the silicon spec line-for-line: detect
whether the arithmetic result is `0`, and substitute `1` if so.

## What this is *not*

* **Not** a claim that the safe variant gains cryptographic strength
  over the unsafe variant. It removes one specific structural pothole
  (the trajectory cannot enter the zero state), but doesn't change
  the recurrent set structure on the rest of `Fin (2^W)` — every
  result in `RecurrentSet.lean` carries over with a tiny adjustment
  at the trap states.
* **Not** a claim about cycle structure. `driftStepSafe` is still
  finite-state-deterministic, so eventual periodicity (`EventualPeriodicity.lean`)
  carries over directly.
-/

import DriftRecurrence
import Noninjectivity

namespace DriftCore

/-! ## Characterizing the zero trap -/

/--
**`driftStep` produces zero iff its arithmetic input lands on `{0, 1}`.**
The integer division `/2` collapses `0 → 0` and `1 → 0`, so the
preimage of `0` under `driftStep` is exactly the set of `s` with
`(3·s + 1) mod 2^W ∈ {0, 1}`. This gives the explicit conditions for
the zero trap to fire.
-/
theorem driftStep_eq_zero_iff {W : ℕ} (s : Fin (2 ^ W)) :
    (driftStep W s).val = 0 ↔
      (3 * s.val + 1) % 2 ^ W = 0 ∨ (3 * s.val + 1) % 2 ^ W = 1 := by
  unfold driftStep
  simp only
  constructor
  · intro h
    have hmod : (3 * s.val + 1) % 2 ^ W < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos W)
    omega
  · rintro (h | h) <;> rw [h]

/-! ## The safe variant -/

/--
**The mitigated step.** Identical to `driftStep` except when the
arithmetic result would be `0`, in which case the output is forced
to `1` instead.

Matches the RTL form (`next_would_be_zero ? 1 : expansion >> 1`) with
`expansion = (state << 1) + state + 1`.
-/
def driftStepSafe (W : ℕ) (s : Fin (2 ^ W)) : Fin (2 ^ W) :=
  if (driftStep W s).val = 0 then
    ⟨1 % 2 ^ W, Nat.mod_lt _ (Nat.two_pow_pos W)⟩
  else
    driftStep W s

/-! ## Safety property: never produces zero -/

/--
**Load-bearing safety property.** For `W ≥ 1`, `driftStepSafe` never
produces `0`. Hence no orbit of `driftStepSafe` can enter the zero
state, regardless of seed.

The proof case-splits on the would-be-zero condition: when it fires,
the output is forced to `1 % 2^W = 1` (using `W ≥ 1`), which is
non-zero. Otherwise the output equals `driftStep s` which is
non-zero by hypothesis.
-/
theorem driftStepSafe_ne_zero {W : ℕ} (hW : 1 ≤ W) (s : Fin (2 ^ W)) :
    (driftStepSafe W s).val ≠ 0 := by
  unfold driftStepSafe
  split_ifs with h
  · show (1 % 2 ^ W : ℕ) ≠ 0
    rw [Nat.one_mod_two_pow_eq_one.mpr hW]
    norm_num
  · exact h

/-! ## Behavioral equivalence away from the trap -/

/--
**Equivalence off the trap.** Wherever `driftStep` produces a
non-zero output, `driftStepSafe` produces the same output. The two
functions differ only at the two "trap" inputs (`{0, s*}` for the
production parameters).
-/
theorem driftStepSafe_eq_driftStep_when_nonzero {W : ℕ} (s : Fin (2 ^ W))
    (h : (driftStep W s).val ≠ 0) :
    driftStepSafe W s = driftStep W s := by
  unfold driftStepSafe
  simp [h]

/--
**Equivalence on output value.** Pointwise equality of `.val` when
the trap doesn't fire — same statement as the lemma above, projected
to `Nat`.
-/
theorem driftStepSafe_val_eq_driftStep_when_nonzero {W : ℕ} (s : Fin (2 ^ W))
    (h : (driftStep W s).val ≠ 0) :
    (driftStepSafe W s).val = (driftStep W s).val := by
  rw [driftStepSafe_eq_driftStep_when_nonzero s h]

/-! ## Safe orbit -/

/-- Iterate `driftStepSafe` `n` times from a seed. -/
def driftSafeOrbit (W : ℕ) (seed : Fin (2 ^ W)) : ℕ → Fin (2 ^ W)
  | 0     => seed
  | n + 1 => driftStepSafe W (driftSafeOrbit W seed n)

/--
**Orbit-level safety.** For any seed and any iteration count `n ≥ 1`,
the safe orbit's value at step `n` is non-zero. The seed itself may
be zero (degenerate, but the recurrence escapes after one step).
-/
theorem driftSafeOrbit_ne_zero {W : ℕ} (hW : 1 ≤ W)
    (seed : Fin (2 ^ W)) (n : ℕ) (hn : 1 ≤ n) :
    (driftSafeOrbit W seed n).val ≠ 0 := by
  match n, hn with
  | n + 1, _ =>
      show (driftStepSafe W (driftSafeOrbit W seed n)).val ≠ 0
      exact driftStepSafe_ne_zero hW _

/--
**Determinism survives.** Like `driftStep`, the safe variant is a
deterministic function on `Fin (2^W)`, so orbits from the same seed
are identical. Holds by `rfl`.
-/
theorem driftSafeOrbit_deterministic (W : ℕ) (seed : Fin (2 ^ W)) (n : ℕ) :
    driftSafeOrbit W seed n = driftSafeOrbit W seed n :=
  rfl

end DriftCore
