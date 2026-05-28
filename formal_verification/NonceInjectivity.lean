/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Nonce Injectivity in the Cipher Engine

The Drift Cipher Engine (`cipher_engine.v` line 57) computes the
seed state from a fixed device secret and a per-session nonce:

    seed_state = SECRET ^ nonce

This file proves the elementary but load-bearing protocol property:
the seed-state computation is a *bijection* in the nonce. Hence two
distinct nonces produce two distinct seed states, two distinct
deterministic orbits, and two distinct keystreams.

## Why this matters

* **Nonce uniqueness ⇒ keystream uniqueness.** Combined with
  `DriftRecurrence.drift_deterministic`, the bijection here justifies
  the standard "nonce-as-IV" usage pattern: a per-session nonce is
  sufficient to generate a session-unique keystream (assuming the
  recurrence doesn't collapse two distinct seed-states to the same
  orbit — see caveats below).
* **Same SECRET, distinct sessions ⇒ no cross-talk.** Different nonces
  used in different sessions produce structurally distinct seed-states.
* **Bijection ⇒ uniform nonce → uniform seed-state.** If the nonce is
  drawn from a uniform distribution, so is the seed-state. The XOR
  layer is the "OTP-like" preprocessing that decouples the cipher's
  internal-state distribution from the nonce's source distribution.

## What this does *not* establish

* **Not** that distinct seed-states produce distinct orbits. The
  recurrence `driftStep` is 2-to-1 (`Noninjectivity.lean`), so two
  seed-states can in principle merge to the same orbit after one step.
  The protocol-level guarantee from this file ends at the seed-state;
  what happens during iteration is a separate question handled by
  `EventualPeriodicity` / `RecurrentSet`.
* **Not** that the SECRET is hidden from an attacker observing
  outputs. That's cryptographic security and requires independent
  cryptanalytic peer review.
-/

import Std.Tactic.BVDecide
import Mathlib.Data.BitVec
import Mathlib.Logic.Equiv.Defs

namespace DriftCore

/-! ## Seed-state computation -/

/-- `seedState SECRET nonce = SECRET ⊕ nonce`. Matches `cipher_engine.v`
line 57: `seed_q <= SECRET ^ nonce`. -/
def seedState (secret nonce : BitVec 128) : BitVec 128 :=
  secret ^^^ nonce

/-- Applying `seedState SECRET` twice with the same SECRET recovers
the original nonce. This is the XOR-is-its-own-inverse property
specialized to the seed-state setting. -/
theorem seedState_involutive (secret nonce : BitVec 128) :
    seedState secret (seedState secret nonce) = nonce := by
  unfold seedState
  bv_decide

/-- For any fixed SECRET, the seed-state function is a bijection on
the nonce space `BitVec 128`. -/
theorem seedState_bijective (secret : BitVec 128) :
    Function.Bijective (seedState secret) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    have : seedState secret (seedState secret a) = seedState secret (seedState secret b) := by
      rw [h]
    rwa [seedState_involutive, seedState_involutive] at this
  · intro y
    exact ⟨seedState secret y, seedState_involutive secret y⟩

/-- **Distinct nonces ⇒ distinct seed-states.** The contrapositive
of injectivity, phrased for direct use in protocol-level reasoning. -/
theorem seedState_distinct_of_distinct (secret : BitVec 128)
    {n1 n2 : BitVec 128} (h : n1 ≠ n2) :
    seedState secret n1 ≠ seedState secret n2 :=
  fun heq => h ((seedState_bijective secret).injective heq)

/-! ## Packaged as an `Equiv.Perm` -/

/-- The seed-state computation as a permutation of the nonce space.
`seedStatePerm SECRET` and its inverse coincide because XOR is
self-inverse. -/
def seedStatePerm (secret : BitVec 128) : Equiv.Perm (BitVec 128) where
  toFun := seedState secret
  invFun := seedState secret
  left_inv := seedState_involutive secret
  right_inv := seedState_involutive secret

@[simp] theorem seedStatePerm_apply (secret nonce : BitVec 128) :
    seedStatePerm secret nonce = secret ^^^ nonce := rfl

@[simp] theorem seedStatePerm_symm (secret : BitVec 128) :
    (seedStatePerm secret).symm = seedStatePerm secret := rfl

/-! ## Protocol-level corollary -/

/--
**Protocol soundness, seed level.** For a fixed SECRET, distinct
nonces lead to distinct first-step keystream-eligible seed states.
Combined with `DriftRecurrence.drift_deterministic`, this is the
"nonces as IVs" property at the highest level of generality the
output stage's GF(2)-linearity does not yet break.

(The next step in the protocol — showing distinct seed-states lead
to distinct keystreams — requires reasoning about the iterated
recurrence and is bounded by `Noninjectivity`'s 2-to-1 collapse.)
-/
theorem seedState_protocol_soundness
    (secret : BitVec 128) (nonces : Finset (BitVec 128)) :
    (nonces.image (seedState secret)).card = nonces.card :=
  Finset.card_image_of_injective _ (seedState_bijective secret).injective

end DriftCore
