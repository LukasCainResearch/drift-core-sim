/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# `driftStep` is *Not* a Bijection — Honest-Framing Result

The Drift Core's arithmetic step is

    driftStep s = ((3 · s + 1) mod 2^W) / 2

The integer division by 2 in the final step discards one bit. Concretely:

* `(3 · s + 1) mod 2^W` is a bijection on `Fin (2^W)` (multiplication by
  3 is invertible mod `2^W` since `gcd(3, 2^W) = 1`; adding 1 is a
  shift).
* `/ 2` (integer division) projects `Fin (2^W)` onto `Fin (2^(W-1))`,
  losing one bit of information.

Hence `driftStep : Fin (2^W) → Fin (2^W)` has image of cardinality
exactly `2^(W-1)` — strictly less than the domain `2^W` whenever
`W ≥ 1`. The map is **not surjective** and (on a finite set with
equal domain and codomain) therefore **not injective**.

## Why this matters — honest framing

The plan's Phase 4-C.1 contemplated "ergodicity in the dynamical-systems
sense (measure-preserving + irreducible)." For *uniform measure* on
`Fin (2^W)`, the answer is now formally known:

> The uniform measure on `Fin (2^W)` is **not** preserved by `driftStep`.

The recurrence loses one bit of entropy per iteration in the worst case.
The empirically-observed approximate uniformity of the output cannot be
explained by measure-preservation of the uniform input; it arises from
transient mixing combined with the bijective whitening (`Whitening.lean`,
`Distribution.lean`) on whatever distribution the iterated state
actually has.

This is a *negative* implementation-safety result: it rules out one
specific reading of "ergodicity" with mathematical certainty (not just
by absence of proof). The stronger readings — measure-preservation with
respect to a non-uniform invariant measure, or mixing rate / spectral
gap — remain research-level (Phase 4-C.2, gated on academic
collaboration).

## What is *not* proved here

* The exact 2-to-1 pairing structure (which `s, s'` pairs collide). This
  is computable from `s' = s + 3⁻¹ mod 2^W` but the formal proof needs
  the explicit modular inverse and is harder than the image-size
  argument used here.
* The *image* of `driftStep` and its dynamics under iteration. The map
  restricted to its image may have nicer properties (potentially
  bijective on a strictly smaller "recurrent" subset), but characterizing
  that subset is research-level.
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Card
import DriftRecurrence

namespace DriftCore

/--
**Image bound.** Every output of `driftStep` has value strictly less
than `2^(W-1)` (for `W ≥ 1`). The `/2` in the recurrence drops the
LSB of the arithmetic step's result, so the image lives in the
lower half of the codomain.
-/
theorem driftStep_val_lt_half {W : ℕ} (s : Fin (2 ^ W)) (hW : 1 ≤ W) :
    (driftStep W s).val < 2 ^ (W - 1) := by
  unfold driftStep
  simp only
  apply Nat.div_lt_of_lt_mul
  have hWpow : (2 : ℕ) ^ W = 2 * 2 ^ (W - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega⟩
    rw [pow_succ, Nat.add_sub_cancel, Nat.mul_comm]
  rw [← hWpow]
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

/--
**Non-surjectivity.** `driftStep` does not surject onto `Fin (2^W)`
for `W ≥ 1`. Witness: the value `2^(W-1)` is in `Fin (2^W)` but
never appears as an output (by `driftStep_val_lt_half`).
-/
theorem driftStep_not_surjective {W : ℕ} (hW : 1 ≤ W) :
    ¬ Function.Surjective (driftStep W) := by
  intro hsurj
  have hpow : 2 ^ (W - 1) < 2 ^ W :=
    Nat.pow_lt_pow_right Nat.one_lt_two (by omega : W - 1 < W)
  let target : Fin (2 ^ W) := ⟨2 ^ (W - 1), hpow⟩
  obtain ⟨s, hs⟩ := hsurj target
  have h1 : (driftStep W s).val < 2 ^ (W - 1) := driftStep_val_lt_half s hW
  have h2 : (driftStep W s).val = 2 ^ (W - 1) := congrArg Fin.val hs
  omega

/--
**Non-injectivity.** On a finite set, `Function.Injective` is equivalent
to `Function.Surjective` (for endomorphisms). Combined with
`driftStep_not_surjective`, this gives non-injectivity directly.

Consequence: there exist distinct seeds `s ≠ s'` with
`driftStep s = driftStep s'`. The Drift Core's arithmetic step *does*
collapse pairs of states.
-/
theorem driftStep_not_injective {W : ℕ} (hW : 1 ≤ W) :
    ¬ Function.Injective (driftStep W) := by
  intro hinj
  exact driftStep_not_surjective hW (Finite.injective_iff_surjective.mp hinj)

/--
**Concrete collision exists.** From non-injectivity, extract two
distinct inputs that `driftStep` maps to the same output. (Existence
only — the explicit `s, s + 3⁻¹` form is computable but not exposed
here; see file header.)
-/
theorem driftStep_exists_collision {W : ℕ} (hW : 1 ≤ W) :
    ∃ s₁ s₂ : Fin (2 ^ W), s₁ ≠ s₂ ∧ driftStep W s₁ = driftStep W s₂ := by
  by_contra h
  push_neg at h
  -- h : ∀ s₁ s₂, s₁ ≠ s₂ → driftStep W s₁ ≠ driftStep W s₂
  apply driftStep_not_injective hW
  intro a b hab
  by_contra hne
  exact h a b hne hab

/--
**Non-bijection.** Combining non-surjectivity with the definition,
`driftStep` is not a bijection on `Fin (2^W)` for `W ≥ 1`. No
bijective relabeling of the state space is induced by one step of
the recurrence.

This is the clean "honest framing" output: the strong reading of
"measure-preserving" — that uniform measure on the state space is
preserved by the recurrence — is provably false.
-/
theorem driftStep_not_bijective {W : ℕ} (hW : 1 ≤ W) :
    ¬ Function.Bijective (driftStep W) :=
  fun hbij => driftStep_not_surjective hW hbij.surjective

end DriftCore
