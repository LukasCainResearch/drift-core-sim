/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Eventual Periodicity of the Drift Recurrence

The Drift Core's state space is `Fin (2^W)` — finite. Any deterministic
function on a finite set, iterated, must eventually enter a cycle: by
pigeonhole, among any `|domain| + 1` consecutive states two must
coincide, and from there the orbit repeats forever.

This is the honest version of the "preventing infinite loops" claim:
the iterated recurrence cannot diverge to a non-repeating trajectory.
Cycle entry occurs within `2^W` steps (`W = 128` in silicon means
`2^128`, astronomically large but structurally bounded).

## What this *does* establish

* `driftOrbit_eventually_periodic` — every orbit from any seed has two
  equal states among the first `2^W + 1` iterates. The orbit is
  eventually periodic.
* No infinite-loop divergence: from any seed, the recurrence stays
  within the finite state space `Fin (2^W)` forever.

## What this *does not* establish

* The cycle length. Pigeonhole gives an upper bound of `2^W`; the
  actual cycle structure of `driftStep` is much richer (and analyzing
  it is Phase 4 research territory).
* That the cycle is the entire state space. In fact `driftStep` is
  *not* a bijection (see `Noninjectivity.lean`), so the recurrence's
  recurrent set is strictly smaller than `Fin (2^W)`.
* Termination of any *halting* property — there is no halting
  condition in the recurrence; "termination" here means "eventual
  periodicity," not "reaches a fixed state and stops."
-/

import Mathlib.Data.Fintype.Pigeonhole
import DriftRecurrence

namespace DriftCore

/--
**Eventual periodicity (pigeonhole).** For any width `W ≥ 1` and any
seed `s : Fin (2^W)`, the orbit `driftOrbit W s` repeats a state within
the first `2^W + 1` iterates: there exist indices `i < j ≤ 2^W` with
`driftOrbit W s i = driftOrbit W s j`.

Consequence: the orbit is eventually periodic with cycle length at
most `2^W`. The recurrence cannot run forever without repetition.
-/
theorem driftOrbit_eventually_periodic (W : ℕ) (seed : Fin (2 ^ W)) :
    ∃ (i j : ℕ), i < j ∧ j ≤ 2 ^ W ∧
      driftOrbit W seed i = driftOrbit W seed j := by
  -- View the orbit as a function `Fin (2^W + 1) → Fin (2^W)`.
  -- Since the codomain has cardinality `2^W < 2^W + 1`, pigeonhole
  -- produces two distinct inputs with the same image.
  have hcard : Fintype.card (Fin (2 ^ W)) < Fintype.card (Fin (2 ^ W + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨x, y, hxy, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (2 ^ W + 1) => driftOrbit W seed k.val) hcard
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact ⟨x.val, y.val, h, Nat.le_of_lt_succ y.isLt, heq⟩
  · exact absurd (Fin.ext h) hxy
  · exact ⟨y.val, x.val, h, Nat.le_of_lt_succ x.isLt, heq.symm⟩

/--
**Period extraction.** From eventual periodicity, extract a positive
period `p ≤ 2^W` such that for some pre-period offset `k`,
`driftOrbit W seed (k + p) = driftOrbit W seed k`.

This packages the existence statement above into the form a downstream
proof would use: "there is a cycle of length `p` reached after `k`
steps."
-/
theorem driftOrbit_has_cycle (W : ℕ) (seed : Fin (2 ^ W)) :
    ∃ (k p : ℕ), 0 < p ∧ p ≤ 2 ^ W ∧
      driftOrbit W seed (k + p) = driftOrbit W seed k := by
  obtain ⟨i, j, hij, hj, heq⟩ := driftOrbit_eventually_periodic W seed
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · -- p = j - i ≤ j ≤ 2^W
    exact le_trans (Nat.sub_le _ _) hj
  · -- driftOrbit (i + (j - i)) = driftOrbit j = driftOrbit i
    rw [Nat.add_sub_cancel' hij.le]
    exact heq.symm

end DriftCore
