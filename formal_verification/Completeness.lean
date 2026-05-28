/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Completeness of the Drift Covering System

Establishes that the three transition conditions (T1: even; T2: 1 mod 4;
T3: 3 mod 4) form a *complete* and *mutually exclusive* covering of `ℤ`.

`complete_coverage`           — every integer satisfies at least one Tᵢ.
`complete_coverage_exactly_one` — every integer satisfies exactly one Tᵢ.

The completeness result rules out "Undefined" or "Idle" hardware states;
the exclusivity result rules out simultaneous routing into multiple gates.
Together they justify the page-text claim that every integer falls into
exactly one bucket.
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace DriftCoverage

/-- Transition 1: divisible by 2 (even). -/
def T1_condition (n : ℤ) : Prop := n % 2 = 0

/-- Transition 2: 1 mod 4. -/
def T2_condition (n : ℤ) : Prop := n % 4 = 1

/-- Transition 3: 3 mod 4. -/
def T3_condition (n : ℤ) : Prop := n % 4 = 3

/--
**Complete coverage.** Every integer satisfies at least one of T1/T2/T3.
The proof dispatches the four residues of `n` modulo 4: classes `0` and
`2` reduce to T1 (even); class `1` is T2; class `3` is T3.
-/
theorem complete_coverage (n : ℤ) :
    T1_condition n ∨ T2_condition n ∨ T3_condition n := by
  dsimp [T1_condition, T2_condition, T3_condition]
  omega

/--
**Exclusive coverage.** Every integer satisfies *exactly one* of T1/T2/T3.
Strengthens `complete_coverage` from a disjunction to a partition: the
three buckets are pairwise disjoint, and their union is all of `ℤ`.

T2 and T3 are clearly disjoint (`1 ≠ 3` mod 4). T1 (even) is disjoint
from both T2 and T3 because `n % 4 = 1` or `n % 4 = 3` forces `n` odd.
-/
theorem complete_coverage_exactly_one (n : ℤ) :
    ( T1_condition n ∧ ¬ T2_condition n ∧ ¬ T3_condition n) ∨
    (¬T1_condition n ∧   T2_condition n ∧ ¬ T3_condition n) ∨
    (¬T1_condition n ∧ ¬ T2_condition n ∧   T3_condition n) := by
  dsimp [T1_condition, T2_condition, T3_condition]
  omega

end DriftCoverage
