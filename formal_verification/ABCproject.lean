-- -----------------------------------------------------------------------------
-- Copyright (c) 2025 Drift Systems Inc.
-- CONFIDENTIAL AND PROPRIETARY
-- -----------------------------------------------------------------------------
import Mathlib

open Nat

namespace AbcProject

/--
`isLaminar a b` means that `a` and `b` are "laminar" (bit-disjoint):
their bitwise AND is `0`.  Equivalently, adding them in base 2
produces **no carries**.
-/
def isLaminar (a b : ℕ) : Prop :=
  a &&& b = 0

/--
**Bit-prime bridge (axiomatized).**

If `a` and `b` are bit-disjoint (laminar), then the binomial coefficient
`(a + b).choose a` is odd (i.e. not divisible by `2`), and conversely.

Mathematically, this is the base-2 Lucas/Kummer statement

> `(a + b).choose a` is odd ↔ no carries occur when adding `a` and `b` in base 2.

Here we record it as an axiom so that the rest of the ABC paper can use it
without needing to reproduce the whole combinatorial proof inside this file.
Once you locate (or prove) the corresponding theorem in mathlib, you can
replace this `axiom` with a `theorem … :=` and a real proof.
-/
axiom laminar_implies_odd_binomial (a b : ℕ) :
  isLaminar a b ↔ ¬ (2 ∣ Nat.choose (a + b) a)

end AbcProject
