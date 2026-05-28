/-
Copyright (c) 2025 Lukas Cain. All rights reserved.
Released under Apache 2.0 license.

# Core definitions for the ABC Conjecture formalization

This file defines the fundamental arithmetic objects from the paper
"The Thermodynamic Limit of the ABC Conjecture":
- Popcount (Hamming weight)
- Bit length
- Carry friction and binary carry stress
- Laminar flow (bit-disjoint) predicate
- Radical of an integer
- ABC triple structure
- Arithmetic quality
-/

import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat

namespace ABCFormalization

/-! ## Popcount (Hamming weight)

The number of 1-bits in the binary representation of a natural number.
Not available in Mathlib for `Nat`, so we define it via `binaryRec`.
-/

/-- The number of 1-bits in the binary representation of `n`. -/
def popcount : ℕ → ℕ :=
  Nat.binaryRec 0 (fun b _ ih => ih + b.toNat)

@[simp]
theorem popcount_zero : popcount 0 = 0 := by
  unfold popcount; rw [Nat.binaryRec_zero]

theorem popcount_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    popcount (Nat.bit b n) = popcount n + b.toNat := by
  unfold popcount
  rw [Nat.binaryRec_eq b n (Or.inr h)]

@[simp]
theorem popcount_one : popcount 1 = 1 := by
  unfold popcount; rw [Nat.binaryRec_one]; rfl

/-! ## Bit length -/

/-- The number of bits needed to represent `n`. Uses `Nat.size` from Mathlib. -/
abbrev bitLength (n : ℕ) : ℕ := Nat.size n

/-! ## Carry friction -/

/-- Binary carry friction: the total number of carries when adding `a` and `b`
in base 2. By the half-adder identity `a + b = (a ^^^ b) + 2 * (a &&& b)`,
carries occur where both bits are 1. The total carry count equals
`popcount(a) + popcount(b) - popcount(a + b)`. -/
def carry_friction (a b : ℕ) : ℕ :=
  popcount a + popcount b - popcount (a + b)

/-! ## Binary carry stress -/

/-- Binary carry stress σ(a,b): carry friction normalized by the bit length
of `c = a + b`. Returns a rational number in [0, 1]. -/
def binary_carry_stress (a b : ℕ) : ℚ :=
  if bitLength (a + b) = 0 then 0
  else (carry_friction a b : ℚ) / (bitLength (a + b) : ℚ)

/-! ## Laminar flow -/

/-- Two natural numbers are *laminar* (bit-disjoint) when their bitwise AND
is zero. Equivalently, their binary representations have no overlapping 1-bits,
so adding them in base 2 produces no carries. -/
def isLaminar (a b : ℕ) : Prop :=
  a &&& b = 0

instance (a b : ℕ) : Decidable (isLaminar a b) :=
  inferInstanceAs (Decidable (a &&& b = 0))

/-! ## Hamming density -/

/-- Hamming density: the fraction of 1-bits in the binary representation. -/
noncomputable def hamming_density (n : ℕ) : ℝ :=
  if Nat.size n = 0 then 0
  else (popcount n : ℝ) / (Nat.size n : ℝ)

/-! ## Radical of an integer -/

/-- The radical of `n`: the product of its distinct prime factors.
For example, `radical 12 = radical (2² × 3) = 2 × 3 = 6`. -/
noncomputable def radical (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, p

theorem radical_one : radical 1 = 1 := by
  simp [radical, Nat.primeFactors]

/-! ## ABC triple -/

/-- An ABC triple: coprime positive integers with `a + b = c`. -/
structure ABCTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  ha : 0 < a
  hb : 0 < b
  hsum : a + b = c
  hcoprime : Nat.Coprime a b

/-- Arithmetic Quality Q(a,b,c) = log(c) / log(rad(abc)).
Measures how much `c` is compressed relative to the radical. -/
noncomputable def arithmetic_quality (t : ABCTriple) : ℝ :=
  Real.log (t.c : ℝ) / Real.log ((radical (t.a * t.b * t.c) : ℕ) : ℝ)

/-! ## Basic lemmas -/

theorem carry_friction_zero_left (b : ℕ) : carry_friction 0 b = 0 := by
  simp [carry_friction]

theorem carry_friction_zero_right (a : ℕ) : carry_friction a 0 = 0 := by
  simp [carry_friction]

theorem carry_friction_comm (a b : ℕ) : carry_friction a b = carry_friction b a := by
  unfold carry_friction
  rw [Nat.add_comm a b]
  ring_nf

theorem isLaminar_comm (a b : ℕ) : isLaminar a b ↔ isLaminar b a := by
  simp [isLaminar, Nat.and_comm]

end ABCFormalization
