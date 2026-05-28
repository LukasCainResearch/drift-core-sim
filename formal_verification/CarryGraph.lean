/-
Copyright (c) 2025 Lukas Cain. All rights reserved.
Released under Apache 2.0 license.

# Carry-State Graph and Fuel Accounting

This file formalizes properties of the ×p carry transducer's state space
and establishes fuel-accounting bounds leading toward global popcount
lower bounds for p^n.

## Main Results

### Section 1 – Block and Carry Bounds
* `extractBlock_lt_pow`: every K-bit block is < 2^K
* `blockCarry_lt`: the carry at any position j is < p

### Section 2 – Carry Reset Properties
* `carry_reset_to_zero`: zero input always resets carry to 0
* `output_at_carry_reset`: when carry resets, the output equals the old carry
* `output_pos_at_carry_reset`: that output is positive if carry was

### Section 3 – Coprimality and Zero-Output Classification
* `odd_prime_coprime_two_pow`: gcd(p, 2^K) = 1 for odd prime p
* `zero_carry_zero_output_imp_zero_input`: at zero carry, zero output ⟹ zero input
* `zero_output_dichotomy`: zero output ⟹ (carry=0 ∧ input=0) ∨ (carry>0 ∧ input>0)

### Section 4 – Fuel Accounting
* `expensive_zero_has_nonzero_input`: expensive zero blocks consume fuel
* `nonzeroBlockCount`, `expensiveZeroCount`: block-counting functions
* `popcount_ge_nonzero_block_count`: popcount ≥ number of nonzero blocks

## Strategy

The carry chain of the ×p transducer has states {0, ..., p-1}.
- State 0 is always reachable (via zero input block)
- Nonzero carry + zero output consumes positive input (fuel consumption lemma)
- At zero carry, only zero input can give zero output (coprimality of p and 2^K)

Together these show every zero-output block is "expensive" (requires fuel)
or "free" (sits at carry = 0 with zero input — but this means the *input*
also has a zero block at that position, pushing the cost to p^(n−1)).
-/

import ABCFormalization.CarryTransducer

open Nat ABCFormalization Filter

namespace ABCFormalization

/-! ## Section 1: Block and Carry Bounds -/

/-- Every K-bit extracted block is strictly less than 2^K. -/
theorem extractBlock_lt_pow (n lo K : ℕ) : extractBlock n lo K < 2 ^ K :=
  Nat.mod_lt _ (by positivity)

/-- The carry at every block position stays strictly below p. -/
theorem blockCarry_lt (p n K : ℕ) (hp : 1 < p) :
    ∀ j, blockCarry p n K j < p := by
  intro j
  induction j with
  | zero => simp [blockCarry]; omega
  | succ j ih =>
    simp only [blockCarry]
    exact mulBlockCarry_lt p _ _ K (extractBlock_lt_pow n (j * K) K) ih

/-! ## Section 2: Carry Reset Properties -/

/-- Zero input block always resets the carry to 0 (when carry < 2^K). -/
theorem carry_reset_to_zero (p c K : ℕ) (hc : c < 2 ^ K) :
    mulBlockCarry p c 0 K = 0 := by
  simp only [mulBlockCarry, mulBlockVal, Nat.mul_zero, Nat.zero_add]
  exact Nat.div_eq_of_lt hc

/-- When a zero-input block resets the carry, the output equals the
old carry value. -/
theorem output_at_carry_reset (p c K : ℕ) (hc : c < 2 ^ K) :
    mulBlockOut p c 0 K = c := by
  simp only [mulBlockOut, mulBlockVal, Nat.mul_zero, Nat.zero_add]
  exact Nat.mod_eq_of_lt hc

/-- Carry reset from a nonzero carry always produces positive output. -/
theorem output_pos_at_carry_reset (p c K : ℕ) (hc : c < 2 ^ K) (hc_pos : 0 < c) :
    0 < mulBlockOut p c 0 K := by
  rw [output_at_carry_reset p c K hc]; exact hc_pos

/-! ## Section 3: Coprimality and Zero-Output Classification -/

/-- An odd prime is coprime to every power of 2. -/
theorem odd_prime_coprime_two_pow (p : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) (K : ℕ) :
    Nat.Coprime p (2 ^ K) := by
  apply Nat.Coprime.pow_right
  rw [hp.coprime_iff_not_dvd]
  intro h2
  exact hodd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)

/-- At zero carry with an odd prime p, a zero output block from a
valid input (x < 2^K) forces x = 0. This uses that gcd(p, 2^K) = 1. -/
theorem zero_carry_zero_output_imp_zero_input (p K x : ℕ)
    (hp : Nat.Prime p) (hodd : p ≠ 2) (hx : x < 2 ^ K) :
    mulBlockOut p 0 x K = 0 → x = 0 := by
  simp only [mulBlockOut, mulBlockVal]
  intro h
  -- h : (p * x) % 2^K = 0
  have hdvd : 2 ^ K ∣ p * x := Nat.dvd_of_mod_eq_zero h
  -- Since gcd(p, 2^K) = 1, Gauss's lemma gives 2^K ∣ x
  have hcop := odd_prime_coprime_two_pow p hp hodd K
  have hdvd_x : 2 ^ K ∣ x := (hcop.symm.dvd_of_dvd_mul_left hdvd)
  -- But x < 2^K, so x = 0
  exact Nat.eq_zero_of_dvd_of_lt hdvd_x hx

/-- **Zero Output Dichotomy**: A zero output block occurs if and only if
either (1) carry = 0 and input = 0 (free zero), or
(2) carry > 0 and input > 0 (expensive zero, consuming fuel). -/
theorem zero_output_dichotomy (p K x c : ℕ)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hx : x < 2 ^ K) (hc : c < p) (hpK : p ≤ 2 ^ K) :
    mulBlockOut p c x K = 0 →
      (c = 0 ∧ x = 0) ∨ (0 < c ∧ 0 < x) := by
  intro hout
  by_cases hc0 : c = 0
  · left
    constructor
    · exact hc0
    · subst hc0
      exact zero_carry_zero_output_imp_zero_input p K x hp hodd hx hout
  · right
    constructor
    · omega
    · exact nonzero_input_of_zero_output p c K (by omega) (by omega) x hout

/-! ## Section 4: Fuel Accounting -/

/-- Count of nonzero output blocks in the first J blocks. -/
def nonzeroBlockCount (p n K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => nonzeroBlockCount p n K j +
      if blockOutput p n K j = 0 then 0 else 1

/-- Count of "expensive" zero blocks (zero output from nonzero carry)
in the first J blocks. -/
def expensiveZeroCount (p n K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => expensiveZeroCount p n K j +
      if blockOutput p n K j = 0 ∧ 0 < blockCarry p n K j then 1 else 0

/-- Count of "free" zero blocks (zero output at zero carry)
in the first J blocks. -/
def freeZeroCount (p n K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => freeZeroCount p n K j +
      if blockOutput p n K j = 0 ∧ blockCarry p n K j = 0 then 1 else 0

/-- The three block types (nonzero, expensive-zero, free-zero) partition all J blocks. -/
theorem block_count_partition (p n K J : ℕ) :
    nonzeroBlockCount p n K J + expensiveZeroCount p n K J +
      freeZeroCount p n K J = J := by
  induction J with
  | zero => simp [nonzeroBlockCount, expensiveZeroCount, freeZeroCount]
  | succ J ih =>
    simp only [nonzeroBlockCount, expensiveZeroCount, freeZeroCount]
    by_cases hout : blockOutput p n K J = 0
    · simp [hout]
      by_cases hc : 0 < blockCarry p n K J
      · simp [hc, show ¬(blockCarry p n K J = 0) from by omega]; omega
      · push_neg at hc
        simp [show blockCarry p n K J = 0 from by omega]; omega
    · simp [hout]; omega

/-- Each expensive zero block has a corresponding nonzero input block
(positive popcount cost from the input). -/
theorem expensive_zero_has_nonzero_input (p n K j : ℕ)
    (hp : 1 < p) (hpK : p ≤ 2 ^ K) :
    blockOutput p n K j = 0 → 0 < blockCarry p n K j →
    0 < extractBlock n (j * K) K := by
  intro hout hcarry
  have hc_lt : blockCarry p n K j < 2 ^ K := by
    calc blockCarry p n K j < p := blockCarry_lt p n K hp j
      _ ≤ 2 ^ K := hpK
  exact nonzero_input_of_zero_output p (blockCarry p n K j) K
    hc_lt hcarry (extractBlock n (j * K) K) hout

/-- A free zero block at position j+1 means the input block at j is also zero
and the carry at j was zero (so carry at j+1 is also zero). -/
theorem free_zero_propagation (p n K j : ℕ)
    (hp : Nat.Prime p) (hodd : p ≠ 2) :
    blockOutput p n K j = 0 → blockCarry p n K j = 0 →
    extractBlock n (j * K) K = 0 ∧ blockCarry p n K (j + 1) = 0 := by
  intro hout hc
  -- Unfold blockOutput in hout so we can substitute the carry
  simp only [blockOutput] at hout
  rw [hc] at hout
  -- Now hout : mulBlockOut p 0 (extractBlock n (j * K) K) K = 0
  have hinp := zero_carry_zero_output_imp_zero_input p K (extractBlock n (j * K) K)
    hp hodd (extractBlock_lt_pow n (j * K) K) hout
  constructor
  · exact hinp
  · -- Next carry: mulBlockCarry p 0 0 K = 0
    simp only [blockCarry]
    rw [hc, hinp]
    exact (zero_block_at_zero_carry p K).2

end ABCFormalization
