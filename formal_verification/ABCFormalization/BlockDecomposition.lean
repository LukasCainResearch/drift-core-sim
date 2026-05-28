/-
Copyright (c) 2025 Lukas Cain. All rights reserved.
Released under Apache 2.0 license.

# Block Decomposition

This file establishes the block decomposition infrastructure for binary
representations, providing the foundation for the carry transducer analysis.

Key results:
- `extractBlock`: extracts a K-bit window from position lo
- `popcount_split`: popcount decomposes across bit boundaries
- `mod_block_decomp`: block decomposition of n mod 2^((J+1)·K)
- `size_prime_pow_ge`: bit-length of p^n is at least n + 1
-/

import ABCFormalization.Bitwise
import Mathlib.Data.Nat.Log

open Nat ABCFormalization

namespace ABCFormalization

/-! ## Section 1: Block extraction -/

/-- Extract K bits from position lo: the K-bit window [lo, lo+K). -/
def extractBlock (n lo K : ℕ) : ℕ := (n / 2 ^ lo) % 2 ^ K

/-- The 0th block is just n mod 2^K. -/
theorem extractBlock_zero_lo (n K : ℕ) : extractBlock n 0 K = n % 2 ^ K := by
  simp [extractBlock]

/-- Every extracted block is less than 2^K. -/
theorem extractBlock_lt (n lo K : ℕ) : extractBlock n lo K < 2 ^ K :=
  Nat.mod_lt _ (by positivity)

/-! ## Section 2: Arithmetic helpers for popcount split -/

/-- Mod identity: (bit b m) % 2^(K+1) = bit b (m % 2^K).
Decomposes the bottom K+1 bits into the K-th bit and the bottom K bits. -/
private lemma bit_mod_two_pow_succ (b : Bool) (m K : ℕ) :
    (Nat.bit b m) % 2 ^ (K + 1) = Nat.bit b (m % 2 ^ K) := by
  simp only [Nat.bit_val, pow_succ]
  -- Goal: (2 * m + b.toNat) % (2^K * 2) = 2 * (m % 2^K) + b.toNat
  have hK_pos : (0 : ℕ) < 2 ^ K := by positivity
  have hb_bound : b.toNat ≤ 1 := by cases b <;> simp [Bool.toNat]
  have hmod_lt : m % 2 ^ K < 2 ^ K := Nat.mod_lt m hK_pos
  have hrhs_lt : 2 * (m % 2 ^ K) + b.toNat < 2 ^ K * 2 := by omega
  -- Decompose: 2*m + b = (2^K * 2) * (m / 2^K) + (2*(m%2^K) + b)
  set q := m / 2 ^ K
  set r := m % 2 ^ K
  have heq : m = 2 ^ K * q + r := (Nat.div_add_mod m (2 ^ K)).symm
  have h_decomp : 2 * m + b.toNat =
      (2 * r + b.toNat) + (2 ^ K * 2) * q := by
    calc 2 * m + b.toNat
        = 2 * (2 ^ K * q + r) + b.toNat := by rw [heq]
      _ = (2 * r + b.toNat) + (2 ^ K * 2) * q := by ring
  conv_lhs => rw [h_decomp]
  -- Goal: ((2*r + b.toNat) + (2^K*2) * q) % (2^K*2) = 2*r + b.toNat
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hrhs_lt

/-- Div identity: (bit b m) / 2^(K+1) = m / 2^K.
Shifting past the lowest bit doesn't change the upper quotient. -/
private lemma bit_div_two_pow_succ (b : Bool) (m K : ℕ) :
    (Nat.bit b m) / 2 ^ (K + 1) = m / 2 ^ K := by
  rw [Nat.bit_val, pow_succ, show 2 ^ K * 2 = 2 * 2 ^ K from by ring,
      ← Nat.div_div_eq_div_mul]
  -- Goal: (2 * m + b.toNat) / 2 / 2^K = m / 2^K
  congr 1
  -- Goal: (2 * m + b.toNat) / 2 = m
  have hb_bound : b.toNat ≤ 1 := by cases b <;> simp [Bool.toNat]
  rw [show 2 * m + b.toNat = b.toNat + m * 2 from by ring]
  rw [Nat.add_mul_div_right _ _ (by omega : (0 : ℕ) < 2)]
  simp [Nat.div_eq_of_lt (by omega : b.toNat < 2)]

/-! ## Section 3: Popcount splits across bit boundaries -/

/-- **Popcount split**: popcount decomposes across any bit boundary.
`popcount n = popcount (n % 2^K) + popcount (n / 2^K)`.

This is the key structural lemma: the popcount of a number equals the
popcount of its lower K bits plus the popcount of its upper bits. -/
theorem popcount_split (n K : ℕ) :
    popcount n = popcount (n % 2 ^ K) + popcount (n / 2 ^ K) := by
  induction K generalizing n with
  | zero => simp [Nat.mod_one, popcount_zero]
  | succ K ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [popcount_zero]
    · -- popcount n = n.bodd.toNat + popcount n.div2
      have h_low : popcount n = n.bodd.toNat + popcount n.div2 := by
        conv_lhs => rw [← Nat.bit_bodd_div2 n]
        rw [popcount_bit']; omega
      -- n % 2^(K+1) = bit (n.bodd) (n.div2 % 2^K)
      have h_mod : n % 2 ^ (K + 1) = Nat.bit n.bodd (n.div2 % 2 ^ K) := by
        conv_lhs => rw [← Nat.bit_bodd_div2 n]
        exact bit_mod_two_pow_succ n.bodd n.div2 K
      -- n / 2^(K+1) = n.div2 / 2^K
      have h_div : n / 2 ^ (K + 1) = n.div2 / 2 ^ K := by
        conv_lhs => rw [← Nat.bit_bodd_div2 n]
        exact bit_div_two_pow_succ n.bodd n.div2 K
      -- Apply IH to n.div2 at K
      have h_ih := ih n.div2
      -- Rewrite and combine
      rw [h_mod, h_div, popcount_bit']
      omega

/-! ## Section 4: Block shift identity -/

/-- Shifting by K: the j-th block of n/2^K equals the (j+1)-th block of n. -/
theorem extractBlock_shift (n K j : ℕ) :
    extractBlock (n / 2 ^ K) (j * K) K = extractBlock n ((j + 1) * K) K := by
  simp only [extractBlock]
  congr 1
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 1
  ring

/-! ## Section 5: Block-level positivity implies popcount lower bound -/

/-- If every K-bit block of n has at least one 1-bit, then
popcount n is at least the number of such blocks. -/
theorem popcount_ge_of_blocks_pos (n K m : ℕ) (_hK : 0 < K)
    (hblocks : ∀ j, j < m → 0 < popcount (extractBlock n (j * K) K)) :
    m ≤ popcount n := by
  induction m generalizing n with
  | zero => omega
  | succ m ih =>
    -- The 0th block is n % 2^K
    have h0 : 0 < popcount (n % 2 ^ K) := by
      have := hblocks 0 (by omega)
      simp only [zero_mul] at this
      rwa [extractBlock_zero_lo] at this
    -- The remaining blocks are blocks of n / 2^K
    have hrest : ∀ j, j < m → 0 < popcount (extractBlock (n / 2 ^ K) (j * K) K) := by
      intro j hj
      have := hblocks (j + 1) (by omega)
      rwa [← extractBlock_shift] at this
    -- IH gives popcount(n/2^K) ≥ m
    have ihm := ih (n / 2 ^ K) hrest
    -- popcount_split decomposes popcount n
    rw [popcount_split n K]
    omega

/-! ## Section 6: Size bounds for prime powers -/

/-- For any prime p, the bit-length of p^n is at least n + 1.
Since p ≥ 2, we have p^n ≥ 2^n, and 2^n requires n + 1 bits. -/
theorem size_prime_pow_ge {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    n + 1 ≤ Nat.size (p ^ n) := by
  by_contra h
  push_neg at h
  have hle : Nat.size (p ^ n) ≤ n := by omega
  have h1 := Nat.lt_size_self (p ^ n)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 from by omega) hle
  have h3 := Nat.pow_le_pow_left hp.two_le n
  omega

/-! ## Section 7: Arithmetic for K=3 derivation -/

/-- For s ≥ 9: s < 4 * (s / 3).
Since s = 3q + r with r ≤ 2 and q ≥ 3, we get 4q > 3q + r = s. -/
private theorem size_lt_four_mul_div_three {s : ℕ} (hs : 9 ≤ s) : s < 4 * (s / 3) := by
  omega

/-! ## Section 8: Carry Transducer Popcount Infrastructure

The carry transducer framework (CarryTransducer.lean, CarryGraph.lean,
FuelAccounting.lean, FuelRecursion.lean) provides a self-regulating feedback
mechanism for popcount bounds on products p · n:

- Every "disagreement" between the carry state and the input block forces
  nonzero output (case B: carry=0, input>0; case C: carry>0, input=0)
- The zero-output dichotomy (CarryGraph) shows that zero output requires
  either carry=input=0 (free zero) or carry>0 ∧ input>0 (expensive zero)
- The fuel recursion bound gives popcount(p·n) ≥ caseBcount + caseCcount ≥ 1
  for any positive n (FuelRecursion.popcount_mul_pos)

The main formalization results (carry conservation law, stress tensor L1 ≥ 1,
laminar scarcity, smooth exclusion) are proved without any axioms. -/

end ABCFormalization
