/-
Copyright (c) 2025 Lukas Cain. All rights reserved.
Released under Apache 2.0 license.

# Carry Transducer for Multiplication by an Odd Prime

This file formalizes the block-level carry transducer that describes how
multiplication by an odd prime p transforms binary representations.

Key results:
- `mulBlockOut`, `mulBlockCarry`: block-level transducer operations
- `mulBlock_decomp`: output + carry · 2^K = p · input + carry_in
- `mulBlockCarry_lt`: carry stays bounded in {0, ..., p-1}
- `nonzero_input_of_zero_output`: zero output from nonzero carry requires
  nonzero input (the "fuel consumption" lemma)
- `mod_block_decomp`: block-level modular decomposition
- `transducer_correct`: the block-level computation correctly gives p · n
-/

import ABCFormalization.BlockDecomposition

open Nat ABCFormalization Filter

namespace ABCFormalization

/-! ## Section 1: Block Multiplication Transducer -/

/-- The combined value when the ×p transducer processes input block `x`
with incoming carry `c`: val = p · x + c. -/
def mulBlockVal (p c x : ℕ) : ℕ := p * x + c

/-- Output block from the ×p transducer: the low K bits of val. -/
def mulBlockOut (p c x K : ℕ) : ℕ := mulBlockVal p c x % 2 ^ K

/-- Carry-out from the ×p transducer: the high bits of val. -/
def mulBlockCarry (p c x K : ℕ) : ℕ := mulBlockVal p c x / 2 ^ K

/-! ## Section 2: Fundamental Properties -/

/-- Output and carry reconstruct the full value. -/
theorem mulBlock_decomp (p c x K : ℕ) :
    mulBlockOut p c x K + mulBlockCarry p c x K * 2 ^ K = mulBlockVal p c x := by
  simp only [mulBlockOut, mulBlockCarry]
  rw [Nat.mul_comm (mulBlockVal p c x / 2 ^ K) (2 ^ K)]
  exact Nat.mod_add_div _ _

/-- The output block is always less than 2^K. -/
theorem mulBlockOut_lt (p c x K : ℕ) : mulBlockOut p c x K < 2 ^ K :=
  Nat.mod_lt _ (by positivity)

/-! ## Section 3: Carry Bound -/

/-- **Carry stays bounded**: if the input block is < 2^K and carry < p,
then the output carry is also < p. -/
theorem mulBlockCarry_lt (p c x K : ℕ) (hx : x < 2 ^ K) (hc : c < p) :
    mulBlockCarry p c x K < p := by
  simp only [mulBlockCarry, mulBlockVal]
  rw [Nat.div_lt_iff_lt_mul (show 0 < 2 ^ K from by positivity)]
  calc p * x + c
      < p * x + p := by omega
    _ = p * (x + 1) := by ring
    _ ≤ p * 2 ^ K := Nat.mul_le_mul_left p (by omega)

/-! ## Section 4: Zero-Block Analysis (Fuel Consumption) -/

/-- **Fuel Consumption Lemma**: When carry < 2^K and carry > 0,
a zero output block requires nonzero input. -/
theorem nonzero_input_of_zero_output (p c K : ℕ) (hpK : c < 2 ^ K)
    (hc : 0 < c) (x : ℕ) :
    mulBlockOut p c x K = 0 → 0 < x := by
  intro hout
  by_contra hx
  push_neg at hx
  have hx0 : x = 0 := by omega
  subst hx0
  simp only [mulBlockOut, mulBlockVal, Nat.mul_zero, Nat.zero_add] at hout
  have : c % 2 ^ K = c := Nat.mod_eq_of_lt hpK
  omega

/-- The carry-0 self-loop: zero input with zero carry gives zero output
and zero carry. -/
theorem zero_block_at_zero_carry (p K : ℕ) :
    mulBlockOut p 0 0 K = 0 ∧ mulBlockCarry p 0 0 K = 0 := by
  simp [mulBlockOut, mulBlockCarry, mulBlockVal]

/-! ## Section 5: Recursive Carry Computation -/

/-- The carry at block position j when computing p · n with K-bit blocks. -/
def blockCarry (p n K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => mulBlockCarry p (blockCarry p n K j) (extractBlock n (j * K) K) K

/-- The block-level output at position j. -/
def blockOutput (p n K j : ℕ) : ℕ :=
  mulBlockOut p (blockCarry p n K j) (extractBlock n (j * K) K) K

/-- The assembled output after processing J blocks. -/
def blockAssembled (p n K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => blockAssembled p n K j + blockOutput p n K j * 2 ^ (j * K)

/-! ## Section 6: Block Decomposition Identity -/

/-- Block decomposition: `n % 2^((j+1)·K) = n % 2^(j·K) + extractBlock(n,j·K,K)·2^(j·K)`. -/
theorem mod_block_decomp (n j K : ℕ) :
    n % 2 ^ ((j + 1) * K) =
      n % 2 ^ (j * K) + extractBlock n (j * K) K * 2 ^ (j * K) := by
  unfold extractBlock
  -- Let a = 2^(j*K), b = 2^K
  set a := 2 ^ (j * K)
  set b := 2 ^ K
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  -- 2^((j+1)*K) = b * a
  have hpow : 2 ^ ((j + 1) * K) = b * a := by
    rw [show (j + 1) * K = K + j * K from by ring, pow_add]
  rw [hpow]
  -- Goal: n % (b * a) = n % a + (n / a) % b * a
  -- Euclidean divisions
  have h1 : a * (n / a) + n % a = n := Nat.div_add_mod n a
  have h2 : b * (n / a / b) + (n / a) % b = n / a := Nat.div_add_mod (n / a) b
  have h3 : n / a / b = n / (b * a) := by
    rw [Nat.div_div_eq_div_mul n a b, Nat.mul_comm]
  -- Remainder bound
  have hrest_lt : n % a + (n / a) % b * a < b * a := by
    have : n % a < a := Nat.mod_lt n ha
    have : (n / a) % b < b := Nat.mod_lt (n / a) hb
    nlinarith
  -- Key: (b*a) * (n / (b*a)) + (n%a + (n/a)%b * a) = n
  have hdecomp : (b * a) * (n / (b * a)) + (n % a + (n / a) % b * a) = n := by
    calc (b * a) * (n / (b * a)) + (n % a + (n / a) % b * a)
        = (b * a) * (n / a / b) + (n % a + (n / a) % b * a) := by rw [h3]
      _ = a * (b * (n / a / b) + (n / a) % b) + n % a := by ring
      _ = a * (n / a) + n % a := by rw [h2]
      _ = n := h1
  -- Standard: (b*a) * (n / (b*a)) + n % (b*a) = n
  have huniq : (b * a) * (n / (b * a)) + n % (b * a) = n := Nat.div_add_mod n (b * a)
  -- Both decompositions give the same n, same quotient, so same remainder
  omega

/-! ## Section 7: Transducer Correctness -/

/-- **Transducer Correctness**: after processing J blocks of n, the
assembled output plus carry · 2^(J·K) equals p · (n mod 2^(J·K)). -/
theorem transducer_correct (p n K : ℕ) :
    ∀ J, blockAssembled p n K J + blockCarry p n K J * 2 ^ (J * K) =
      p * (n % 2 ^ (J * K)) := by
  intro J
  induction J with
  | zero =>
    simp [blockAssembled, blockCarry, pow_zero, Nat.mod_one]
  | succ J ih =>
    simp only [blockAssembled, blockOutput, blockCarry]
    set b := extractBlock n (J * K) K
    set c := blockCarry p n K J
    -- mulBlock_decomp: out + cout * 2^K = p * b + c
    have hdecomp := mulBlock_decomp p c b K
    -- mod_block_decomp: n % 2^((J+1)*K) = n % 2^(J*K) + b * 2^(J*K)
    have hrhs := mod_block_decomp n J K
    -- 2^((J+1)*K) = 2^K * 2^(J*K)
    have hpow : 2 ^ ((J + 1) * K) = 2 ^ K * 2 ^ (J * K) := by
      rw [show (J + 1) * K = K + J * K from by ring, pow_add]
    -- Factor: out * M + cout * 2^((J+1)*K) = (out + cout * 2^K) * M
    have hfactor :
        mulBlockOut p c b K * 2 ^ (J * K) +
        mulBlockCarry p c b K * 2 ^ ((J + 1) * K) =
        (mulBlockOut p c b K + mulBlockCarry p c b K * 2 ^ K) * 2 ^ (J * K) := by
      rw [hpow]; ring
    -- Reassociate so we can rewrite with hfactor
    have hassoc :
        blockAssembled p n K J + mulBlockOut p c b K * 2 ^ (J * K) +
        mulBlockCarry p c b K * 2 ^ ((J + 1) * K) =
        blockAssembled p n K J +
        (mulBlockOut p c b K * 2 ^ (J * K) +
         mulBlockCarry p c b K * 2 ^ ((J + 1) * K)) := by ring
    rw [hassoc, hfactor, hdecomp]
    -- Goal: assembled + mulBlockVal p c b * 2^(J*K) = p * (n % 2^((J+1)*K))
    simp only [mulBlockVal]
    -- Goal: assembled + (p*b + c) * 2^(J*K) = p * (n % 2^((J+1)*K))
    rw [hrhs, Nat.mul_add]
    -- Rearrange to use ih
    have : blockAssembled p n K J + (p * b + c) * 2 ^ (J * K) =
        (blockAssembled p n K J + c * 2 ^ (J * K)) + p * b * 2 ^ (J * K) := by ring
    rw [this, ih]
    ring

end ABCFormalization
