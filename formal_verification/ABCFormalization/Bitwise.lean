/-
Copyright (c) 2025 Lukas Cain. All rights reserved.
Released under Apache 2.0 license.

# Bitwise arithmetic lemmas for the ABC formalization

This file proves the core bitwise identities underlying the carry-entropy
framework:
- The half-adder identity: `a + b = (a ^^^ b) + 2 * (a &&& b)`
- Popcount additivity for bit-disjoint numbers
- Laminar flow equivalence: `carry_friction = 0 ↔ bit-disjoint`
- Parity collision: distinct odd prime powers are never bit-disjoint
- Carry friction positivity when bits overlap
-/

import ABCFormalization.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.BinaryRec

open Nat ABCFormalization

namespace ABCFormalization

/-! ## The half-adder identity

The fundamental identity `a + b = (a ^^^ b) + 2 * (a &&& b)` expressing
addition in terms of XOR (sum without carries) and AND (carry generation).
-/

/-- The half-adder identity for natural numbers:
`a + b = (a ^^^ b) + 2 * (a &&& b)`.

This expresses addition as XOR (carry-free sum) plus twice the AND
(carry generation). It is the foundation of the carry-entropy framework. -/
theorem add_eq_xor_add_two_mul_and (a b : ℕ) :
    a + b = (a ^^^ b) + 2 * (a &&& b) := by
  -- Double induction on binary representations.
  -- Key idea: decompose a = bit a₀ a', b = bit b₀ b', then:
  --   LHS = 2*(a'+b') + (a₀.toNat + b₀.toNat)
  --   RHS = 2*((a'^^^b') + 2*(a'&&&b')) + (bne a₀ b₀).toNat + 2*(a₀&&b₀).toNat
  -- By IH the inner terms match, and Bool arithmetic handles the low bits.
  -- Strong induction on a, with b universally quantified.
  -- Decompose a = bit (bodd a) (div2 a) and similarly for b,
  -- then use xor_bit/land_bit and close with Bool case analysis.
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · -- Decompose a and b into bit form
      conv_lhs => rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
      conv_rhs => rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
      rw [Nat.xor_bit, Nat.land_bit]
      simp only [Nat.bit_val]
      -- IH for div2 a (which is strictly smaller since a > 0)
      have hdlt : a.div2 < a := by
        rw [Nat.div2_val]; exact Nat.div_lt_self ha (by omega)
      have := ih a.div2 hdlt b.div2
      -- Bool case split on the low bits
      cases a.bodd <;> cases b.bodd <;>
        simp only [Bool.toNat_true, Bool.toNat_false, Bool.true_bne,
          Bool.false_bne, Bool.not_true, Bool.not_false,
          Bool.and_true, Bool.and_false] <;>
        omega

/-! ## Unconditional popcount_bit -/

/-- `popcount (bit b n) = popcount n + b.toNat` without the side condition
that `popcount_bit` requires. The edge case `bit false 0 = 0` is handled
by direct computation. -/
theorem popcount_bit' (b : Bool) (n : ℕ) :
    popcount (Nat.bit b n) = popcount n + b.toNat := by
  rcases eq_or_ne n 0 with rfl | hn
  · cases b
    · -- bit false 0 = 0
      have h1 : Nat.bit false 0 = 0 := by
        rw [Nat.bit_val, Bool.toNat_false]
      rw [h1, popcount_zero, Bool.toNat_false]
    · -- bit true 0 = 1
      have h1 : Nat.bit true 0 = 1 := by
        rw [Nat.bit_val, Bool.toNat_true]
      rw [h1, popcount_one, popcount_zero, Bool.toNat_true]
  · exact popcount_bit b n (fun h => absurd h hn)

/-! ## Popcount of XOR when AND is zero -/

/-- When `a` and `b` are bit-disjoint, the popcount of their XOR equals
the sum of their individual popcounts. Since XOR = OR when AND = 0,
there is no cancellation. -/
theorem popcount_xor_of_and_zero (a b : ℕ) (h : a &&& b = 0) :
    popcount (a ^^^ b) = popcount a + popcount b := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · -- Derive div2-level bit-disjointness and low-bit disjointness
      have hbit : Nat.bit ((a.bodd) && (b.bodd)) (a.div2 &&& b.div2) = 0 := by
        rw [← Nat.land_bit, Nat.bit_bodd_div2, Nat.bit_bodd_div2]; exact h
      have hbit_arith : 2 * (a.div2 &&& b.div2) + ((a.bodd) && (b.bodd)).toNat = 0 := by
        rw [← Nat.bit_val]; exact hbit
      have hhigh : a.div2 &&& b.div2 = 0 := by omega
      have hlow : ((a.bodd) && (b.bodd)).toNat = 0 := by omega
      -- Expand popcount using bit decomposition
      conv_lhs => rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b, Nat.xor_bit]
      rw [popcount_bit',
        show popcount a = popcount (a.div2) + (a.bodd).toNat from by
          conv_lhs => rw [← Nat.bit_bodd_div2 a]; exact popcount_bit' _ _,
        show popcount b = popcount (b.div2) + (b.bodd).toNat from by
          conv_lhs => rw [← Nat.bit_bodd_div2 b]; exact popcount_bit' _ _]
      -- Apply IH for div2 a
      have hdlt : a.div2 < a := by
        rw [Nat.div2_val]; exact Nat.div_lt_self ha (by omega)
      have ihres := ih a.div2 hdlt b.div2 hhigh
      -- Substitute IH directly into goal, eliminating popcount(xor)
      rw [ihres]
      -- After rw, goal is pure arithmetic + Bool; close by case analysis
      -- Bool case split with explicit substitution hypotheses
      -- Prove the Bool identity: bne.toNat = x.toNat + y.toNat when (x && y).toNat = 0
      suffices h : (bne a.bodd b.bodd).toNat + (popcount a.div2 + popcount b.div2) =
          a.bodd.toNat + b.bodd.toNat + (popcount a.div2 + popcount b.div2) by omega
      congr 1
      revert hlow
      cases a.bodd <;> cases b.bodd <;> simp [Bool.toNat]

/-! ## Addition of bit-disjoint numbers -/

/-- When `a` and `b` are bit-disjoint, `a + b = a ^^^ b = a ||| b`.
No carries occur in the addition. -/
theorem add_eq_xor_of_and_zero (a b : ℕ) (h : a &&& b = 0) :
    a + b = a ^^^ b := by
  -- From the half-adder identity with a &&& b = 0
  have := add_eq_xor_add_two_mul_and a b
  rw [h] at this
  omega

/-- Bit-disjoint addition equals bitwise OR. -/
theorem add_eq_or_of_and_zero (a b : ℕ) (h : a &&& b = 0) :
    a + b = a ||| b := by
  rw [add_eq_xor_of_and_zero a b h]
  -- xor = or when and = 0: prove bitwise via testBit
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_lor]
  -- Since a &&& b = 0, at each position at most one bit is set
  have hi : (a &&& b).testBit i = false := by rw [h]; simp
  rw [Nat.testBit_land] at hi
  -- So bne and || coincide when at most one is true
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

/-! ## Popcount subadditivity -/

/-- Adding 1 increases popcount by at most 1. -/
private theorem popcount_succ_le (n : ℕ) : popcount (n + 1) ≤ popcount n + 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [popcount_one]
    · cases hb : n.bodd
      · -- n is even: n = bit false (div2 n)
        -- n + 1 = bit true (div2 n), popcount increases by exactly 1
        have hn_eq : n = Nat.bit false n.div2 := by
          conv_lhs => rw [← Nat.bit_bodd_div2 n, hb]
        have hn1_eq : n + 1 = Nat.bit true n.div2 := by
          rw [hn_eq, Nat.bit_val, Nat.bit_val]; simp [Bool.toNat]
        rw [hn1_eq, hn_eq, popcount_bit', popcount_bit']
        simp [Bool.toNat]
      · -- n is odd: n = bit true (div2 n)
        -- n + 1 = 2*(div2 n + 1), carry propagates
        have hdlt : n.div2 < n := by
          rw [Nat.div2_val]; exact Nat.div_lt_self hn (by omega)
        -- popcount n = popcount (div2 n) + 1
        have hpn : popcount n = popcount n.div2 + 1 := by
          conv_lhs => rw [← Nat.bit_bodd_div2 n, hb]
          rw [popcount_bit']; simp [Bool.toNat]
        -- popcount (n+1) = popcount (div2 n + 1) (since n+1 = 2*(div2 n + 1))
        have hpn1 : popcount (n + 1) = popcount (n.div2 + 1) := by
          have hsucc : n + 1 = Nat.bit false (n.div2 + 1) := by
            rw [Nat.bit_val, Bool.toNat_false]
            have := (Nat.bit_bodd_div2 n).symm
            rw [hb, Nat.bit_val, Bool.toNat_true] at this; omega
          rw [hsucc, popcount_bit', Bool.toNat_false, Nat.add_zero]
        rw [hpn1, hpn]
        have := ih n.div2 hdlt
        omega

/-- Popcount is subadditive: `popcount(a + b) ≤ popcount(a) + popcount(b)`.
This ensures `carry_friction` doesn't underflow with `Nat` subtraction. -/
theorem popcount_add_le (a b : ℕ) :
    popcount (a + b) ≤ popcount a + popcount b := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · -- Decompose a = bit a₀ a', b = bit b₀ b'
      conv_lhs => rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
      -- Expand popcount of a and b
      rw [show popcount a = popcount a.div2 + a.bodd.toNat from by
            conv_lhs => rw [← Nat.bit_bodd_div2 a]; exact popcount_bit' _ _,
          show popcount b = popcount b.div2 + b.bodd.toNat from by
            conv_lhs => rw [← Nat.bit_bodd_div2 b]; exact popcount_bit' _ _]
      -- IH for div2 a
      have hdlt : a.div2 < a := by
        rw [Nat.div2_val]; exact Nat.div_lt_self ha (by omega)
      -- Case split on low bits
      cases ha0 : a.bodd <;> cases hb0 : b.bodd
      · -- false, false: sum = 2*(a'+b') = bit false (a'+b')
        simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
        -- 2*a' + 2*b' = 2*(a'+b'), popcount(bit false (a'+b')) = popcount(a'+b')
        rw [show 2 * a.div2 + 2 * b.div2 = Nat.bit false (a.div2 + b.div2) from by
          rw [Nat.bit_val]; simp [Bool.toNat]; ring]
        rw [popcount_bit']
        simp only [Bool.toNat_false, Nat.add_zero]
        exact ih a.div2 hdlt b.div2
      · -- false, true: sum = 2*(a'+b') + 1 = bit true (a'+b')
        simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
        rw [show 2 * a.div2 + (2 * b.div2 + 1) = Nat.bit true (a.div2 + b.div2) from by
          rw [Nat.bit_val]; simp [Bool.toNat]; ring]
        rw [popcount_bit']
        simp only [Bool.toNat_true]
        have := ih a.div2 hdlt b.div2
        omega
      · -- true, false: sum = 2*(a'+b') + 1 = bit true (a'+b')
        simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
        rw [show 2 * a.div2 + 1 + 2 * b.div2 = Nat.bit true (a.div2 + b.div2) from by
          rw [Nat.bit_val]; simp [Bool.toNat]; ring]
        rw [popcount_bit']
        simp only [Bool.toNat_true]
        have := ih a.div2 hdlt b.div2
        omega
      · -- true, true: sum = 2*(a'+b'+1), carry propagation
        simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
        rw [show 2 * a.div2 + 1 + (2 * b.div2 + 1) = Nat.bit false (a.div2 + b.div2 + 1) from by
          rw [Nat.bit_val]; simp [Bool.toNat]; ring]
        rw [popcount_bit']
        simp only [Bool.toNat_false, Nat.add_zero]
        -- Need: popcount(a'+b'+1) ≤ popcount a' + popcount b' + 2
        -- By IH: popcount(a' + (b'+1)) ≤ popcount a' + popcount(b'+1)
        -- By popcount_succ_le: popcount(b'+1) ≤ popcount b' + 1
        have h1 := ih a.div2 hdlt (b.div2 + 1)
        have h2 := popcount_succ_le b.div2
        rw [show a.div2 + (b.div2 + 1) = a.div2 + b.div2 + 1 from by omega] at h1
        omega

/-! ## Laminar flow equivalence -/

/-- **Laminar flow equivalence** (Lemma 2.3 from the paper):
`carry_friction a b = 0` if and only if `a` and `b` are bit-disjoint.

Equivalently, binary addition produces zero carries iff the summands
have no overlapping 1-bits. -/
theorem laminar_flow_equivalence (a b : ℕ) :
    carry_friction a b = 0 ↔ isLaminar a b := by
  constructor
  · -- Forward: carry_friction = 0 → a &&& b = 0
    intro hcf
    rw [isLaminar]
    unfold carry_friction at hcf
    have hle := popcount_add_le a b
    -- carry_friction = 0 means popcount(a+b) = popcount a + popcount b
    -- Prove: popcount equality implies bit-disjointness, by strong induction on a
    suffices ∀ (a b : ℕ), popcount (a + b) = popcount a + popcount b → a &&& b = 0 from
      this a b (by omega)
    clear hcf hle a b
    intro a
    induction a using Nat.strongRecOn with
    | _ a ih =>
      intro b heq
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · -- Decompose a and b via bit_bodd_div2
        -- First rewrite the land goal
        conv_lhs => rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
        rw [Nat.land_bit]
        -- Need: bit (a.bodd && b.bodd) (div2 a &&& div2 b) = 0
        -- This holds iff (a.bodd && b.bodd) = false AND (div2 a &&& div2 b) = 0
        -- Expand popcount in heq
        rw [show popcount a = popcount a.div2 + a.bodd.toNat from by
              conv_lhs => rw [← Nat.bit_bodd_div2 a]; exact popcount_bit' _ _,
            show popcount b = popcount b.div2 + b.bodd.toNat from by
              conv_lhs => rw [← Nat.bit_bodd_div2 b]; exact popcount_bit' _ _] at heq
        -- Expand the sum a + b
        conv_lhs at heq => rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
        simp only [Nat.bit_val] at heq
        have hdlt : a.div2 < a := by
          rw [Nat.div2_val]; exact Nat.div_lt_self ha (by omega)
        -- Case split on low bits
        cases ha0 : a.bodd <;> cases hb0 : b.bodd <;>
          simp only [ha0, hb0, Bool.toNat_false, Bool.toNat_true, Bool.false_and,
            Bool.true_and, Bool.and_false, Bool.and_true] at heq ⊢
        · -- false, false: sum = bit false (a'+b'), popcount preserved
          rw [show 2 * a.div2 + 0 + (2 * b.div2 + 0) =
              Nat.bit false (a.div2 + b.div2) from by
            rw [Nat.bit_val]; simp [Bool.toNat]; ring, popcount_bit'] at heq
          simp only [Bool.toNat_false, Nat.add_zero] at heq
          rw [Nat.bit_val, Bool.toNat_false]; simp
          exact ih a.div2 hdlt b.div2 heq
        · -- false, true: sum = bit true (a'+b')
          rw [show 2 * a.div2 + 0 + (2 * b.div2 + 1) =
              Nat.bit true (a.div2 + b.div2) from by
            rw [Nat.bit_val]; simp [Bool.toNat]; ring, popcount_bit'] at heq
          simp only [Bool.toNat_true] at heq
          rw [Nat.bit_val, Bool.toNat_false]; simp
          exact ih a.div2 hdlt b.div2 (by omega)
        · -- true, false: sum = bit true (a'+b')
          rw [show 2 * a.div2 + 1 + (2 * b.div2 + 0) =
              Nat.bit true (a.div2 + b.div2) from by
            rw [Nat.bit_val]; simp [Bool.toNat]; ring, popcount_bit'] at heq
          simp only [Bool.toNat_true] at heq
          rw [Nat.bit_val, Bool.toNat_false]; simp
          exact ih a.div2 hdlt b.div2 (by omega)
        · -- true, true: CONTRADICTION
          -- sum = bit false (a'+b'+1), popcount = popcount(a'+b'+1)
          rw [show 2 * a.div2 + 1 + (2 * b.div2 + 1) =
              Nat.bit false (a.div2 + b.div2 + 1) from by
            rw [Nat.bit_val]; simp [Bool.toNat]; ring, popcount_bit'] at heq
          simp only [Bool.toNat_false, Nat.add_zero] at heq
          -- heq: popcount(a'+b'+1) = popcount a' + popcount b' + 2
          -- But popcount(a'+b'+1) ≤ popcount(a'+b') + 1 ≤ popcount a' + popcount b' + 1
          exfalso
          have h1 := popcount_succ_le (a.div2 + b.div2)
          have h2 := popcount_add_le a.div2 b.div2
          omega
  · -- Backward: a &&& b = 0 → carry_friction = 0
    intro hlam
    unfold carry_friction
    rw [isLaminar] at hlam
    -- When bit-disjoint: a + b = a ^^^ b and popcount(a ^^^ b) = popcount a + popcount b
    have hpc := popcount_xor_of_and_zero a b hlam
    have hadd := add_eq_xor_of_and_zero a b hlam
    rw [hadd, hpc]
    omega

/-! ## Parity collision (Lemma 2.5) -/

/-- An odd natural number has its lowest bit set. -/
theorem testBit_zero_of_odd {n : ℕ} (h : ¬ 2 ∣ n) : n.testBit 0 = true := by
  rw [Nat.testBit_zero]
  simp only [decide_eq_true_eq]
  omega

/-- An odd prime power is odd. -/
theorem odd_prime_pow {p : ℕ} (hp : Nat.Prime p) (hodd : p ≠ 2) (n : ℕ) (_hn : 0 < n) :
    ¬ 2 ∣ p ^ n := by
  intro h
  have hp2 : ¬ 2 ∣ p := by
    intro h2
    have := hp.eq_one_or_self_of_dvd 2 h2
    omega
  exact hp2 (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)

/-- **Parity Collision Lemma** (Lemma 2.5 from the paper):
For distinct odd primes `p, q` and positive exponents, the prime powers
`p^n` and `q^m` are never bit-disjoint.

Both odd numbers have their lowest bit set to 1, so their AND is nonzero
at bit position 0. This means any addition `p^n + q^m` must produce at
least one carry. -/
theorem parity_collision {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hoddp : p ≠ 2) (hoddq : q ≠ 2) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ¬ isLaminar (p ^ n) (q ^ m) := by
  intro hlam
  rw [isLaminar] at hlam
  -- Both p^n and q^m are odd
  have hp_odd := odd_prime_pow hp hoddp n hn
  have hq_odd := odd_prime_pow hq hoddq m hm
  -- So both have testBit 0 = true
  have hpb := testBit_zero_of_odd hp_odd
  have hqb := testBit_zero_of_odd hq_odd
  -- Their AND at bit 0 is true
  have : (p ^ n &&& q ^ m).testBit 0 = true := by
    rw [Nat.testBit_land]; simp [hpb, hqb]
  -- But this contradicts a &&& b = 0
  have : (p ^ n &&& q ^ m) ≠ 0 := by
    intro h0
    rw [h0] at this
    simp at this
  exact this hlam

/-! ## Carry friction positivity -/

/-- If `a` and `b` share any 1-bit, carry friction is positive.
This is the contrapositive of `laminar_flow_equivalence`. -/
theorem carry_friction_pos_of_and_ne_zero (a b : ℕ) (h : a &&& b ≠ 0) :
    0 < carry_friction a b := by
  by_contra hle
  push_neg at hle
  have hzero : carry_friction a b = 0 := Nat.eq_zero_of_le_zero hle
  exact h ((laminar_flow_equivalence a b).mp hzero)

/-! ## Carry cascade helpers -/

/-- Doubling preserves popcount: `popcount(2n) = popcount(n)`. -/
theorem popcount_two_mul (n : ℕ) : popcount (2 * n) = popcount n := by
  have h : 2 * n = Nat.bit false n := by
    rw [Nat.bit_val, Bool.toNat_false]; ring
  rw [h, popcount_bit', Bool.toNat_false, Nat.add_zero]

/-- Popcount splits over XOR and AND:
`popcount(a) + popcount(b) = popcount(a ^^^ b) + 2 * popcount(a &&& b)`.
At each bit position, `a₀ + b₀ = (a₀ ⊕ b₀) + 2 * (a₀ ∧ b₀)`. -/
private theorem popcount_add_eq_xor_and (a b : ℕ) :
    popcount a + popcount b = popcount (a ^^^ b) + 2 * popcount (a &&& b) := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · -- Decompose popcount a and popcount b
      conv_lhs =>
        rw [show popcount a = popcount a.div2 + a.bodd.toNat from by
              conv_lhs => rw [← Nat.bit_bodd_div2 a]; exact popcount_bit' _ _,
            show popcount b = popcount b.div2 + b.bodd.toNat from by
              conv_lhs => rw [← Nat.bit_bodd_div2 b]; exact popcount_bit' _ _]
      -- Decompose XOR and AND via bit operations
      conv_rhs =>
        rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b,
            Nat.xor_bit, Nat.land_bit, popcount_bit', popcount_bit']
      -- Apply IH for div2 a
      have hdlt : a.div2 < a := by
        rw [Nat.div2_val]; exact Nat.div_lt_self ha (by omega)
      have ihres := ih a.div2 hdlt b.div2
      -- Close by Bool case analysis + omega
      cases a.bodd <;> cases b.bodd <;>
        simp only [Bool.toNat_true, Bool.toNat_false, Bool.true_bne,
          Bool.false_bne, Bool.not_true, Bool.not_false,
          Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and] <;>
        omega

/-- Carry friction is at least the popcount of the bitwise AND:
`popcount(a &&& b) ≤ carry_friction(a, b)`.

From the half-adder identity and popcount subadditivity:
- `popcount(a) + popcount(b) = popcount(a ^^^ b) + 2 * popcount(a &&& b)`
- `popcount(a + b) ≤ popcount(a ^^^ b) + popcount(a &&& b)`
Subtracting: `carry_friction ≥ popcount(a &&& b)`. -/
private theorem carry_friction_ge_popcount_and (a b : ℕ) :
    popcount (a &&& b) ≤ carry_friction a b := by
  unfold carry_friction
  have h_ident := popcount_add_eq_xor_and a b
  have h_half := add_eq_xor_add_two_mul_and a b
  have h_sub : popcount (a + b) ≤ popcount (a ^^^ b) + popcount (a &&& b) := by
    calc popcount (a + b)
        = popcount ((a ^^^ b) + 2 * (a &&& b)) := by rw [h_half]
      _ ≤ popcount (a ^^^ b) + popcount (2 * (a &&& b)) := popcount_add_le _ _
      _ = popcount (a ^^^ b) + popcount (a &&& b) := by rw [popcount_two_mul]
  have h_le := popcount_add_le a b
  omega

/-- If `n` has `testBit = true` at `m` consecutive positions starting at `k`,
then `popcount n ≥ m`. Proved by strong induction on `n`, shifting right
via `div2` to reduce either `k` or `m`. -/
private theorem popcount_ge_of_testBit_run (n : ℕ) (k m : ℕ)
    (h : ∀ i, i < m → n.testBit (k + i) = true) : m ≤ popcount n := by
  induction n using Nat.strongRecOn generalizing k m with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · omega
    · -- m > 0, so n.testBit k = true, hence n > 0
      have hn_pos : 0 < n := by
        by_contra h0; push_neg at h0
        have := h 0 hm_pos; simp [Nat.le_zero.mp h0] at this
      -- Key shift lemma: (div2 n).testBit i = n.testBit (i + 1)
      have htb : ∀ i, (n.div2).testBit i = n.testBit (i + 1) := by
        intro i
        have := Nat.testBit_bit_succ i n.bodd n.div2
        rw [Nat.bit_bodd_div2] at this
        exact this.symm
      -- popcount n = popcount (div2 n) + (bodd n).toNat
      have hpc : popcount n = popcount n.div2 + n.bodd.toNat := by
        conv_lhs => rw [← Nat.bit_bodd_div2 n]; exact popcount_bit' _ _
      -- div2 n < n (for IH)
      have hdlt : n.div2 < n := by
        rw [Nat.div2_val]; exact Nat.div_lt_self hn_pos (by omega)
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- Case k = 0: low bit is in the run
        have hbit0 : n.testBit 0 = true := by
          have := h 0 hm_pos; simpa using this
        have hbodd : n.bodd = true := by
          rw [Nat.testBit_zero, decide_eq_true_eq] at hbit0
          have hmod := Nat.mod_two_of_bodd n
          have heq : n.bodd.toNat = 1 := by omega
          -- Revert so cases can substitute in the goal
          revert heq; cases n.bodd <;> simp [Bool.toNat]
        -- Remaining run: div2 n has testBit true at [0, m-1)
        have hrun' : ∀ i, i < m - 1 → (n.div2).testBit (0 + i) = true := by
          intro i hi
          rw [Nat.zero_add, htb]
          have := h (i + 1) (by omega)
          simpa using this
        have ihres := ih n.div2 hdlt 0 (m - 1) hrun'
        rw [hpc, hbodd]; simp only [Bool.toNat_true]; omega
      · -- Case k > 0: run is entirely above bit 0, shift right
        have hrun' : ∀ i, i < m → (n.div2).testBit (k - 1 + i) = true := by
          intro i hi
          rw [htb]; rw [show k - 1 + i + 1 = k + i from by omega]
          exact h i hi
        have ihres := ih n.div2 hdlt (k - 1) m hrun'
        rw [hpc]; omega

/-! ## Carry cascade lower bound (Lemma 2.7) -/

/-- **Carry cascade lower bound** (Lemma 2.7 from the paper):
If `a` and `b` share a run of `m` consecutive 1-bits starting at position `k`,
then a ripple-carry adder produces at least `⌈m/2⌉` carries, hence
`carry_friction a b ≥ ⌈m/2⌉`.

The proof uses a stronger intermediate: `carry_friction ≥ popcount(a &&& b)`.
Since the shared run contributes `m` 1-bits to `a &&& b`, we get
`carry_friction ≥ m ≥ ⌈m/2⌉`. -/
theorem carry_cascade_lower_bound (a b : ℕ) (k m : ℕ) (hm : 0 < m)
    (hrun : ∀ i, i < m → a.testBit (k + i) = true ∧ b.testBit (k + i) = true) :
    (m + 1) / 2 ≤ carry_friction a b := by
  -- Step 1: From hrun, deduce (a &&& b).testBit (k + i) = true for i < m
  have hrun_and : ∀ i, i < m → (a &&& b).testBit (k + i) = true := by
    intro i hi
    rw [Nat.testBit_land]
    obtain ⟨ha, hb⟩ := hrun i hi
    simp [ha, hb]
  -- Step 2: m ≤ popcount (a &&& b)
  have h2 := popcount_ge_of_testBit_run (a &&& b) k m hrun_and
  -- Step 3: popcount (a &&& b) ≤ carry_friction a b
  have h3 := carry_friction_ge_popcount_and a b
  -- Chain: (m + 1) / 2 ≤ m ≤ popcount(a &&& b) ≤ carry_friction a b
  omega

/-! ## Parity consequences for carry friction -/

/-- If both a and b are odd, their AND is nonzero at bit 0. -/
private theorem and_ne_zero_of_both_odd {a b : ℕ} (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) :
    a &&& b ≠ 0 := by
  intro h
  have ha0 := testBit_zero_of_odd ha
  have hb0 := testBit_zero_of_odd hb
  have : (a &&& b).testBit 0 = true := by
    rw [Nat.testBit_land]; simp [ha0, hb0]
  rw [h] at this; simp at this

/-- If both a and b are odd, carry friction is at least 1.
An immediate consequence of bit-0 overlap. -/
theorem carry_friction_pos_of_both_odd (a b : ℕ) (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) :
    0 < carry_friction a b :=
  carry_friction_pos_of_and_ne_zero a b (and_ne_zero_of_both_odd ha hb)

/-- If a and b are bit-disjoint (laminar), at most one of them is odd.
Contrapositive of the bit-0 overlap argument. -/
theorem isLaminar_implies_at_most_one_odd (a b : ℕ) (hlam : isLaminar a b) :
    2 ∣ a ∨ 2 ∣ b := by
  by_contra h
  push_neg at h
  exact and_ne_zero_of_both_odd h.1 h.2 hlam

end ABCFormalization
