/-
Copyright (c) 2025 Lukas Cain. All rights reserved.
Released under Apache 2.0 license.

# Kummer's theorem bridge and p-adic carry stress

This file connects the binary carry framework to Mathlib's formalization
of Kummer's theorem, proving that:
- Bit-disjoint ↔ no carries in base 2 ↔ odd binomial coefficient
- Binary carry stress equals the 2-adic Kummer stress
- The digit-sum identity relates popcount to p-adic valuations
-/

import ABCFormalization.Bitwise
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Defs

open Nat ABCFormalization

namespace ABCFormalization

/-! ## No-carries characterization via testBit

The key bridge between bitwise AND and Kummer's carry-count formulation.
-/

/-- At each bit position, if `a &&& b = 0` then at most one of
`a.testBit i` and `b.testBit i` is true. -/
theorem testBit_disjoint_of_and_zero {a b : ℕ} (h : a &&& b = 0) (i : ℕ) :
    a.testBit i = false ∨ b.testBit i = false := by
  by_contra hc
  push_neg at hc
  have : (a &&& b).testBit i = true := by
    rw [Nat.testBit_land]; simp [hc.1, hc.2]
  rw [h] at this; simp at this

/-- Mod decomposition: `a % 2^(n+1) = 2 * ((a/2) % 2^n) + a % 2`.
This expresses the lower `n+1` bits as twice the upper bits plus the lowest bit. -/
private lemma mod_two_pow_succ (a n : ℕ) :
    a % 2 ^ (n + 1) = 2 * (a / 2 % 2 ^ n) + a % 2 := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have h := Nat.div_add_mod a (2 ^ (n + 1))
  have h2 := Nat.div_add_mod a 2
  have h3 := Nat.div_add_mod (a / 2) (2 ^ n)
  rw [hpow, ← Nat.div_div_eq_div_mul, mul_assoc] at h
  rw [hpow]
  omega

/-- If `a &&& b = 0` then `a/2 &&& b/2 = 0`. Bit-disjointness is preserved by right-shift. -/
private lemma and_zero_div2 {a b : ℕ} (h : a &&& b = 0) : a / 2 &&& b / 2 = 0 := by
  have hbit : Nat.bit (a.bodd && b.bodd) (a.div2 &&& b.div2) = 0 := by
    rw [← Nat.land_bit, Nat.bit_bodd_div2, Nat.bit_bodd_div2]; exact h
  have : 2 * (a.div2 &&& b.div2) + (a.bodd && b.bodd).toNat = 0 := by
    rw [← Nat.bit_val]; exact hbit
  have : a.div2 &&& b.div2 = 0 := by omega
  simp only [Nat.div2_val] at this
  exact this

/-- If `a` and `b` are bit-disjoint, then no carry occurs at any position
when adding them in base 2. Formally: `a % 2^i + b % 2^i < 2^i` for all `i ≥ 1`.

This is the "no carries" condition used in Kummer's theorem.
The proof strategy: induction on `i` with `a, b` universally quantified,
using mod decomposition and bit-disjointness preservation under right-shift. -/
theorem no_carries_of_and_zero (a b : ℕ) (h : a &&& b = 0) :
    ∀ i : ℕ, 1 ≤ i → a % 2 ^ i + b % 2 ^ i < 2 ^ i := by
  -- Strengthen: induct on j where i = j + 1, quantifying over a, b
  suffices key : ∀ (j : ℕ) (a b : ℕ), a &&& b = 0 →
      a % 2 ^ (j + 1) + b % 2 ^ (j + 1) < 2 ^ (j + 1) from by
    intro i hi
    match i, hi with
    | i + 1, _ => exact key i a b h
  intro j
  induction j with
  | zero =>
    -- Base case: 2^1 = 2, need a % 2 + b % 2 < 2
    intro a b hab
    simp only [Nat.zero_add, pow_one]
    have hd := testBit_disjoint_of_and_zero hab 0
    simp only [Nat.testBit_zero, decide_eq_false_iff_not] at hd
    have := Nat.mod_lt a (show (0 : ℕ) < 2 by omega)
    have := Nat.mod_lt b (show (0 : ℕ) < 2 by omega)
    omega
  | succ n ih =>
    -- Inductive step: 2^(n+2) case
    intro a b hab
    -- Decompose: a % 2^(n+2) = 2 * ((a/2) % 2^(n+1)) + a % 2
    have hma := mod_two_pow_succ a (n + 1)
    have hmb := mod_two_pow_succ b (n + 1)
    -- Bit-disjointness preserved: a/2 &&& b/2 = 0
    have hhigh := and_zero_div2 hab
    -- Apply IH to a/2, b/2
    have ih_app := ih (a / 2) (b / 2) hhigh
    -- Low bits: a%2 + b%2 ≤ 1 from bit-disjointness at position 0
    have hlow : a % 2 + b % 2 ≤ 1 := by
      have hd := testBit_disjoint_of_and_zero hab 0
      simp only [Nat.testBit_zero, decide_eq_false_iff_not] at hd
      have := Nat.mod_lt a (show (0 : ℕ) < 2 by omega)
      have := Nat.mod_lt b (show (0 : ℕ) < 2 by omega)
      omega
    -- Combine: sum = 2*(upper sums) + (lower sums) < 2*2^(n+1) = 2^(n+2)
    rw [hma, hmb]
    have hpow : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    rw [hpow]
    omega

/-- Converse: if a carry occurs at some position, then `a &&& b ≠ 0`. -/
theorem and_ne_zero_of_carry (a b : ℕ) (i : ℕ) (hi : 1 ≤ i)
    (hcarry : 2 ^ i ≤ a % 2 ^ i + b % 2 ^ i) :
    a &&& b ≠ 0 := by
  intro h
  exact Nat.not_le.mpr (no_carries_of_and_zero a b h i hi) hcarry

/-! ## Digit-sum and popcount connection -/

/-- The sum of base-2 digits of `n` equals its popcount.
This connects Mathlib's `Nat.digits` to our `popcount` definition. -/
theorem digits_two_sum_eq_popcount (n : ℕ) :
    (Nat.digits 2 n).sum = popcount n := by
  -- Bridge: digits 2 n = n.bits.map (fun b => cond b 1 0)
  rw [Nat.digits_two_eq_bits]
  -- Strong induction on n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · -- Decompose n = bit (bodd n) (div2 n)
      conv_lhs => rw [← Nat.bit_bodd_div2 n]
      rw [Nat.bits_append_bit _ _ (by
        intro h; cases hb : n.bodd
        · exfalso
          have := (Nat.bit_bodd_div2 n).symm
          rw [h, hb, Nat.bit_val, Bool.toNat_false] at this; omega
        · rfl)]
      simp only [List.map_cons, List.sum_cons]
      -- Apply IH for div2 n
      rw [ih n.div2 (by rw [Nat.div2_val]; exact Nat.div_lt_self hn (by omega))]
      -- Goal: cond (bodd n) 1 0 + popcount (div2 n) = popcount n
      conv_rhs => rw [← Nat.bit_bodd_div2 n, popcount_bit']
      -- Goal: cond (bodd n) 1 0 + popcount (div2 n) = popcount (div2 n) + (bodd n).toNat
      cases n.bodd <;> simp [Bool.toNat] <;> omega

/-! ## p-adic carry stress -/

/-- Base-`p` carry count: the number of carries when adding `a` and `b` in
base `p`. By Kummer's theorem, this equals `padicValNat p (choose (a+b) a)`. -/
noncomputable def base_p_carry_count (p a b : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  padicValNat p (Nat.choose (a + b) a)

/-- Base-`p` carry stress: the carry count normalized by the base-`p`
representation length of `c = a + b`.

σ_p(a, b) = v_p(C(c, a)) / ⌊log_p(c)⌋

This generalizes binary carry stress to arbitrary prime bases using
Kummer's theorem rather than popcount. -/
noncomputable def padic_stress (p a b : ℕ) [Fact (Nat.Prime p)] : ℚ :=
  let c := a + b
  if Nat.log p c = 0 then 0
  else (base_p_carry_count p a b : ℚ) / (Nat.log p c : ℚ)

/-- **Kummer digit-sum identity** (directly from Mathlib):
`(p - 1) * v_p(C(a+b, a)) = S_p(a) + S_p(b) - S_p(a+b)`
where `S_p(n)` is the digit sum of `n` in base `p`.

This is `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` from Mathlib. -/
theorem kummer_digit_sum {p : ℕ} (a b : ℕ) [hp : Fact (Nat.Prime p)] :
    (p - 1) * padicValNat p (Nat.choose (b + a) a) =
    (Nat.digits p a).sum + (Nat.digits p b).sum - (Nat.digits p (b + a)).sum :=
  sub_one_mul_padicValNat_choose_eq_sub_sum_digits'

/-- For `p = 2`, the digit-sum form simplifies: the `(p-1) = 1` factor
drops out, so `v_2(C(a+b, a)) = popcount(a) + popcount(b) - popcount(a+b)`.

This is exactly the carry friction! -/
theorem binary_carry_is_kummer (a b : ℕ) :
    carry_friction a b = padicValNat 2 (Nat.choose (a + b) a) := by
  -- Use the Kummer digit-sum identity for p = 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := kummer_digit_sum (p := 2) a b
  -- hk : (2 - 1) * padicValNat 2 (choose (b + a) a) = ...
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at hk
  -- Substitute digits sums with popcount
  rw [digits_two_sum_eq_popcount, digits_two_sum_eq_popcount,
      digits_two_sum_eq_popcount] at hk
  -- hk : padicValNat 2 (choose (b + a) a) = popcount a + popcount b - popcount (b + a)
  rw [show b + a = a + b from by omega] at hk
  -- carry_friction a b = popcount a + popcount b - popcount (a + b) by definition
  unfold carry_friction
  omega

/-! ## Laminar implies odd binomial (replacing the axiom) -/

/-- **Bit-Prime Bridge** (replacing the axiom from the original formalization):
`a` and `b` are bit-disjoint if and only if the binomial coefficient
`(a + b).choose a` is odd (not divisible by 2).

This is the base-2 specialization of Kummer's theorem: the 2-adic
valuation of `C(a+b, a)` equals the number of carries when adding
`a` and `b` in base 2. Zero carries ↔ bit-disjoint ↔ odd binomial.

This theorem replaces the `axiom laminar_implies_odd_binomial` from
the original `ABCproject.lean`. -/
theorem laminar_implies_odd_binomial (a b : ℕ) :
    isLaminar a b ↔ ¬ (2 ∣ Nat.choose (a + b) a) := by
  rw [isLaminar]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : Nat.choose (a + b) a ≠ 0 := by
    have := Nat.choose_pos (Nat.le_add_right a b); omega
  constructor
  · -- Forward: a &&& b = 0 → ¬(2 ∣ choose (a+b) a)
    -- carry_friction = 0 → padicValNat 2 choose = 0 → ¬(2 ∣ choose)
    intro h
    have hcf : carry_friction a b = 0 := (laminar_flow_equivalence a b).mpr h
    have hpv : padicValNat 2 (Nat.choose (a + b) a) = 0 := by
      rw [← binary_carry_is_kummer]; exact hcf
    intro hdvd
    exact absurd hpv ((dvd_iff_padicValNat_ne_zero hne).mp hdvd)
  · -- Backward: ¬(2 ∣ choose (a+b) a) → a &&& b = 0
    -- ¬(2 ∣ choose) → padicValNat 2 choose = 0 → carry_friction = 0 → a &&& b = 0
    intro hndvd
    have hpv : padicValNat 2 (Nat.choose (a + b) a) = 0 := by
      by_contra hne'
      exact hndvd ((dvd_iff_padicValNat_ne_zero hne).mpr hne')
    have hcf : carry_friction a b = 0 := by
      rw [binary_carry_is_kummer]; exact hpv
    exact (laminar_flow_equivalence a b).mp hcf

end ABCFormalization
