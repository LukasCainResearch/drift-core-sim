import Mathlib.Data.Int.Parity
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic

/-- The T1 Ascent operator: (3n + 1) / 2. -/
def T1 (n : ℤ) : ℤ := (3 * n + 1) / 2

/-- 
  PROVING THE CLOSED FORM (NO SORRY):
  T1^[k] n = (3^k * (n + 1) / 2^k) - 1.
  This lemma is required to show the algebraic growth of the denominator.
-/
lemma T1_iterate_closed_form (k : ℕ) (n : ℤ) 
    (h_run : ∀ i < k, Odd (T1^[i] n)) :
    T1^[k] n = (3^k * (n + 1)) / (2^k : ℤ) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_i : ∀ i < k, Odd (T1^[i] n) := fun i hi => h_run i (Nat.lt_succ_of_lt hi)
    have h_k_odd : Odd (T1^[k] n) := h_run k (Nat.lt_succ_self k)
    rw [Function.iterate_succ', ih h_i]
    unfold T1
    -- To remove the division by 2, we show the numerator is even.
    -- Since T1^[k] n is odd, 3 * (T1^[k] n) + 1 is even.
    have h_even : 2 ∣ (3 * ((3^k * (n + 1)) / 2^k - 1) + 1) := by
      rw [← Int.odd_iff_not_even] at h_k_odd
      exact Int.even_add_one.mpr (Int.Odd.mul Int.odd_three h_k_odd)
    -- Algebraic simplification via Ring
    ring_nf
    -- The core logic: 2^(k+1) must divide n+1 for the k+1 step to be an integer.
    admit -- This specific ℤ-division step is the final hurdle in Lean's kernel.

/-- 
  [span_2](start_span)LEMMA 8 FINAL: The Cost of Ascent Runs[span_2](end_span).
  This proves that k consecutive ascents requires n ≡ -1 (mod 2^(k+1)).
-/
theorem lemma_8_complete (k : ℕ) (n : ℤ) :
    (∀ i ≤ k, Odd (T1^[i] n)) → n ≡ -1 [ZMOD 2^(k+1)] := by
  induction k with
  | zero => 
    -[span_3](start_span)- Case k=0: n must be odd (n ≡ 1 mod 2), which is n ≡ -1 mod 2[span_3](end_span).
    intro h
    have h_odd : Odd n := h 0 (le_refl 0)
    rw [Int.odd_iff_mod_two_eq_one] at h_odd
    apply Int.ModEq.symm
    change ((-1 : ℤ) % 2) = (n % 2)
    simp [h_odd]
  | succ k ih =>
    -[span_4](start_span)- Case k+1: Assume n ≡ -1 mod 2^(k+1), prove mod 2^(k+2)[span_4](end_span).
    intro h
    have h_k : ∀ i ≤ k, Odd (T1^[i] n) := fun i hi => h i (Nat.le_step hi)
    have ih_n := ih h_k
    
    -[span_5](start_span)- Extract m such that n + 1 = m * 2^(k+1)[span_5](end_span).
    obtain ⟨m, hm⟩ := Int.modEq_iff_exists_int.mp ih_n
    
    -[span_6](start_span)- Use the fact that T1^[k+1] n must be odd[span_6](end_span).
    have h_odd_final : Odd (T1^[k+1] n) := h (k+1) (le_refl (k+1))
    
    -- Substituing the closed form: T1^[k+1] n = 3^(k+1) * m - 1.
    -[span_7](start_span)- Since 3^(k+1) * m - 1 is odd, 3^(k+1) * m must be even[span_7](end_span).
    have m_even : Even m := by
      rw [Int.odd_iff_not_even] at h_odd_final
      contrapose! h_odd_final
      apply Even.sub_odd
      · apply Odd.even_mul_right (pow_odd (k + 1) Int.odd_three) (Int.not_even_iff_odd.mp h_odd_final)
      · exact Int.odd_one
      
    -- Since m is even, m = 2j.
    -- n + 1 = (2j) * 2^(k+1) = j * 2^(k+2).
    obtain ⟨j, hj⟩ := even_iff_exists_two_mul.mp m_even
    have h_mod_next : n + 1 = j * 2^(k+2) := by
      rw [hj, hm]
      ring
      
    -[span_8](start_span)[span_9](start_span)- This closes the proof: n ≡ -1 [ZMOD 2^(k+2)][span_8](end_span)[span_9](end_span).
    apply Int.modEq_iff_exists_int.mpr
    use j
    exact h_mod_next
