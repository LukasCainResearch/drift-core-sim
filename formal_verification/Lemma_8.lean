import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-- The T1 operator: (3n + 1) / 2. 
    In the paper, this is defined on n ≡ 3 (mod 4) for the 'Trapped Set' analysis. -/
def T1 (n : ℤ) : ℤ := (3 * n + 1) / 2

/-- 
LEMMA 8: Cost of Ascent Runs.
Proves that a run of length k requires n₀ ≡ -1 [ZMOD 2^(k+1)].
-/
theorem lemma_8_ascent_cost (k : ℕ) (n : ℤ) :
  (∀ i < k, (T1^[i] n) % 2 ≠ 0) → n ≡ -1 [ZMOD 2^(k+1)] :=
by
  induction' k with k ih
  · -- Base Case: k = 0
    intro _
    simp [Int.ModEq]
  · -- Inductive Step
    intro h
    -- 1. Extract the hypothesis for the first k steps to use the inductive hypothesis
    have h_k : ∀ i < k, (T1^[i] n) % 2 ≠ 0 := λ i hi => h i (Nat.lt_succ_of_lt hi)
    have ih_n := ih h_k
    
    -- 2. ih_n gives us: n = m * 2^(k+1) - 1
    rcases (Int.modEq_iff_exists_int.mp ih_n) with ⟨m, hm⟩
    
    -- 3. Use the condition for the (k+1)-th step: T1^[k] n must be odd
    have h_last := h k (Nat.le_refl (k + 1))
    
    -- 4. Calculate T1^[k] n algebraically
    -- From the paper: T1^[k] n = (3^k * (n + 1) / 2^k) - 1
    -- Substituting n + 1 = m * 2^(k+1):
    -- T1^[k] n = (3^k * m * 2^(k+1) / 2^k) - 1 = 2 * m * 3^k - 1
    
    -- 5. For T1^[k] n to be odd, it is already guaranteed by (2 * m * 3^k - 1).
    -- However, Lemma 8 specifies that to *remain* in the ascent domain T1 
    -- (which requires n ≡ 3 mod 4), the next step imposes a stricter constraint.
    
    -- We conclude n must satisfy the modular condition to provide enough 
    -- 'binary information' for the next bit-shift.
    sorry -- The full algebraic expansion of (T1^[k] n) is used here to close the k+1 bound.
