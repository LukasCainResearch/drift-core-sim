import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.NormNum

/-- 
  General Cycle Equation: (2^V - 3^k) * n₁ = RHS
  For a tuple of valuations (v₁, v₂, ..., vₖ).
-/
def cycle_rhs (v : List ℕ) : ℤ :=
  let k := v.length
  let sums := v.scanl (·+·) 0
  (List.range k).map (λ i => (3 : ℤ)^(k - 1 - i) * (2 : ℤ)^(sums.get! i)) |>.sum

/-- 
  Theorem: Case (v=1, 3). k=2, V=4.
  LHS = 2^4 - 3^2 = 7.
  RHS = 3^(2-1)*2^0 + 3^(2-2)*2^1 = 3*1 + 1*2 = 5.
  Equation: 7 * n₁ = 5 => n₁ = 5/7 (Not an integer).
-/
theorem case_v1_3_no_integer_solution :
  let v := [1, 3]
  let lhs : ℤ := 2^4 - 3^2
  let rhs := cycle_rhs v
  lhs = 7 ∧ rhs = 5 ∧ ¬ (∃ (n : ℤ), n > 1 ∧ lhs * n = rhs) := 
by
  native_decide -- Verifies the arithmetic and non-existence of integer n > 1

/-- 
  Theorem: Case (v=1, 1, 3). k=3, V=5.
  LHS = 2^5 - 3^3 = 32 - 27 = 5.
  RHS = 3^2*2^0 + 3^1*2^1 + 3^0*2^2 = 9*1 + 3*2 + 1*4 = 19.
  Equation: 5 * n₁ = 19 => n₁ = 19/5 (Not an integer).
-/
theorem case_v1_1_3_no_integer_solution :
  let v := [1, 1, 3]
  let lhs : ℤ := 2^5 - 3^3
  let rhs := cycle_rhs v
  lhs = 5 ∧ rhs = 19 ∧ ¬ (∃ (n : ℤ), n > 1 ∧ lhs * n = rhs) := 
by
  native_decide
