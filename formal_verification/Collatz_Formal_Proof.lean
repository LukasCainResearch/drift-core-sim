import Mathlib.Data.Rat.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Formal Evidence: Collatz via 2-Adic Automata (Lean 4 / Mathlib)

This module proves several small, self-contained lemmas that support an
automaton-style analysis:

1. Carry Uniformity: adding three bits produces a carry bit ≤ 1.
2. FSA Transitions: a small transition function has a verified loop.
3. Cycle Exclusion (example): a concrete Diophantine instance has no solution n > 1.
4. Basin Separation: 1 ≠ -5/3 and the affine map c ↦ 3c+1 is injective on ZMod (2^k).
-/

noncomputable section
namespace CollatzProof

-- ==============================================================================
-- 1. CARRY UNIFORMITY
-- ==============================================================================

/-- Carry-out for adding three bits in base 2. -/
def carryNext (n_k n_prev c_k : ℕ) : ℕ :=
  (n_k + n_prev + c_k) / 2

/-- If inputs are bits (≤ 1), the carry-out is ≤ 1. -/
theorem carry_is_bounded (n_k n_prev c_k : ℕ)
  (h_n : n_k ≤ 1) (h_p : n_prev ≤ 1) (h_c : c_k ≤ 1) :
  carryNext n_k n_prev c_k ≤ 1 := by
  unfold carryNext
  have hs : n_k + n_prev + c_k ≤ 3 := by
    nlinarith
  have h_div : (n_k + n_prev + c_k) / 2 ≤ 3 / 2 := Nat.div_le_div_right hs
  -- 3/2 = 1 in ℕ, so this closes.
  simpa using h_div

-- ==============================================================================
-- 2. 6-STATE FSA TRANSITIONS
-- ==============================================================================

inductive FSAState | S0 | S1 | S2 | S3 | S4 | S5
  deriving DecidableEq, Repr

/-- Transition function: (State, InputBit) ↦ (NextState, OutputBit?). -/
def fsa_step : FSAState → Bool → (FSAState × Option Bool)
  | FSAState.S3, true  => (FSAState.S5, none)
  | FSAState.S5, false => (FSAState.S3, none)
  | FSAState.S3, false => (FSAState.S0, some true)
  | FSAState.S5, true  => (FSAState.S4, some true)
  | _, _               => (FSAState.S0, some true)

/-- Verified S3 ↔ S5 loop. -/
theorem v_counting_loop_verified :
  (fsa_step FSAState.S3 true).1 = FSAState.S5 ∧
  (fsa_step FSAState.S5 false).1 = FSAState.S3 := by
  constructor <;> rfl

-- ==============================================================================
-- 3. CYCLE EXCLUSION (example instance)
-- ==============================================================================

/-- A computable “RHS” construction (kept list-based and total). -/
def cycle_rhs (v : List ℕ) : ℤ :=
  let k := v.length
  let sums := (v.scanl (· + ·) 0).take k
  let p3   := (List.range k).reverse.map (fun i => (3 : ℤ) ^ i)
  let p2   := sums.map (fun s => (2 : ℤ) ^ s)
  (List.zipWith (· * ·) p3 p2).sum

/-- For the example v = [1,3], the cycle equation LHS*n = RHS has no solution n > 1. -/
theorem case_v1_3_no_solution :
  let lhs : ℤ := 2^4 - 3^2
  let rhs : ℤ := cycle_rhs [1, 3]
  lhs = 7 ∧ rhs = 5 ∧ ∀ n : ℤ, n > 1 → lhs * n ≠ rhs := by
  intro lhs rhs
  have hL : lhs = 7 := by
    -- lhs is definitional alias above
    norm_num [lhs]
  have hR : rhs = 5 := by
    -- small concrete computation; fast and robust
    native_decide
  refine ⟨hL, hR, ?_⟩
  intro n hn
  -- Reduce to showing 7*n ≠ 5 for n > 1
  rw [hL, hR]
  have hn2 : n ≥ 2 := by linarith
  have hge : (7 : ℤ) * n ≥ 14 := by nlinarith
  -- 14 ≤ 7*n contradicts 7*n = 5
  intro hEq
  have : (7 : ℤ) * n = 5 := hEq
  nlinarith

-- ==============================================================================
-- 4. BASIN SEPARATION & MODULAR DRIFT
-- ==============================================================================

def bridge_target : ℚ := (-5 : ℚ) / 3

theorem basin_gap_verified : (1 : ℚ) ≠ bridge_target := by
  norm_num [bridge_target]

/-- The affine map c ↦ 3c + 1 is injective on ZMod (2^k). -/
theorem drift_is_injective (k : ℕ) :
  Function.Injective (fun (c : ZMod (2^k)) => 3 * c + 1) := by
  intro c1 c2 h
  -- Cancel the +1 on the right
  have h_mul : 3 * c1 = 3 * c2 := by
    exact add_right_cancel h
  -- 3 is a unit mod 2^k since gcd(3,2)=1 ⇒ gcd(3,2^k)=1
  have hu : IsUnit (3 : ZMod (2^k)) := by
    rw [ZMod.isUnit_iff_natCoprime]
    have h32 : Nat.Coprime 3 2 := by decide
    exact h32.pow_right k
  -- Cancel multiplication by a unit
  exact (IsUnit.mul_left_cancel hu).1 h_mul

end CollatzProof
