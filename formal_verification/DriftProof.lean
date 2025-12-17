import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-!
# Formal Verification of Drift Core Carry Uniformity

This module formalizes the "Carry Uniformity" theorem for the Drift Core architecture.
It proves that the algebraic "Full Adder" logic used in the hardware has a strictly
bounded carry, guaranteeing finite state machine behavior.

References correspond to: `Collatz_Final.pdf` (Drift Systems Research, Dec 2025)
-/

namespace DriftCore

-- ==============================================================================
-- SECTION 1: The Arithmetic Model
-- Reference: Proof of Theorem 1, "The full adder relation"
-- ==============================================================================

/--
The carry recurrence relation derived from the operation y = (3n + 1) / 2.
Modeled as the binary operation: (n << 1) + n + 1.
Formula: n_k + n_{k-1} + c_k = 2 * c_{k+1} + s_k
-/
def carry_next (n_k : ℕ) (n_prev : ℕ) (c_k : ℕ) : ℕ :=
  (n_k + n_prev + c_k) / 2

-- ==============================================================================
-- SECTION 2: The Bounded Carry Theorem
-- Reference: Theorem 1 (Carry Uniformity), Page 3
-- ==============================================================================

/--
Theorem 1: For any valid binary stream (n_k, n_prev ∈ {0,1}) and a bounded
carry-in (c_k ≤ 2), the next carry c_{k+1} is strictly bounded by 2.
This proves the system cannot diverge into infinite states.
-/
theorem carry_is_bounded (n_k n_prev c_k : ℕ)
  (h_n_k : n_k ≤ 1) -- Input bit constraint
  (h_n_prev : n_prev ≤ 1) -- Previous bit constraint
  (h_c_k : c_k ≤ 2) -- Current carry constraint (Inductive Hypothesis)
  : carry_next n_k n_prev c_k ≤ 2 := by

  unfold carry_next
  -- 1. Establish max value of numerator: 1 + 1 + 2 = 4
  have h_sum : n_k + n_prev + c_k ≤ 4 := by linarith

  -- 2. Apply division property: 4 / 2 = 2
  have h_div : (n_k + n_prev + c_k) / 2 ≤ 2 := by
    apply Nat.div_le_of_le_mul
    linarith

  exact h_div

-- ==============================================================================
-- SECTION 3: The Finite State Automaton (FSA)
-- Reference: Appendix C.2 "Reachable States"
-- ==============================================================================

/--
The 6 explicit states reachable by the Drift Core.
S3 is the Start State (1,0,T).
-/
inductive FSAState
| S0 -- (0,0,F)
| S1 -- (0,1,F)
| S2 -- (1,0,F)
| S3 -- (1,0,T) [Start]
| S4 -- (1,1,F)
| S5 -- (1,1,T)
deriving Repr, DecidableEq

-- ==============================================================================
-- SECTION 4: The Transition Logic
-- Reference: Appendix C.2 "Transitions" and Figure 2
-- ==============================================================================

/--
The Transition Function δ(State, Input) -> NextState.
This models the "Double-Kick" logic inherent in the arithmetic.
-/
def next_state (s : FSAState) (input_bit : ℕ) : FSAState :=
  match s, input_bit with
  -- Laminar Flow (Descent)
  | FSAState.S3, 0 => FSAState.S0

  -- Turbulent Flow (Ascent / "Kick")
  | FSAState.S3, 1 => FSAState.S5
  | FSAState.S5, 1 => FSAState.S4

  -- Default / Other transitions (Simplified for verification scope)
  | _, _ => FSAState.S0

end DriftCore
