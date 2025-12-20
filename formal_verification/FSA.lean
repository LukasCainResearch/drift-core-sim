-[span_4](start_span)- Define the state space as an inductive type[span_4](end_span)
inductive FSAState
  | [span_5](start_span)S0 -- (0,0,False)[span_5](end_span)
  | [span_6](start_span)S1 -- (0,1,False)[span_6](end_span)
  | [span_7](start_span)S2 -- (1,0,False)[span_7](end_span)
  | [span_8](start_span)[span_9](start_span)S3 -- (1,0,True)  - Start State[span_8](end_span)[span_9](end_span)
  | [span_10](start_span)S4 -- (1,1,False)[span_10](end_span)
  | [span_11](start_span)S5 -- (1,1,True)[span_11](end_span)
  deriving DecidableEq, Repr

-[span_12](start_span)[span_13](start_span)- Define the Transition Function based on Appendix C.2[span_12](end_span)[span_13](end_span)
-- Returns (NextState, OutputBit). None represents no output yet (v-finding).
def fsa_transition : FSAState → Bool → (FSAState × Option Bool)
  | [span_14](start_span)FSAState.S0, false => (FSAState.S0, some false) --[span_14](end_span)
  | [span_15](start_span)FSAState.S0, true  => (FSAState.S1, some true)  --[span_15](end_span)
  | [span_16](start_span)FSAState.S1, false => (FSAState.S0, some true)  --[span_16](end_span)
  | [span_17](start_span)FSAState.S1, true  => (FSAState.S4, some false) --[span_17](end_span)
  | [span_18](start_span)FSAState.S2, false => (FSAState.S0, some true)  --[span_18](end_span)
  | [span_19](start_span)FSAState.S2, true  => (FSAState.S4, some false) --[span_19](end_span)
  | [span_20](start_span)FSAState.S3, false => (FSAState.S0, some true)  --[span_20](end_span)
  | [span_21](start_span)FSAState.S3, true  => (FSAState.S5, none)       --[span_21](end_span)
  | [span_22](start_span)FSAState.S4, false => (FSAState.S2, some false) --[span_22](end_span)
  | [span_23](start_span)FSAState.S4, true  => (FSAState.S4, some true)  --[span_23](end_span)
  | [span_24](start_span)FSAState.S5, false => (FSAState.S3, none)       --[span_24](end_span)
  | [span_25](start_span)FSAState.S5, true  => (FSAState.S4, some true)  --[span_25](end_span)

--- PROOFS OF CORRECTNESS (Sample Transitions from Appendix E) ---

[span_26](start_span)/-- Proof of Transition E.5.2: S3 + 1 -> S5 (v increments)[span_26](end_span) --/
theorem transition_S3_1 : fsa_transition FSAState.S3 true = (FSAState.S5, none) := 
by rfl

[span_27](start_span)/-- Proof of Transition E.1.2: S0 + 1 -> S1 (Output 1)[span_27](end_span) --/
theorem transition_S0_1 : fsa_transition FSAState.S0 true = (FSAState.S1, some true) := 
by rfl

[span_28](start_span)/-- Proof of the S3 <-> S5 Cycle (The 'Engine' of Strong Descent)[span_28](end_span) --/
theorem strong_descent_loop : 
  (fsa_transition FSAState.S3 true).1 = FSAState.S5 ∧ 
  (fsa_transition FSAState.S5 false).1 = FSAState.S3 := 
by 
  constructor
  [span_29](start_span)· rfl -- S3 --(1)--> S5[span_29](end_span)
  [span_30](start_span)· rfl -- S5 --(0)--> S3[span_30](end_span)
