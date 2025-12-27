/-
  CollatzFSA.FSA

  A standalone, reusable Lean module that defines the 6-state automaton
  used to stream bits and produce output bits, with a “counting” phase.

  This file intentionally contains:
    - Definitions (transition table, runners)
    - Structural lemmas about the automaton graph

  It intentionally does NOT contain the arithmetic bridge to (3n+1),
  so it remains lightweight and reusable in other projects.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace CollatzFSA

/-- States of the 6-state automaton. -/
inductive FSAState
| S0 | S1 | S2 | S3 | S4 | S5
deriving DecidableEq, Repr

/-- A bit (LSB-first streams are typical). -/
abbrev Bit := Bool

/-- Output bit: `none` represents the “-” (no output; still counting). -/
abbrev OutBit := Option Bool

/--
Full 12-transition table.

Conventions:
- input bit: false=0, true=1
- output: `none` means “no output emitted”
- output: `some b` means “emit bit b”
-/
def step : FSAState → Bit → (FSAState × OutBit)
| FSAState.S0, false => (FSAState.S0, some false)
| FSAState.S0, true  => (FSAState.S1, some true)

| FSAState.S1, false => (FSAState.S0, some true)
| FSAState.S1, true  => (FSAState.S4, some false)

| FSAState.S2, false => (FSAState.S0, some true)
| FSAState.S2, true  => (FSAState.S4, some false)

| FSAState.S3, false => (FSAState.S0, some true)
| FSAState.S3, true  => (FSAState.S5, none)

| FSAState.S4, false => (FSAState.S2, some false)
| FSAState.S4, true  => (FSAState.S4, some true)

| FSAState.S5, false => (FSAState.S3, none)
| FSAState.S5, true  => (FSAState.S4, some true)

/-- “Counting” states: those that can emit `none` (no output) in this design. -/
def counting : FSAState → Prop
| FSAState.S3 => True
| FSAState.S5 => True
| _           => False

/-- Convenience: complement of counting. -/
def emitting (s : FSAState) : Prop := ¬ counting s

/-- Run only the state evolution over a finite bitstring. -/
def runState : FSAState → List Bit → FSAState
| s, []      => s
| s, b :: bs => runState (step s b).1 bs

/--
Run the automaton over a finite bitstring, returning:
- `outBits`: output bits (collected in the natural “cons” order of emission;
            i.e. reverse-emission order due to recursion)
- `count`: how many `none` outputs occurred
-/
structure RunResult where
  outBits : List Bit
  count   : Nat
deriving Repr

/--
Core runner (efficient):

`outBits` are accumulated by consing onto the recursive result,
so they are in reverse-emission order (often MSB-first if the automaton
emits LSB-first). If you want bits in emission order, use `runLSB`.
-/
def run : FSAState → List Bit → RunResult
| s, [] =>
    { outBits := [], count := 0 }
| s, b :: bs =>
    let (s', o) := step s b
    let r := run s' bs
    match o with
    | none     => { outBits := r.outBits,        count := r.count + 1 }
    | some bit => { outBits := bit :: r.outBits, count := r.count }

/-- Alias emphasizing that `run` collects bits in reverse-emission order. -/
abbrev runRev := run

/--
Return output bits in emission order.

For LSB-first input streams (common for `bitsLSB`-style decompositions),
this produces an output list that is LSB-first in the same sense as
“push bits as they’re produced”, matching many reference implementations.

Downstream arithmetic code should prefer `runLSB` to avoid carrying `reverse`
everywhere.
-/
def runLSB (s : FSAState) (bs : List Bit) : RunResult :=
  let r := runRev s bs
  { r with outBits := r.outBits.reverse }

@[simp] lemma runLSB_count (s : FSAState) (bs : List Bit) :
  (runLSB s bs).count = (runRev s bs).count := by
  simp [runLSB, runRev]

@[simp] lemma runLSB_outBits (s : FSAState) (bs : List Bit) :
  (runLSB s bs).outBits = (runRev s bs).outBits.reverse := by
  simp [runLSB, runRev]

/-!
  ----------------------------------------------------------------------
  Structural lemmas (graph properties)
  ----------------------------------------------------------------------
  These are safe to include in a reusable module because they do not
  depend on any arithmetic interpretation of the automaton.
-/

/-- Characterize counting states. -/
lemma counting_iff (s : FSAState) :
  counting s ↔ s = FSAState.S3 ∨ s = FSAState.S5 := by
  cases s <;> simp [counting]

/-- Sanity checks: the v-counting loop edges. -/
lemma step_S3_1 : step FSAState.S3 true = (FSAState.S5, none) := rfl
lemma step_S5_0 : step FSAState.S5 false = (FSAState.S3, none) := rfl

/--
Two zeros force exit from counting:
- from S3: one zero already exits
- from S5: zero takes you to S3, then another zero exits
-/
theorem exit_counting_after_two_zeros :
  ∀ s, counting s → emitting (runState s [false, false]) := by
  intro s hs
  have : s = FSAState.S3 ∨ s = FSAState.S5 := (counting_iff s).1 hs
  cases this with
  | inl h =>
      subst h
      -- S3 --0--> S0; then S0 --0--> S0, and S0 is not counting.
      simp [runState, step, emitting, counting]
  | inr h =>
      subst h
      -- S5 --0--> S3 --0--> S0
      simp [runState, step, emitting, counting]

/--
Padding with two zeros ensures you end in an emitting state.

This captures the “finite bits + zero padding” property common in
LSB-first finite binary representations.
-/
theorem emitting_after_append_two_zeros (s : FSAState) (bs : List Bit) :
  emitting (runState s (bs ++ [false, false])) := by
  -- Let s' be the state after bs; if s' is counting, exit lemma applies;
  -- otherwise, brute-force case split on s' for the final two steps.
  let s' := runState s bs
  by_cases hcount : counting s'
  ·
    have hexit := exit_counting_after_two_zeros s' hcount
    -- rewrite runState s (bs ++ [0,0]) = runState s' [0,0]
    simpa [s', runState, List.append_assoc] using hexit
  ·
    -- s' is not counting. Split on s' and compute the final two steps.
    cases s' <;> simp [s', runState, step, emitting, counting] at *

end CollatzFSA
