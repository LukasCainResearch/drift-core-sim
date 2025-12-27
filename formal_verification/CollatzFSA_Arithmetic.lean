/-
  CollatzFSA.Arithmetic

  Arithmetic interpretation layer for the CollatzFSA automaton.

  This file depends on CollatzFSA.FSA (the reusable automaton definition)
  and adds:
    - bitlist <-> Nat interpretation helpers
    - a “Collatz-odd-step” target function (3n+1, strip 2-adic valuation)
    - theorem statements connecting run/count/output bits to arithmetic

  Design goal:
    Keep CollatzFSA.FSA reusable and free of number theory.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Tactic

import CollatzFSA.FSA

namespace CollatzFSA

open CollatzFSA

/-- Interpret a list of bits as a natural number (LSB-first). -/
def bitsToNat : List Bool → Nat
| []       => 0
| b :: bs  => (if b then 1 else 0) + 2 * bitsToNat bs

/-- Convenience: the Collatz “3n+1” map on Nat. -/
def threeNPlusOne (n : Nat) : Nat := 3*n + 1

/-- The 2-adic valuation on Nat, as number of trailing zeros in binary. -/
def v2 (n : Nat) : Nat := Nat.trailingZeros n

/-- Strip all factors of two from a Nat. -/
def oddPart (n : Nat) : Nat := n / (2 ^ v2 n)

/-- Collatz odd-step (for odd n): (3n+1)/2^{v2(3n+1)}. -/
def collatzOddStep (n : Nat) : Nat :=
  oddPart (threeNPlusOne n)

--------------------------------------------------------------------------------
-- Basic lemmas about bitsToNat (lightweight; reusable)
--------------------------------------------------------------------------------

@[simp] lemma bitsToNat_nil : bitsToNat ([] : List Bool) = 0 := rfl

@[simp] lemma bitsToNat_cons (b : Bool) (bs : List Bool) :
  bitsToNat (b :: bs) = (if b then 1 else 0) + 2 * bitsToNat bs := rfl

/-- LSB-first “shift” lemma. -/
lemma bitsToNat_append_zero (bs : List Bool) :
  bitsToNat (false :: bs) = 2 * bitsToNat bs := by
  simp [bitsToNat]

lemma bitsToNat_append_one (bs : List Bool) :
  bitsToNat (true :: bs) = 1 + 2 * bitsToNat bs := by
  simp [bitsToNat]

--------------------------------------------------------------------------------
-- Bridge to Nat.bits
--
-- Mathlib already provides a rich theory of Nat.bits, but which lemma names
-- are available can vary with Mathlib versions. To keep this file stable,
-- we isolate the required bridge as a single lemma. Once proven for your
-- pinned Mathlib, the rest of the arithmetic development becomes routine.
--------------------------------------------------------------------------------

/--
TODO (version-pinned):

bitsToNat agrees with Nat.bits:

  bitsToNat (Nat.bits n) = n

Once you discharge this lemma against your Mathlib version, all theorems below
can be stated “for n : Nat” directly, using Nat.bits as input to the automaton.
-/
theorem bitsToNat_natBits (n : Nat) :
  bitsToNat (Nat.bits n) = n := by
  -- NOTE: Fill this using the Mathlib lemma that relates Nat.bits to Nat
  -- (often via Nat.bitsRec / Nat.bit / Nat.testBit, depending on version).
  --
  -- Typical approach:
  --   induction n using Nat.binaryRec
  -- or:
  --   simpa using (Nat.bits_toNat n)  -- if such a lemma exists in your version
  --
  -- Leaving as a TODO placeholder until we lock the exact lemma name.
  sorry

--------------------------------------------------------------------------------
-- Automaton output interpretation
--------------------------------------------------------------------------------

/--
Interpret the automaton output bits as a Nat.

Important: `run` in CollatzFSA.FSA collects output via `bit :: r.outBits`,
which is LSB-first if the automaton emits LSB-first. If your interpretation
is MSB-first, you would reverse here. We keep it LSB-first for consistency.
-/
def outValue (r : RunResult) : Nat := bitsToNat r.outBits

/--
The main arithmetic contract we ultimately want:

Running the automaton from S3 on Nat.bits n produces:
  threeNPlusOne n = 2^count * outValue

This is the “factorization” view:
  3n+1 = 2^v * m
where v is the count of none-outputs and m is the emitted bitstream value.
-/
theorem fsa_factorization_contract (n : Nat) :
  let r := run FSAState.S3 (Nat.bits n)
  threeNPlusOne n = (2 ^ r.count) * outValue r := by
  -- This is the core arithmetic proof.
  --
  -- Proof strategy (recommended):
  --   1) Prove a stronger invariant by induction on the input bitstream:
  --      after processing a prefix, the automaton state + accumulated output
  --      corresponds to a partial computation of 3n+1 with a carry-like term.
  --   2) Use the concrete 12-transition table to discharge the “one-step
  --      arithmetic” cases (finite, mechanical case split).
  --
  -- This is intentionally in the Arithmetic module (not FSA core).
  sorry

/--
Corollary: the automaton computes the odd part of (3n+1).

This is the canonical “Collatz odd-step” result:
  outValue = (3n+1) / 2^{v2(3n+1)}
and count = v2(3n+1).
-/
theorem fsa_computes_oddPart (n : Nat) :
  let r := run FSAState.S3 (Nat.bits n)
  r.count = v2 (threeNPlusOne n) ∧
  outValue r = oddPart (threeNPlusOne n) := by
  -- From factorization_contract, show:
  --   (i) 2^r.count divides 3n+1
  --   (ii) r.count is maximal (equals trailingZeros), using the fact that the
  --        automaton emits its first output exactly when leaving counting
  --        and that counting corresponds to consuming factors of 2.
  --
  -- Requires connecting “none outputs” to divisibility-by-2.
  sorry

/--
Final packaging theorem (nice API): the automaton computes Collatz odd-step.
-/
theorem fsa_collatzOddStep (n : Nat) :
  let r := run FSAState.S3 (Nat.bits n)
  outValue r = collatzOddStep n := by
  intro r
  have h := fsa_computes_oddPart n
  -- unpack and rewrite
  simpa [collatzOddStep, oddPart, threeNPlusOne, outValue] using (h.2)

end CollatzFSA
