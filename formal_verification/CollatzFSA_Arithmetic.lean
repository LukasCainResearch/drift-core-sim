/-
  CollatzFSA.Arithmetic

  Arithmetic interpretation layer for the CollatzFSA automaton.

  This file depends on CollatzFSA.FSA (the reusable automaton definition)
  and adds:
    - bitlist <-> Nat interpretation helpers (LSB-first)
    - a “Collatz-odd-step” target function (3n+1, strip 2-adic valuation)
    - theorem statements connecting run/count/output bits to arithmetic

  Design goal:
    Keep CollatzFSA.FSA reusable and free of number theory.

  IMPORTANT (bit order):
  - CollatzFSA.FSA.runRev collects outBits in reverse-emission order (cons on recursion).
  - CollatzFSA.FSA.runLSB reverses once, returning outBits in emission order.
  - This arithmetic module uses runLSB so `bitsToNat outBits` is the intended value.
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

/-- Collatz odd-step: (3n+1)/2^{v2(3n+1)}. -/
def collatzOddStep (n : Nat) : Nat :=
  oddPart (threeNPlusOne n)

--------------------------------------------------------------------------------
-- Basic lemmas about bitsToNat (lightweight; reusable)
--------------------------------------------------------------------------------

@[simp] lemma bitsToNat_nil : bitsToNat ([] : List Bool) = 0 := rfl

@[simp] lemma bitsToNat_cons (b : Bool) (bs : List Bool) :
  bitsToNat (b :: bs) = (if b then 1 else 0) + 2 * bitsToNat bs := rfl

/-- LSB-first “shift” lemma. -/
lemma bitsToNat_cons_zero (bs : List Bool) :
  bitsToNat (false :: bs) = 2 * bitsToNat bs := by
  simp [bitsToNat]

lemma bitsToNat_cons_one (bs : List Bool) :
  bitsToNat (true :: bs) = 1 + 2 * bitsToNat bs := by
  simp [bitsToNat]

--------------------------------------------------------------------------------
-- A project-local LSB-first bit decomposition (stable across Mathlib versions)
--
-- We intentionally avoid Nat.bits here, because its lemma names vary.
-- You can add a separate "NatBitsBridge.lean" later if needed.
--------------------------------------------------------------------------------

/-- LSB-first bit decomposition via repeated div2. -/
def bitsLSB : Nat → List Bool
| 0 => []
| n => (n % 2 = 1) :: bitsLSB (n / 2)

/--
TODO (one-time foundational lemma):

bitsToNat agrees with bitsLSB:

  bitsToNat (bitsLSB n) = n

Once proven, you can use bitsLSB as the canonical input stream to the automaton.
-/
theorem bitsToNat_bitsLSB (n : Nat) :
  bitsToNat (bitsLSB n) = n := by
  -- Suggested proof:
  --   strong induction on n
  --   use Nat.div_add_mod (or Nat.mod_add_div) specialized to 2
  --   split on n%2 = 0 or 1
  sorry

--------------------------------------------------------------------------------
-- Automaton output interpretation
--------------------------------------------------------------------------------

/--
Interpret the automaton output bits as a Nat.

We run the automaton using `runLSB`, which returns outBits in emission order,
so this is a direct LSB-first interpretation.
-/
def outValue (r : RunResult) : Nat := bitsToNat r.outBits

/--
Core arithmetic contract (preferred API):

Running the automaton from S3 on bitsLSB n produces:
  threeNPlusOne n = 2^count * outValue

This is the “factorization” view:
  3n+1 = 2^v * m
where v is the number of none-outputs and m is the emitted bitstream value.
-/
theorem fsa_factorization_bitsLSB (n : Nat) :
  let r := runLSB FSAState.S3 (bitsLSB n)
  threeNPlusOne n = (2 ^ r.count) * outValue r := by
  -- This is the core arithmetic proof.
  --
  -- Recommended proof strategy:
  --   1) Prove a stronger invariant by induction on the input bitstream:
  --      after processing a prefix, the automaton state + accumulated output
  --      corresponds to a partial computation of 3n+1 with a bounded carry term.
  --   2) Discharge the one-step invariant by finite case split on (state, bit)
  --      using simp [CollatzFSA.step].
  --   3) Conclude by induction.
  sorry

/--
Corollary: the automaton computes the odd part of (3n+1).

Canonical result:
  outValue = (3n+1) / 2^{v2(3n+1)}
and count = v2(3n+1).
-/
theorem fsa_computes_oddPart_bitsLSB (n : Nat) :
  let r := runLSB FSAState.S3 (bitsLSB n)
  r.count = v2 (threeNPlusOne n) ∧
  outValue r = oddPart (threeNPlusOne n) := by
  -- From fsa_factorization_bitsLSB, show:
  --   (i) 2^r.count divides 3n+1, with quotient outValue
  --   (ii) r.count is maximal, i.e. equals trailingZeros(3n+1).
  --
  -- The maximality step uses:
  --   - how `none` outputs correspond to consuming factors of 2
  --   - the structural “counting” region behavior (S3/S5 loop)
  --   - and the fact that after leaving counting, the next output is a bit.
  sorry

/-- Final packaging theorem (nice API): the automaton computes Collatz odd-step. -/
theorem fsa_collatzOddStep_bitsLSB (n : Nat) :
  let r := runLSB FSAState.S3 (bitsLSB n)
  outValue r = collatzOddStep n := by
  intro r
  have h := fsa_computes_oddPart_bitsLSB n
  simpa [collatzOddStep, oddPart, threeNPlusOne, outValue] using (h.2)

--------------------------------------------------------------------------------
-- Optional: bridge back to Nat.bits (if/when you want it)
--------------------------------------------------------------------------------

/--
Optional bridge (version-pinned):

If you later want theorems stated using `Nat.bits n` directly, add a separate
file that proves `bitsLSB n = Nat.bits n` (or that they have equal bitsToNat),
and then transport the results. This keeps the core arithmetic file stable.
-/

end CollatzFSA
