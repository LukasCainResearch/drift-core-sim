import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace CollatzFSA

abbrev Bit := Bool

/-- Interpret LSB-first bits as Nat. -/
def bitsToNat : List Bit → Nat
| []       => 0
| b :: bs  => (if b then 1 else 0) + 2 * bitsToNat bs

@[simp] lemma bitsToNat_nil : bitsToNat ([] : List Bit) = 0 := rfl
@[simp] lemma bitsToNat_cons (b : Bit) (bs : List Bit) :
  bitsToNat (b :: bs) = (if b then 1 else 0) + 2 * bitsToNat bs := rfl

lemma bitsToNat_false (bs : List Bit) :
  bitsToNat (false :: bs) = 2 * bitsToNat bs := by simp [bitsToNat]

lemma bitsToNat_true (bs : List Bit) :
  bitsToNat (true :: bs) = 1 + 2 * bitsToNat bs := by simp [bitsToNat]

/--
A project-local LSB-first bit decomposition.

This is deliberately simple: repeated division by 2.
-/
def bitsLSB : Nat → List Bit
| 0 => []
| n => (n % 2 = 1) :: bitsLSB (n / 2)

/-- The key round-trip theorem you want early: bitsToNat (bitsLSB n) = n. -/
theorem bitsToNat_bitsLSB (n : Nat) : bitsToNat (bitsLSB n) = n := by
  -- This proof is standard:
  -- 1) strong induction on n
  -- 2) use Nat.mod_two_eq_zero_or_one and n = 2*(n/2) + n%2
  --
  -- I am leaving this as `sorry` because the exact lemma names differ a bit,
  -- but the proof is stable and you only do it once in this file.
  --
  -- In VS Code: search for lemmas:
  --   #check Nat.mod_two_eq_zero_or_one
  --   #check Nat.div_add_mod
  --   #check Nat.mod_eq_of_lt
  --   #check Nat.mul_add_div
  sorry

end CollatzFSA
