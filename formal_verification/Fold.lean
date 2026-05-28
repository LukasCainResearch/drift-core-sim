/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Fold-Step Correctness

The Drift Core's output stage folds a `2W`-bit arithmetic state into a
`W`-bit value by XOR-ing the high half with the low half. In the
production silicon (`dad_core.v`), with `W = 64`:

    folded_bits = next_state_arithmetic[63:0]
                ^ next_state_arithmetic[127:64];

This file formalizes the fold for arbitrary `W` and proves:

* `fold_width_invariant` — a `2W`-bit input yields a `W`-bit output
  (the output stage is *structurally bounded*; no overflow into a
  `W+1`-bit wire is possible).
* `fold_eq_truncate_xor` — equivalence with the XOR-then-truncate form
  used by downstream synthesis tooling. Confirms the RTL line is
  algebraically the same as a single XOR over the full word followed
  by truncation to the output wire width.

The fold is the load-bearing operation that bounds the output stage of
the production recurrence `Fold(qS + d) >> k`; together with
`CarryUniformity`, `CarryTransducer`, and `CarryGraph` it certifies
the recurrence is well-formed at every step.

Uses only stock Mathlib + Lean 4 core; no axioms, no `sorry`.
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace DriftCore

/--
**The fold.** XOR the high `W` bits of `x` with its low `W` bits.

* Low half: `x &&& (2^W - 1)` — mask off the bottom `W` bits.
* High half: `x >>> W` — arithmetic right-shift discards the bottom `W`.

For a `2W`-bit input, the result is `W` bits (`fold_width_invariant`).
-/
def fold (W x : ℕ) : ℕ :=
  (x &&& (2 ^ W - 1)) ^^^ (x >>> W)

private lemma two_pow_sub_one_lt (W : ℕ) : 2 ^ W - 1 < 2 ^ W :=
  Nat.sub_lt (Nat.two_pow_pos W) Nat.one_pos

/-- A `2W`-bit value, right-shifted by `W`, fits in `W` bits. -/
lemma shiftRight_lt_two_pow {W x : ℕ} (hx : x < 2 ^ (2 * W)) :
    x >>> W < 2 ^ W := by
  rw [Nat.shiftRight_eq_div_pow]
  have hpow : (2 : ℕ) ^ (2 * W) = 2 ^ W * 2 ^ W := by
    rw [two_mul, pow_add]
  rw [hpow] at hx
  exact Nat.div_lt_of_lt_mul hx

/-- The low-`W`-bit mask of any value fits in `W` bits. -/
lemma and_mask_lt_two_pow (W x : ℕ) : x &&& (2 ^ W - 1) < 2 ^ W :=
  Nat.and_lt_two_pow x (two_pow_sub_one_lt W)

/--
**Width invariant.** A `2W`-bit input folds to a `W`-bit output.

This is the structural correctness statement: the fold cannot
overflow the output register, regardless of input.
-/
theorem fold_width_invariant {W x : ℕ} (hx : x < 2 ^ (2 * W)) :
    fold W x < 2 ^ W := by
  unfold fold
  exact Nat.xor_lt_two_pow (and_mask_lt_two_pow W x)
    (shiftRight_lt_two_pow hx)

/--
**Strongly-typed fold.** A `2W`-bit `Fin` value folds to a `W`-bit
`Fin` value. The bound is discharged once by `fold_width_invariant`;
downstream consumers get the bound by type.
-/
def Fold (W : ℕ) (x : Fin (2 ^ (2 * W))) : Fin (2 ^ W) :=
  ⟨fold W x.val, fold_width_invariant x.isLt⟩

/--
**RTL equivalence.** For a `2W`-bit input, the fold equals XOR-ing
the value with its right-shift, then truncating to the low `W` bits.

This is the form a synthesis tool typically produces when it expresses
the fold as a single XOR over the full word followed by an implicit
truncation to the output wire width. The two forms are algebraically
equal, so the silicon's behavior matches the spec regardless of which
form the synthesis tool emits.
-/
theorem fold_eq_truncate_xor {W x : ℕ} (hx : x < 2 ^ (2 * W)) :
    fold W x = (x ^^^ (x >>> W)) &&& (2 ^ W - 1) := by
  unfold fold
  rw [Nat.and_xor_distrib_right,
      Nat.and_two_pow_sub_one_of_lt_two_pow (shiftRight_lt_two_pow hx)]

/-! ## Production instantiation (W = 64) -/

/-- The production fold: `W = 64`, matching `dad_core.v`. The type
`Fin (2 ^ (2 * 64))` reduces to `Fin (2 ^ 128)` definitionally. -/
abbrev FoldProd : Fin (2 ^ (2 * 64)) → Fin (2 ^ 64) := Fold 64

end DriftCore
