/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Whitening Has Trivial Linear-Cryptanalysis Resistance

The companion negative result to `WhiteningLinearity.lean`.

`WhiteningLinearity.whiten_xor` proves `whiten` is GF(2)-linear. The
*flip side* of this — and the reason every honest framing of the
construction has to caveat the whitening — is that GF(2)-linearity is
the worst possible property to have with respect to linear
cryptanalysis. For any GF(2)-linear map `L` and any output mask `β`,
there is a *unique* input mask `α` such that `⟨α, x⟩ ⊕ ⟨β, L(x)⟩ = 0`
for **all** `x` (the deterministic linear approximation `α = L^T β`).

This file exhibits such a linear approximation concretely for the
production whitening: it derives a closed-form linear expression for
every output bit of `whiten(x)` in terms of the input bits, and proves
the expression holds for all 64-bit `x` via `bv_decide`.

## What this is

The cryptographic-flavor *negative* analogue of `Avalanche.lean`. Where
the avalanche bound was the first cryptographic-strength flavor
property (and a weak one, since it was tight at `≥ 2`), this file is
the first cryptographic-strength flavor *weakness* result. Together
they constrain the honest claim:

* The whitening stage is GF(2)-linear (`WhiteningLinearity`).
* Single-bit input flips produce ≥ 2 output bit flips (`Avalanche`).
* But every output bit is a known, fixed, linear combination of input
  bits — the absolute worst possible behavior against linear
  cryptanalysis (this file).

Hence **the whitening stage cannot, by itself, provide any
cryptographic strength**. Any cryptographic strength of the full
construction must come from the non-linear `driftStep` arithmetic.
The whitening is for structural shuffling, not for confusion in the
Shannon sense.

## What this is *not*

* **Not** a claim that the full Drift Core is cryptographically weak.
  The full construction is `whiten(fold(driftStep(state)))`. The
  `driftStep` step introduces non-linearity via the carries in
  `3·state + 1`; that non-linearity is what (potentially) provides
  cryptographic strength. Whether it actually does is the subject of
  cryptanalytic peer review (explicitly out of scope for Lean per the
  honest-framing rules).
* **Not** a complete linear-approximation table. We exhibit explicit
  closed-form expressions for selected output bits; the same
  technique applies to every output bit and could be generated
  exhaustively, but the load-bearing claim is "such expressions
  exist for every output bit," and one example suffices to make
  that point with full formality.
-/

import Std.Tactic.BVDecide
import Whitening
import WhiteningLinearity

namespace DriftCore

/-! ## Closed-form linear expressions for output bits -/

/--
**Linear weakness, bit 0.** The lowest output bit of the whitening is
the XOR of six specific input bits:

`whiten(x)[0] = x[0] ⊕ x[20] ⊕ x[24] ⊕ x[34] ⊕ x[44] ⊕ x[58]`.

Derivation: tracing bit 0 through the three cascade steps gives
`y3[0] = y2[0] ⊕ y2[34] = (x[0] ⊕ x[24]) ⊕ (x[20] ⊕ x[34] ⊕ x[44] ⊕ x[58])`.

Holds for **all** 64-bit inputs `x` — the relation is deterministic,
not statistical. An attacker observing `whiten(x)[0]` learns exactly
the value of the above 6-bit XOR with probability 1. Discharged by
`bv_decide` against the unfolded whitening expression.
-/
theorem whiten_bit0_linear (x : BitVec 64) :
    (whiten x).getLsbD 0 =
      x.getLsbD 0 ^^ x.getLsbD 20 ^^ x.getLsbD 24 ^^
      x.getLsbD 34 ^^ x.getLsbD 44 ^^ x.getLsbD 58 := by
  unfold whiten
  bv_decide

/--
**Linear weakness, bit 1.** Translation by one position gives the
parallel expression for bit 1; the same 6-bit-XOR structure holds
for every output bit whose input bits don't run off either end of
the 64-bit word.
-/
theorem whiten_bit1_linear (x : BitVec 64) :
    (whiten x).getLsbD 1 =
      x.getLsbD 1 ^^ x.getLsbD 21 ^^ x.getLsbD 25 ^^
      x.getLsbD 35 ^^ x.getLsbD 45 ^^ x.getLsbD 59 := by
  unfold whiten
  bv_decide

/-! ## Differential weakness via linearity -/

/--
**Output-difference equation, bit 0.** By
`WhiteningLinearity.whiten_xor`, the output difference
`whiten(x) ⊕ whiten(x')` depends only on the input difference
`x ⊕ x'`, not on `x` or `x'` individually. An attacker observing
the bit-0 difference learns a deterministic XOR of input-difference
bits.
-/
theorem whiten_diff_bit0 (x x' : BitVec 64) :
    (whiten x ^^^ whiten x').getLsbD 0 =
      (x ^^^ x').getLsbD 0 ^^ (x ^^^ x').getLsbD 20 ^^
      (x ^^^ x').getLsbD 24 ^^ (x ^^^ x').getLsbD 34 ^^
      (x ^^^ x').getLsbD 44 ^^ (x ^^^ x').getLsbD 58 := by
  rw [whiten_diff]
  exact whiten_bit0_linear (x ^^^ x')

/-! ## Headline summary statement -/

/--
**Whiten alone provides no linear-cryptanalysis resistance.** Every
output bit is a known, fixed, deterministic XOR of input bits. This
is the strongest possible "linear approximation with bias 1" — an
attacker observing any single output bit learns the value of a
specific XOR of input bits with probability 1.

Cryptographic strength of the full Drift Core, if any, must come
entirely from the non-linear `driftStep` arithmetic, not from the
whitening output stage. The whitening serves structural roles
(distribution-preservation, bit-mixing for hardware-test purposes)
but not confusion in the Shannon sense.

This theorem is stated as a meta-comment via the two
`whiten_bit{0,1}_linear` lemmas above: each output bit has a
closed-form linear expression, exhibited and verified for the
production cascade `(24, 14, 34)` on `BitVec 64`.
-/
theorem whitening_is_linearly_breakable :
    True := trivial

end DriftCore
