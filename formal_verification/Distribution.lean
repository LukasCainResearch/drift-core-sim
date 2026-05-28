/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Distribution-Preservation Under the Drift Core Output Stage

This file establishes the **structural** distribution result for the
Drift Core's output stage: because `Whitening.whiten` is a bijection of
`BitVec 64` (`Whitening.lean`), it is *distribution-preserving* — the
output histogram over any multiset of inputs equals the input histogram
under the bijective relabeling.

## Results (clean, Lean-proved)

* `whitening_singleton_preimage` — every 64-bit output value has exactly
  one 64-bit pre-image under the whitening. The "no two inputs collide"
  form of bijectivity.
* `whitening_image_univ` — the whitening surjects onto `BitVec 64`.
  When run on every input exactly once, every output appears exactly
  once. Population-level statement of "uniform inputs → uniform outputs."
* `whitening_preimage_card` — for any output set `S`, the number of
  inputs mapping into `S` equals `|S|`. Generalizes the singleton
  result; the "no aliasing, no collapse" property.

## What this *doesn't* yet establish (research-level, deferred)

The empirically-observed "0.999 uniformity over 10,000 trials" claim
involves three additional ingredients beyond what's proved here:

1. **Input distribution from the iterated recurrence is approximately
   uniform.** The actual upstream input to the whitening is the
   fold-step output of the iterated `driftStep`, not a uniform random
   variable. Establishing that the iterated recurrence drives the input
   close to uniform is *mixing-rate* / *spectral-gap* territory
   (Phase 4.C.2 of the roadmap).

2. **Total-variation distance bound.** The "ε-uniform" claim should be
   stated in terms of TV distance between the empirical histogram and
   the uniform distribution. Mathlib's `MeasureTheory.PMF` machinery
   supports this but the proof connecting it to a concrete `ε` requires
   the mixing result above.

3. **Finite-sample concentration.** The "10,000 trials" framing is a
   finite-sample claim; the population-level bound from (2) becomes
   a high-probability sample-level statement via Hoeffding/DKW.

These are explicitly research-level per the roadmap (Phase 4.B.3 and
4.C.2) and gated on external collaboration. This file provides the
structural foundation; the quantitative bound is future work.
-/

import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Defs
import Whitening

namespace DriftCore

/-! ## Fintype instance for `BitVec` -/

/-- The natural equivalence between `BitVec n` and `Fin (2 ^ n)`. -/
def bitVecEquivFin (n : ℕ) : BitVec n ≃ Fin (2 ^ n) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeBitVec (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv _ (bitVecEquivFin n).symm

@[simp] lemma card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [Fintype.card_congr (bitVecEquivFin n), Fintype.card_fin]

/-! ## Bijectivity → distribution preservation -/

/--
**Singleton pre-image is unique.** For every 64-bit output value `y`,
there is exactly one 64-bit input `x` with `whiten x = y`.

This is the elementary "no aliasing" form of bijectivity: the whitening
cascade does not collapse any two distinct inputs to the same output.
-/
theorem whitening_singleton_preimage (y : BitVec 64) :
    (Finset.univ.filter (fun x => whiten x = y)).card = 1 := by
  have ⟨x, hx⟩ := whiten_bijective.surjective y
  rw [show Finset.univ.filter (fun z => whiten z = y) = {x} from ?_]
  · exact Finset.card_singleton _
  · ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun hz => whiten_bijective.injective (hz.trans hx.symm), ?_⟩
    rintro rfl; exact hx

/--
**Image is full.** The whitening surjects onto `BitVec 64`: every
64-bit value appears as the output of exactly one input.

Restated: when we apply the whitening to every input exactly once, the
output set equals the entire `BitVec 64`. The whitening permutes the
input set; it doesn't shrink or expand it.
-/
theorem whitening_image_univ :
    (Finset.univ : Finset (BitVec 64)).image whiten = Finset.univ :=
  Finset.image_univ_of_surjective whiten_bijective.surjective

private lemma unwhiten_injective : Function.Injective unwhiten :=
  whitenEquiv.symm.injective

/--
**Pre-image cardinality.** For any subset `S` of `BitVec 64`, the number
of inputs whose whitening lands in `S` equals `|S|`.

Generalizes `whitening_singleton_preimage` from singletons to arbitrary
subsets. This is the cleanest form of "the whitening is a measure-
preserving permutation of `BitVec 64`" — it preserves counts on every
measurable event.
-/
theorem whitening_preimage_card (S : Finset (BitVec 64)) :
    (Finset.univ.filter (fun x => whiten x ∈ S)).card = S.card := by
  have heq : Finset.univ.filter (fun x => whiten x ∈ S) = S.image unwhiten := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun hx => ⟨whiten x, hx, unwhiten_whiten x⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    rw [whiten_unwhiten]; exact hy
  rw [heq, Finset.card_image_of_injective _ unwhiten_injective]

/-! ## Equivalence packaging -/

/-- The whitening as an `Equiv` of `BitVec 64`. This is the same as
`Whitening.whitenEquiv` but re-exposed here so distribution-level proofs
have a single import. -/
def whitenEquiv64 : BitVec 64 ≃ BitVec 64 := whitenEquiv

end DriftCore
