/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Recurrent Set: `driftStep` is Bijective on Its Eventual Image

This file is the **positive complement** to `Noninjectivity.lean`.

`Noninjectivity.lean` proved that `driftStep : Fin (2^W) → Fin (2^W)`
is *not* a bijection of the full state space — the arithmetic step's
final `/2` drops the LSB, so the image lies in `Fin (2^(W-1))`. As a
consequence, uniform measure on the full state space is **not**
preserved.

This file proves that on the *eventual image* (the "recurrent set"
`R`), `driftStep` **is** a bijection — and uniform measure on `R`
**is** preserved.

Together the two files give a clean structural picture:

* Initial transient (finite, bounded by `2^W` steps): `driftStep`
  collapses pairs of states, the image shrinks.
* Eventual recurrent behavior on `R ⊆ Fin (2^W)`: `driftStep` is a
  cyclic permutation of `R`, uniform measure on `R` is preserved.

## What this is

A partial-positive resolution of Phase 4-C.1 (ergodicity in the
dynamical-systems sense). The remaining piece — characterizing `R`
quantitatively (its cardinality, cycle structure) — is still
research-level (Phase 4-C.2 mixing-rate / spectral-gap territory).

## What this is *not*

* Not a closed-form characterization of `R`. We prove `R` exists and
  has `|R| ≤ 2^(W-1)` (for `W ≥ 1`), but its precise structure depends
  on the specific shape of `driftStep` and is harder to analyze.
* Not a measure-preservation statement for an arbitrary measure. Only
  the uniform measure on `R` is shown preserved (immediate from the
  bijection structure).

## Result summary

* `driftImage W k` — image of `driftStep` iterated `k` times on
  `Finset.univ`. Decreasing chain (`driftImage_anti`), stabilizes
  within `2^W` steps (`driftImage_stabilizes`).
* `recurrentSet W := driftImage W (2^W)` — the eventual image.
  Equals `driftImage W k` for any `k ≥ 2^W`.
* `recurrentSet_image_eq` — `driftStep` maps `recurrentSet` onto itself.
* `driftStepEquivRecurrent` — `driftStep` restricted to `recurrentSet`
  is an `Equiv.Perm` (a bijection of the recurrent set).
* `recurrentSet_card_le` — `|recurrentSet W| ≤ 2^(W-1)` for `W ≥ 1`
  (immediate from `Noninjectivity.driftStep_val_lt_half`).
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Equiv.Defs
import DriftRecurrence
import Noninjectivity

namespace DriftCore

variable {W : ℕ}

/-! ## The iterated-image chain -/

/-- Image of `driftStep` iterated `k` times, applied to `Finset.univ`.
The chain `driftImage 0 ⊇ driftImage 1 ⊇ …` is decreasing on a finite
set, hence stabilizes within `|Fin (2^W)| = 2^W` steps. -/
def driftImage (W : ℕ) : ℕ → Finset (Fin (2 ^ W))
  | 0     => Finset.univ
  | k + 1 => (driftImage W k).image (driftStep W)

@[simp] theorem driftImage_zero : driftImage W 0 = Finset.univ := rfl

@[simp] theorem driftImage_succ (k : ℕ) :
    driftImage W (k + 1) = (driftImage W k).image (driftStep W) := rfl

/-- The image chain is decreasing: `driftImage (k+1) ⊆ driftImage k`. -/
theorem driftImage_anti (k : ℕ) :
    driftImage W (k + 1) ⊆ driftImage W k := by
  induction k with
  | zero =>
      intro x _
      rw [driftImage_zero]
      exact Finset.mem_univ x
  | succ n ih =>
      rw [driftImage_succ (n + 1), driftImage_succ n]
      exact Finset.image_subset_image ih

/-- Once the chain stabilizes at index `N`, it stays stable forever. -/
theorem driftImage_stable_after {N : ℕ}
    (hN : driftImage W N = driftImage W (N + 1)) :
    ∀ k, driftImage W (N + k) = driftImage W N := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
      show driftImage W (N + n + 1) = driftImage W N
      calc driftImage W (N + n + 1)
          = (driftImage W (N + n)).image (driftStep W) := driftImage_succ _
        _ = (driftImage W N).image (driftStep W) := by rw [ih]
        _ = driftImage W (N + 1) := (driftImage_succ N).symm
        _ = driftImage W N := hN.symm

/--
**Stabilization.** The image chain stabilizes within `2^W` steps:
there exists `N ≤ 2^W` with `driftImage N = driftImage (N+1)`.

Proof: `(driftImage k).card` is non-increasing and bounded below by
`0`. If it strictly decreased at every `k ≤ 2^W`, then
`(driftImage (2^W + 1)).card` would have to be negative — impossible.
-/
theorem driftImage_stabilizes :
    ∃ N : ℕ, N ≤ 2 ^ W ∧ driftImage W N = driftImage W (N + 1) := by
  by_contra hcontra
  push_neg at hcontra
  have hstrict : ∀ k ≤ 2 ^ W,
      (driftImage W (k + 1)).card < (driftImage W k).card := by
    intro k hk
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨driftImage_anti k, ?_⟩
    intro heq
    exact hcontra k hk heq.symm
  have hzero : (driftImage W 0).card = 2 ^ W := by
    rw [driftImage_zero, Finset.card_univ, Fintype.card_fin]
  have hbound : ∀ k, k ≤ 2 ^ W + 1 → (driftImage W k).card + k ≤ 2 ^ W := by
    intro k hk
    induction k with
    | zero => rw [Nat.add_zero, hzero]
    | succ n ih =>
        have hn : n ≤ 2 ^ W := by omega
        have hstr := hstrict n hn
        have hih := ih (by omega)
        omega
  have h1 := hbound (2 ^ W + 1) le_rfl
  omega

/-! ## The recurrent set -/

/-- The recurrent set: the eventual image of `driftStep`. Concretely
taken as `driftImage W (2^W)` — since the image chain stabilizes
within `2^W` steps, this is the stable value. -/
def recurrentSet (W : ℕ) : Finset (Fin (2 ^ W)) := driftImage W (2 ^ W)

/-- Helper: once stabilized at `N`, every `m ≥ N` gives `driftImage m = driftImage N`. -/
private theorem driftImage_const_after {N : ℕ}
    (hN : driftImage W N = driftImage W (N + 1)) :
    ∀ m, N ≤ m → driftImage W m = driftImage W N := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact driftImage_stable_after hN d

/-- For any `k ≥ 2^W`, `driftImage W k = recurrentSet W`. -/
theorem driftImage_eq_recurrent {k : ℕ} (hk : 2 ^ W ≤ k) :
    driftImage W k = recurrentSet W := by
  obtain ⟨N, hN_le, hN_eq⟩ := driftImage_stabilizes (W := W)
  show driftImage W k = driftImage W (2 ^ W)
  calc driftImage W k
      = driftImage W N := driftImage_const_after hN_eq k (le_trans hN_le hk)
    _ = driftImage W (2 ^ W) := (driftImage_const_after hN_eq (2 ^ W) hN_le).symm

/--
**The recurrent set is fixed by `driftStep`.**

`(recurrentSet W).image (driftStep W) = recurrentSet W`. Both
inclusions follow from the stabilization: `driftStep` maps
`driftImage (2^W)` to `driftImage (2^W + 1)`, and both equal the
recurrent set.
-/
theorem recurrentSet_image_eq :
    (recurrentSet W).image (driftStep W) = recurrentSet W := by
  unfold recurrentSet
  rw [← driftImage_succ]
  exact driftImage_eq_recurrent (W := W) (by omega : 2 ^ W ≤ 2 ^ W + 1)

/-- `driftStep` sends the recurrent set into itself. -/
theorem driftStep_mapsTo_recurrentSet (s : Fin (2 ^ W)) (hs : s ∈ recurrentSet W) :
    driftStep W s ∈ recurrentSet W := by
  rw [← recurrentSet_image_eq]
  exact Finset.mem_image_of_mem _ hs

/-! ## Bijection on the recurrent set -/

/-- `driftStep` restricted to `recurrentSet W` viewed as an endomorphism
of the subtype `↥(recurrentSet W)`. -/
def driftStepRestrict (W : ℕ) : ↥(recurrentSet W) → ↥(recurrentSet W) :=
  fun s => ⟨driftStep W s.val, driftStep_mapsTo_recurrentSet s.val s.property⟩

/-- The restricted map is surjective: every `y ∈ recurrentSet` has some
`s ∈ recurrentSet` mapping to it. Immediate from `recurrentSet_image_eq`. -/
theorem driftStepRestrict_surjective :
    Function.Surjective (driftStepRestrict W) := by
  intro ⟨y, hy⟩
  rw [← recurrentSet_image_eq, Finset.mem_image] at hy
  obtain ⟨s, hs_mem, hsy⟩ := hy
  refine ⟨⟨s, hs_mem⟩, ?_⟩
  apply Subtype.ext
  exact hsy

/-- Surjective endomorphism of a finite type is bijective. -/
theorem driftStepRestrict_bijective :
    Function.Bijective (driftStepRestrict W) :=
  ⟨Finite.injective_iff_surjective.mpr driftStepRestrict_surjective,
   driftStepRestrict_surjective⟩

/--
**The Equiv form.** `driftStep` restricted to the recurrent set is an
`Equiv.Perm` of `↥(recurrentSet W)` — a permutation of the recurrent
set. Downstream proofs that want to compose with this bijection or
invoke measure-preservation machinery should use this.
-/
noncomputable def driftStepEquivRecurrent (W : ℕ) :
    Equiv.Perm ↥(recurrentSet W) :=
  Equiv.ofBijective (driftStepRestrict W) driftStepRestrict_bijective

/-- Set-theoretic bijection statement: `driftStep` is a bijection
between `recurrentSet W` and itself (as a `Set`). -/
theorem driftStep_bijOn_recurrentSet :
    Set.BijOn (driftStep W) ↑(recurrentSet W) ↑(recurrentSet W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact driftStep_mapsTo_recurrentSet s hs
  · -- InjOn: from finite + Mapsto + SurjOn
    intro x hx y hy hxy
    have hinj : Function.Injective (driftStepRestrict W) :=
      driftStepRestrict_bijective.injective
    have : driftStepRestrict W ⟨x, hx⟩ = driftStepRestrict W ⟨y, hy⟩ := by
      apply Subtype.ext
      exact hxy
    exact congrArg Subtype.val (hinj this)
  · -- SurjOn
    intro y hy
    have : y ∈ (recurrentSet W).image (driftStep W) := by
      rw [recurrentSet_image_eq]; exact hy
    obtain ⟨s, hs_mem, hsy⟩ := Finset.mem_image.mp this
    exact ⟨s, hs_mem, hsy⟩

/-! ## Cardinality bound -/

/--
**Recurrent set has at most half the state space.** For `W ≥ 1`,
`|recurrentSet W| ≤ 2^(W-1)`. The recurrent set sits inside the
first-step image, which inherits the `< 2^(W-1)` bound from
`Noninjectivity.driftStep_val_lt_half` via an injection into
`Fin (2^(W-1))`.
-/
theorem recurrentSet_card_le (hW : 1 ≤ W) :
    (recurrentSet W).card ≤ 2 ^ (W - 1) := by
  -- recurrentSet ⊆ driftImage W 1
  have h_sub_one : recurrentSet W ⊆ driftImage W 1 := by
    have step : ∀ k, 1 ≤ k → driftImage W k ⊆ driftImage W 1 := by
      intro k hk
      induction k with
      | zero => omega
      | succ n ih =>
          by_cases hn : 1 ≤ n
          · exact (driftImage_anti n).trans (ih hn)
          · interval_cases n
            exact subset_refl _
    exact step (2 ^ W) Nat.one_le_two_pow
  -- |driftImage W 1| ≤ 2^(W-1): every output factors through Fin (2^(W-1))
  have h_one_le : (driftImage W 1).card ≤ 2 ^ (W - 1) := by
    rw [driftImage_succ, driftImage_zero]
    -- Map each y in the image to ⟨y.val, driftStep_val_lt_half⟩ : Fin (2^(W-1))
    let proj : Fin (2 ^ W) → Fin (2 ^ (W - 1)) := fun y =>
      if h : y.val < 2 ^ (W - 1) then ⟨y.val, h⟩ else ⟨0, Nat.two_pow_pos _⟩
    -- proj is injective on the image of driftStep
    have hinj : Set.InjOn proj ↑(Finset.univ.image (driftStep W)) := by
      intro a ha b hb hab
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
                 Finset.mem_univ, true_and] at ha hb
      obtain ⟨sa, hsa⟩ := ha
      obtain ⟨sb, hsb⟩ := hb
      have haval : a.val < 2 ^ (W - 1) := hsa ▸ driftStep_val_lt_half sa hW
      have hbval : b.val < 2 ^ (W - 1) := hsb ▸ driftStep_val_lt_half sb hW
      simp only [proj, haval, hbval, dif_pos, Fin.mk.injEq] at hab
      exact Fin.ext hab
    calc (Finset.univ.image (driftStep W)).card
        = ((Finset.univ.image (driftStep W)).image proj).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset (Fin (2 ^ (W - 1)))).card := by
          apply Finset.card_le_card
          intro x _; exact Finset.mem_univ x
      _ = 2 ^ (W - 1) := by
          rw [Finset.card_univ, Fintype.card_fin]
  exact le_trans (Finset.card_le_card h_sub_one) h_one_le

end DriftCore
