/-
Copyright (c) 2025 Drift Systems Inc. Released under Apache 2.0 license.

# Agile-State (Runtime-Reconfigurable Width) Formalization

Formalizes Appendix B of `DRIFT_AGILE_STATE_design.md`: the
runtime-reconfigurable `drift_core_agile` variant that supports
128/256/512/1024-bit state widths selectable via a mode register.

The existing `DriftRecurrence.lean` infrastructure is already
`W`-parameterized, so every per-mode safety property
(`driftStep`, `driftOrbit`, determinism, eventual periodicity,
recurrent-set bound) holds at each mode for free. This file adds:

* **§1 Mode representation** — the four width tiers.
* **§2 Bit-exact backward compatibility** — the RTL's mask-gated
  wide-adder (`& mode_mask`) is *bit-exactly* the native modular
  recurrence at every active width. THIS IS THE LOAD-BEARING RESULT —
  it discharges the `sorry` Appendix B left for `agile_W128_equiv`.
* **§3 Mode-switch state-erasure** — the post-switch snapshot is
  independent of pre-switch state (no cross-mode leakage *through the
  modeled state*). See the honest-framing caveat below.
* **§4 Inherited per-mode guarantees** — determinism, eventual
  periodicity, recurrent-set cardinality bound, instantiated at every
  mode.
* **§5 K_ROUNDS monotonicity** — the downstream round-count schedule
  is monotone in width.

## Strength of each result (honest framing)

| Result | Content |
|---|---|
| §2 `driftStepAgileRaw_eq` | **Real.** A genuine bit-vector ↔ modular-arithmetic equivalence (`& (2^W−1) = % 2^W`), proved for all `W`. The W=128 case is the backward-compat guarantee. |
| §4 inherited lemmas | **Real but free.** The `W`-parameterized proofs apply verbatim at each mode. |
| §5 monotonicity | **Real but trivial.** Finite-table check over four modes. |
| §3 erasure / no-leakage | **Spec-level, NOT RTL-level.** See caveat. |

### Caveat on §3 (carry this into any external claim)

The state-erasure theorems model a mode switch as "replace the machine
snapshot with all-zeros." They prove that *this model* discards all
pre-switch information — `modeSwitch` ignores its input by
construction, so post-switch behavior cannot depend on pre-switch
state. That is a statement about the **specification**, exactly like
`drift_deterministic` being `rfl`.

They do **not** prove the silicon zeroizes: that the 3-cycle drain
protocol actually clears every register/counter/buffer, leaves no
residual entropy in routing or glitch states, and cannot be bypassed.
That is an RTL-correspondence + side-channel obligation (design doc
§5.2 M1–M4, validated by the 10^10-cycle bit-exact campaign and the
cryptanalytic engagement) — out of scope for Lean per the project's
honest-framing rules.

So the defensible claim is "the mode-switch *design* has no cross-mode
leakage by construction," **not** "the silicon is proven leak-free."
-/

import DriftRecurrence
import EventualPeriodicity
import RecurrentSet
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace DriftCore

/-! ## §1 — Mode representation -/

/-- The four supported state-width tiers (design doc §2.1). -/
inductive Mode where
  | M128 | M256 | M512 | M1024
  deriving DecidableEq, Repr

/-- Active state width in bits for each mode. -/
def Mode.width : Mode → ℕ
  | .M128  => 128
  | .M256  => 256
  | .M512  => 512
  | .M1024 => 1024

/-- Every mode has positive width (needed for `Fin (2^width)` inhabited
and for the `1 % 2^W` reasoning in the safe variant). -/
theorem Mode.one_le_width (m : Mode) : 1 ≤ m.width := by
  cases m <;> decide

/-! ## §2 — Bit-exact backward compatibility (the load-bearing result)

The agile RTL computes on a wide register and masks at the active
width (design doc §3.1):

    expansion             = ((state << 1) + state + 1) & mode_mask
    next_state_arithmetic = (expansion >> 1) & mode_mask

with `mode_mask = 2^W − 1`. We prove this masked bit-vector
computation equals the native modular recurrence `driftStep W`
*bit-exactly*, for every width `W`. The key fact is the same one used
in `Fold.lean`: AND-with-`(2^W − 1)` equals reduction mod `2^W`
(`Nat.and_two_pow_sub_one_eq_mod`).

The `W = 128` instance is the design doc's §6.4 backward-compatibility
guarantee: an agile core in M128 mode produces the same bitstream as
the deployed fixed-width `dad_core`.
-/

/-- RTL-faithful agile arithmetic step on raw bits, matching the
mask-gated wide adder of design doc §3.1 verbatim:
`next = ((((s<<1)+s+1) & (2^W−1)) >> 1) & (2^W−1)`. -/
def driftStepAgileRaw (W : ℕ) (s : ℕ) : ℕ :=
  ((((s <<< 1) + s + 1) &&& (2 ^ W - 1)) >>> 1) &&& (2 ^ W - 1)

/--
**Bit-exact equivalence.** The RTL mask-gated step equals the native
modular `driftStep` at every width. `& (2^W−1)` is `% 2^W`; the
shifts are `*2` and `/2`; the outer mask is a no-op because the
post-division value is already `< 2^W`.
-/
theorem driftStepAgileRaw_eq (W : ℕ) (s : Fin (2 ^ W)) :
    driftStepAgileRaw W s.val = (driftStep W s).val := by
  show driftStepAgileRaw W s.val = ((3 * s.val + 1) % 2 ^ W) / 2
  unfold driftStepAgileRaw
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
             Nat.and_two_pow_sub_one_eq_mod, pow_one]
  rw [show s.val * 2 + s.val + 1 = 3 * s.val + 1 from by ring]
  exact Nat.mod_eq_of_lt
    (lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos W)))

/-- **Agile step, mode-indexed.** In any mode, the agile core's
arithmetic is the native recurrence at that mode's width. (The masking
in the RTL is exactly the active-width window, by
`driftStepAgileRaw_eq`.) -/
def driftStepAgile (m : Mode) (s : Fin (2 ^ m.width)) : Fin (2 ^ m.width) :=
  driftStep m.width s

/--
**Backward compatibility at W = 128 (design doc §6.4).** The agile
core, run in M128 mode through its RTL mask-gated datapath, is
bit-exact with the fixed-width `dad_core`. Direct instance of
`driftStepAgileRaw_eq`.
-/
theorem agile_W128_bit_exact (s : Fin (2 ^ 128)) :
    driftStepAgileRaw 128 s.val = (driftStep 128 s).val :=
  driftStepAgileRaw_eq 128 s

/-- The same bit-exactness, stated at every mode. -/
theorem agile_bit_exact (m : Mode) (s : Fin (2 ^ m.width)) :
    driftStepAgileRaw m.width s.val = (driftStepAgile m s).val :=
  driftStepAgileRaw_eq m.width s

/-! ## §3 — Mode-switch state-erasure (spec-level; see header caveat) -/

/-- A snapshot of the agile core's mutable state. Beyond the main
state register, the mode-switch drain phase must also clear the
round counter and the downstream accumulator/keystream buffer
(design doc §2.4, obligations M1/M2). -/
structure CoreState where
  reg      : ℕ  -- state register
  roundCtr : ℕ  -- K_ROUNDS round counter
  accum    : ℕ  -- cipher_engine buffer / rolling_mac accumulator

/-- The modeled mode-switch drain: produce an all-zero snapshot,
discarding the pre-switch snapshot entirely. -/
def modeSwitchState (_pre : CoreState) : CoreState :=
  { reg := 0, roundCtr := 0, accum := 0 }

/-- **Full zeroization (M1/M2).** After the modeled drain, the state
register, round counter, and accumulator are all zero. -/
theorem modeSwitch_zeroizes_all (pre : CoreState) :
    (modeSwitchState pre).reg = 0 ∧
    (modeSwitchState pre).roundCtr = 0 ∧
    (modeSwitchState pre).accum = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- **No leakage through the modeled state.** The post-switch snapshot
is independent of the pre-switch snapshot — two arbitrary pre-switch
states drain to the same result. (Spec-level: see header caveat.) -/
theorem modeSwitch_independent_of_pre (pre₁ pre₂ : CoreState) :
    modeSwitchState pre₁ = modeSwitchState pre₂ := rfl

/-- Mode-switch as it crosses widths: the post-switch seed in the new
mode, discarding the pre-switch state in the old mode. -/
def modeSwitch (_cur new : Mode) (_s : Fin (2 ^ _cur.width)) :
    Fin (2 ^ new.width) :=
  ⟨0, Nat.two_pow_pos _⟩

/--
**Cross-mode observability isolation (design doc §5.2 M3, structural
part).** The post-switch orbit in the new mode is identical regardless
of the pre-switch mode *or* pre-switch state — even across two
*different* current modes. Hence no observation of post-switch behavior
can carry information about the pre-switch session through the state.

Stronger than the design doc's stated `modeSwitch_no_leakage` (which
fixes a single current mode); the `current ≠ new` hypothesis there is
unnecessary — isolation holds unconditionally. Spec-level (header
caveat): the model discards pre-state by construction.
-/
theorem modeSwitch_orbit_no_leakage
    (cur₁ cur₂ new : Mode)
    (s₁ : Fin (2 ^ cur₁.width)) (s₂ : Fin (2 ^ cur₂.width)) (k : ℕ) :
    driftOrbit new.width (modeSwitch cur₁ new s₁) k =
    driftOrbit new.width (modeSwitch cur₂ new s₂) k := rfl

/-! ## §4 — Per-mode safety guarantees inherited from the W-parameterized core

These instantiate the existing `DriftRecurrence` / `EventualPeriodicity`
/ `RecurrentSet` theorems at every mode, substantiating the design
doc's claim that "agile-state satisfies the same implementation-safety
guarantees as the W=128 baseline at every mode."
-/

/-- Determinism holds at every mode (inherited; `rfl`). -/
theorem agile_deterministic (m : Mode) (seed : Fin (2 ^ m.width)) (k : ℕ) :
    driftOrbit m.width seed k = driftOrbit m.width seed k := rfl

/-- Eventual periodicity (no infinite loops) holds at every mode:
every orbit repeats within `2^width` steps. -/
theorem agile_eventually_periodic (m : Mode) (seed : Fin (2 ^ m.width)) :
    ∃ i j : ℕ, i < j ∧ j ≤ 2 ^ m.width ∧
      driftOrbit m.width seed i = driftOrbit m.width seed j :=
  driftOrbit_eventually_periodic m.width seed

/-- The recurrent-set cardinality bound holds at every mode:
`|R| ≤ 2^(width−1)`. -/
theorem agile_recurrentSet_card_le (m : Mode) :
    (recurrentSet m.width).card ≤ 2 ^ (m.width - 1) :=
  recurrentSet_card_le m.one_le_width

/-! ## §5 — K_ROUNDS scaling monotonicity (structure only; values internal)

The downstream constructions (`rolling_token`, `rolling_mac`) scale
their round counts with width (design doc §3.5). The *concrete*
per-mode round counts are pre-PPA design parameters held in an
internal file (`AgileStateParams.lean`, not in this public repo /
not a build root here).

The **publishable** content is structural and value-free: a
width→rounds step function over the public CNSA tier thresholds
(128/256/512/1024) is monotone in width **provided** its four per-tier
counts are non-decreasing. The internal file discharges that
hypothesis for the actual production counts by `decide` and
instantiates the theorem below. No concrete schedule values — and no
`axiom` — appear in this published file; the monotonicity is a proved
theorem, not an asserted one.
-/

section RoundSchedule

variable (v₀ v₁ v₂ v₃ : ℕ)

/-- Width→rounds step function over the public CNSA tier thresholds,
parameterized by abstract per-tier round counts `v₀ … v₃`. The actual
counts are internal; only the threshold structure is public. -/
def kRoundsSchedule (W : ℕ) : ℕ :=
  if W ≤ 128 then v₀ else if W ≤ 256 then v₁ else if W ≤ 512 then v₂ else v₃

/--
**Threshold-binning preserves monotonicity.** If the per-tier counts
are sorted (`v₀ ≤ v₁ ≤ v₂ ≤ v₃`), the width→rounds schedule is monotone
in width — a wider mode never schedules fewer rounds.

This is the value-free structural guarantee. The sortedness hypotheses
are discharged for the concrete production counts in the internal
`AgileStateParams.lean` by `decide`, which then instantiates this
theorem at the real numbers. No axioms.
-/
theorem kRoundsSchedule_monotone
    (h01 : v₀ ≤ v₁) (h12 : v₁ ≤ v₂) (h23 : v₂ ≤ v₃)
    {W₁ W₂ : ℕ} (hW : W₁ ≤ W₂) :
    kRoundsSchedule v₀ v₁ v₂ v₃ W₁ ≤ kRoundsSchedule v₀ v₁ v₂ v₃ W₂ := by
  unfold kRoundsSchedule
  split_ifs <;> omega

end RoundSchedule

end DriftCore
