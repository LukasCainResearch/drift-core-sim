# Drift Systems — Formal Verification Sources

Lean 4 proof sources backing the implementation-safety claims displayed on driftsystems.io.

## Files

### Top level — Drift Core implementation-safety proofs

| File | What it establishes | Page |
|---|---|---|
| `CarryUniformity.lean` | Bit-level full-adder carry bound: `carry_is_bounded` proves the carry-out is ≤ 1 under bit-valued inputs and bounded incoming carry. | [compute.html § 3.1](https://driftsystems.io/docs/compute.html#proof) |
| `Fold.lean` | Output-stage width invariant: a `2W`-bit input folds to a `W`-bit output via `XOR(high, low)`. `fold_width_invariant` plus `fold_eq_truncate_xor` (RTL equivalence). Matches `dad_core.v` with `W = 64`. | [compute.html § 3.3](https://driftsystems.io/docs/compute.html#proof) |
| `DriftRecurrence.lean` | Determinism of the iterated recurrence on `Fin (2^W)`: `drift_deterministic` (by `rfl`) plus `driftStep_eq_rtl` (bit-exact match to the `((s<<1) + s + 1) >> 1` RTL form). | [compute.html § 3.4](https://driftsystems.io/docs/compute.html#proof) |
| `Completeness.lean` | Erdős covering for T1/T2/T3: `complete_coverage` (at-least-one) and `complete_coverage_exactly_one` (mutually exclusive partition). | [coverage.html § 2](https://driftsystems.io/docs/coverage.html#proof) |
| `SplitLoopAdder.lean` | Hardware popcount split-loop is lossless: `(chunks.map naivePopcount).sum = naivePopcount chunks.flatten`, derived from Lean core's `List.countP_flatten`. | [prime.html § 3](https://driftsystems.io/docs/prime.html#proof) |
| `Whitening.lean` | **Output-stage bijectivity** of the production XOR-shift cascade `(a, b, c) = (24, 14, 34)` on `BitVec 64`: explicit Neumann-series inverse + both inverse identities discharged by `bv_decide` (Std SAT-backed BitVec tactic). | [compute.html § 3.5](https://driftsystems.io/docs/compute.html#proof) |
| `Distribution.lean` | **Distribution-preservation** corollary: `Fintype (BitVec n)` instance + `whitening_singleton_preimage`, `whitening_image_univ`, `whitening_preimage_card`. The empirically-observed 0.999 uniformity bound is research-level (mixing-rate + TV distance + concentration); this file establishes the structural foundation. | [compute.html § 3.6](https://driftsystems.io/docs/compute.html#proof) |
| `EventualPeriodicity.lean` | **No infinite loops** (Phase 4-B.1, pigeonhole version): `driftOrbit_eventually_periodic` — every orbit on `Fin (2^W)` repeats a state within `2^W + 1` iterates. Cycle length bounded by `2^W`. | [compute.html § 3.7](https://driftsystems.io/docs/compute.html#proof) |
| `Noninjectivity.lean` | **`driftStep` is not bijective** (Phase 4-C.1, negative): the arithmetic step's final `/2` drops the LSB, so the image lies in `Fin (2^(W-1))`. Hence not surjective (and therefore not injective). The uniform-measure reading of "ergodicity" is provably false. | [compute.html § 3.8](https://driftsystems.io/docs/compute.html#proof) |
| `WhiteningLinearity.lean` | **GF(2)-linearity of the whitening** (Phase 4-B.3a): `whiten (x ⊕ y) = whiten x ⊕ whiten y` via `bv_decide`. Reduction lemma that lifts the avalanche bound to differential form. | [compute.html § 3.9](https://driftsystems.io/docs/compute.html#proof) |
| `Avalanche.lean` | **Single-bit avalanche bound** (Phase 4-B.3b, partial): for every unit vector `e_i`, `whiten(e_i)` has ≥ 2 set bits. First cryptographic-flavor property; bound is tight (achieved by `e_0, …, e_19`). Full one-iteration avalanche through `driftStep`'s non-linear carry propagation remains research-level. | [compute.html § 3.10](https://driftsystems.io/docs/compute.html#proof) |
| `RecurrentSet.lean` | **`driftStep` is bijective on its eventual image** (Phase 4-C.1 partial-positive): `driftImage_stabilizes`, `recurrentSet_image_eq`, `driftStepEquivRecurrent`, `recurrentSet_card_le ≤ 2^(W-1)`. Complements `Noninjectivity.lean` — uniform measure on the recurrent subset *is* preserved even though uniform measure on the full state space is not. | [compute.html § 3.11](https://driftsystems.io/docs/compute.html#proof) |
| `NonceInjectivity.lean` | **`SECRET ⊕ nonce` is a bijection on nonces** (Phase 4+, protocol-level): `seedState_involutive`, `seedState_bijective`, `seedStatePerm : Equiv.Perm (BitVec 128)`, `seedState_protocol_soundness`. Justifies the cipher_engine.v line-57 nonce-as-IV pattern. | (Phase 4+; not yet on the site) |
| `WhiteningWeakness.lean` | **Whiten alone has trivial linear-cryptanalysis resistance** (Phase 4+, honest framing): `whiten_bit0_linear`, `whiten_bit1_linear` exhibit explicit 6-bit XOR linear approximations with bias 1. `whiten_diff_bit0` lifts to differential form. Any cryptographic strength must come from `driftStep`, not whiten. | (Phase 4+; not yet on the site) |
| `OutputChain.lean` | **End-to-end output composition** (Phase 4+, structural): `dataOut = whiten ∘ foldBV ∘ driftStepBV` on BitVec 128 → BitVec 64. `foldBV_xor`, `whiten_foldBV_xor` (linearity of output stage); `dataOut_not_linear`, `driftStepBV_not_linear` (non-linearity confined to driftStep, with concrete counterexample `(s, d) = (1, 2)`). | (Phase 4+; not yet on the site) |
| `DriftRecurrenceSafe.lean` | **ZeroTrap mitigation** (Phase 4+, RTL counterpart): `driftStep_eq_zero_iff` (characterizes the trap inputs `(3s+1) mod 2^W ∈ {0, 1}`); `driftStepSafe` (mitigated step with `1`-reroute); `driftStepSafe_ne_zero`, `driftSafeOrbit_ne_zero` (orbit-level safety). Formal counterpart to the proposed `next_would_be_zero ? 128'h1 : ...` RTL change. | (Phase 4+; not yet on the site) |

### `ABCFormalization/` — proofs of the ABC carry / Kummer bridge

| File | What it establishes | Page |
|---|---|---|
| `ABCFormalization/Kummer.lean` | Base-2 Kummer bridge: bit-disjoint ↔ no-carry ↔ odd binomial. Includes `laminar_implies_odd_binomial` (replaces the prior axiomatized version). | [entropy_barriers.html § 3](https://driftsystems.io/docs/entropy_barriers.html#proof) |
| `ABCFormalization/CarryTransducer.lean` | Block-level carry transducer for `×p` multiplication; `mulBlockCarry_lt` proves the FSM state space is `{0..p-1}`; `transducer_correct` proves the transducer is a faithful implementation of `×p`. | [compute.html § 3.2](https://driftsystems.io/docs/compute.html#proof) |
| `ABCFormalization/CarryGraph.lean` | Global FSM-state-space bound: `blockCarry_lt` proves the carry never exceeds `p` at any block position. Fuel-accounting machinery for the global popcount lower bound. | [compute.html § 3.2](https://driftsystems.io/docs/compute.html#proof) |
| `ABCFormalization/Basic.lean`, `ABCFormalization/Bitwise.lean`, `ABCFormalization/BlockDecomposition.lean` | Sibling-library closure required by the three files above. Published here so the entire ABC chain is reproducible end-to-end. | (background — not displayed on any page) |

## Build status

```bash
# from repo root
lake build           # builds everything; cached after first run
lake build Fold      # builds a single target
```

All files build clean against a stock Mathlib install with **no `sorry` and no axioms beyond Mathlib's standard library**, pinned to Mathlib commit `bcc3f989` and Lean toolchain `v4.26.0-rc2` (see [`lakefile.toml`](../lakefile.toml), [`lean-toolchain`](../lean-toolchain), [`lake-manifest.json`](../lake-manifest.json)). First-time `lake build` will fetch Mathlib (≈30 min full build; use `lake exe cache get` to pull pre-built artifacts for a few minutes instead).

CI verifies the build on every push that touches Lean sources or the lake config — see [.github/workflows/lean.yml](../.github/workflows/lean.yml).

## Honest-framing reminder

These Lean files cover **implementation-safety** properties of the Drift Core — bounded carry, FSM-state-space bound, fold width invariant, deterministic iteration, complete state coverage, lossless split-loop popcount, and the Kummer carry-count bridge. They do **not** establish cryptographic security. Cryptographic security is pursued separately via independent cryptanalytic peer review.

## License

Apache 2.0 — same as the parent repository.
