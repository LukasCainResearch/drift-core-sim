# Drift Systems — Formal Verification Sources

Lean 4 proof sources backing the implementation-safety claims displayed on driftsystems.io.

## Files

| File | What it establishes | Page |
|---|---|---|
| `CarryUniformity.lean` | Bit-level full-adder carry bound: carry ≤ 2 under bit-valued inputs and bounded incoming carry. | [compute.html § 3.1](https://driftsystems.io/docs/compute.html#proof) |
| `CarryTransducer.lean` | Block-level carry transducer for ×p multiplication; `mulBlockCarry_lt` proves the FSM state space is {0..p-1}; `transducer_correct` proves the transducer is a faithful implementation of ×p. | [compute.html § 3.2](https://driftsystems.io/docs/compute.html#proof) |
| `CarryGraph.lean` | Global FSM-state-space bound: `blockCarry_lt` proves the carry never exceeds p at any block position. Fuel-accounting machinery for the global popcount lower bound. | [compute.html § 3.2](https://driftsystems.io/docs/compute.html#proof) |
| `Kummer.lean` | Base-2 Kummer bridge: bit-disjoint ↔ no-carry ↔ odd binomial. Includes `laminar_implies_odd_binomial` (replaces the prior axiomatized version). | [entropy_barriers.html § 3](https://driftsystems.io/docs/entropy_barriers.html#proof) |

## Build status

`CarryTransducer.lean`, `CarryGraph.lean`, and `Kummer.lean` import from a larger ABCFormalization sibling library (`Bitwise`, `BlockDecomposition`, plus Mathlib `NumberTheory.Padics.PadicVal.Basic`). The sibling files are not currently in this public repo; the displayed theorems and proof bodies match the canonical versions verbatim.

A `lakefile.toml` for end-to-end reproducibility (including the sibling imports) is on the roadmap; in the interim, the displayed proofs in the canonical files contain no `sorry` and only standard-Mathlib axioms.

`CarryUniformity.lean` is self-contained and builds against a stock Mathlib 4 install.

## Honest-framing reminder

These Lean files cover **implementation-safety** properties of the Drift core — bounded carry, FSM-state-space bound, Kummer carry-count bridge. They do **not** establish cryptographic security. Cryptographic security is pursued separately via independent cryptanalytic peer review.

## License

Apache 2.0 — same as the parent repository.
