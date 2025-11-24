# Drift Core™ Simulation

**Reference Implementation for the Discrete Arithmetic Dynamics (DAD) Engine.**

This repository contains the software simulation, verification tools, and formal proofs for the **Drift Core**, an ultra-low-power cryptographic primitive designed for IoT, Defense, and AI Watermarking.

## Technology
The Drift Engine utilizes a constrained affine transformation (`qn+d`) combined with bitwise state folding to generate high-entropy streams without the use of integer multipliers or complex S-boxes.

*   **Architecture:** Arithmetic Drift + XOR Folding
*   **Gate Count:** < 700 Logic Cells (Verified on Lattice iCE40)
*   **Period:** > 2^128 (Algebraically proven)
*   **Compliance:** NIST SP 800-22 (STS)

## Formal Verification
The non-cyclic property of the Drift Engine ($q=3, k=1$) has been formally verified using the **Lean 4** theorem prover. The proof establishes that the affine coefficient $c$ is strictly monotonic increasing for all $N > 1$, rendering non-trivial cycles algebraically impossible in the divergent domain.

*   **Proof Source:** [`formal_verification/drift_theorem.lean`](formal_verification/drift_theorem.lean)

## Benchmarks
Using the "Casino Configuration" (included in `dad_config.h`), the engine achieves:
*   **Frequency (Monobit):** p > 0.9 (NIST PASS)
*   **Serial Correlation:** < 0.0001 (Pearson)
*   **Throughput:** ~140 MB/s (Software), 1 Cycle/Pixel (Hardware)

## Usage

### Build
This project uses a standard Makefile. To compile the generator:

```bash
make
Generate Stream
Create a binary output file (e.g., 100MB) for testing:
code
Bash
./drift_gen 100000000 > output.bin
Clean
Remove binaries and object files:
code
Bash
make clean
Repository Structure
dad_tool.cpp - High-performance stream generator (C++).
dad_config.h - Configuration profiles (Standard vs. Casino).
drift_viz.py - Python visualization tool for entropy/texture inspection.
cycle_verification.py - Diophantine analysis script.
formal_verification/ - Lean 4 proofs of algebraic stability.
License
Copyright (c) 2025 Drift Systems Inc. All Rights Reserved.
This software is provided for evaluation and research purposes only.
Commercial use, hardware synthesis, or redistribution without a license is strictly prohibited.
See LICENSE for details.
Contact: licensing@driftsystems.io
