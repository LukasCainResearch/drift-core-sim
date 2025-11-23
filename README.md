# Drift Core™ Simulation

**Reference Implementation for the Discrete Arithmetic Dynamics (DAD) Engine.**

This repository contains the software simulation and verification tools for the **Drift Core**, an ultra-low-power cryptographic primitive designed for IoT, Defense, and AI Watermarking.

## Technology
The Drift Engine utilizes a constrained affine transformation (`qn+d`) combined with bitwise state folding to generate high-entropy streams without the use of integer multipliers or complex S-boxes.

*   **Architecture:** Arithmetic Drift + XOR Folding
*   **Gate Count:** < 700 Logic Cells (Lattice iCE40)
*   **Period:** > 2^128
*   **Compliance:** NIST SP 800-22 (STS)

## Benchmarks
Using the "Casino Configuration" (included in `dad_config.h`), the engine achieves:
*   **Frequency (Monobit):** p > 0.9
*   **Serial Correlation:** < 0.0001 (Pearson)
*   **Throughput:** ~140 MB/s (Software), 1 Cycle/Pixel (Hardware)

## Usage
Compile the generator:
```bash
g++ -O3 dad_tool.cpp -o drift_gen
