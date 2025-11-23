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

DRIFT SYSTEMS SOURCE CODE LICENSE
Copyright (c) 2025 Drift Systems Inc. All Rights Reserved.
1. GRANT OF LICENSE (EVALUATION ONLY)
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to execute the Software solely for the purpose of internal technical evaluation, research, and verification of the underlying technology.
2. RESTRICTIONS
No Commercial Use: You may not use the Software, or any derivative works, in any commercial product, service, or production environment.
No Redistribution: You may not distribute, sublicense, or sell copies of the Software.
No Hardware Synthesis: You may not use the Software or its logic to synthesize hardware circuits (FPGA/ASIC) without a separate commercial license.
3. PATENT NOTICE
The underlying algorithms and architecture are protected by pending US Patents (including 63/921,874 and related filings). Use of this Software does not grant any express or implied license to these patents beyond the limited evaluation rights granted herein.
4. COMMERCIAL LICENSING
For commercial use, hardware integration, or production rights, please contact:
licensing@driftsystems.com (or your contact info)
