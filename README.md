# Drift Core™ (DC-100) Reference Implementation

![Version](https://img.shields.io/badge/version-2.0-blue.svg)
![License](https://img.shields.io/badge/license-DSEL--1.0-red.svg)
![Status](https://img.shields.io/badge/status-Patent%20Pending-orange.svg)
![Statistical testing](https://img.shields.io/badge/SP%20800--22-in--house%20tested-lightgrey.svg)

> **A 1-cycle, zero-multiplier arithmetic conditioning & DRBG engine.**

## 1. Overview

The **Drift Core (DC-100)** is a compact cryptographic primitive designed for ultra-low-latency and power-constrained environments where standard AES/SHA architectures are prohibitive.

Based on **Discrete Arithmetic Dynamics (DAD)**, the core conditions and expands entropy (paired with a standard hardware noise source) and produces signatures using a constrained affine transformation ($qS+d$) combined with bitwise state folding.

### Key Performance Metrics

Hardware-validated on FPGA (Tang Primer 20K — Gowin GW2A-18) at bit-exact lockstep against the cycle-accurate software model across the two-FPGA demo suite. ASIC synthesis measured on the SKY130HD open-source PDK at the 13.56 MHz EPC Gen2 / ISO 14443 carrier (area-optimized).

| Metric                    | Specification                                                                                | Competitive position                              |
| ------------------------- | -------------------------------------------------------------------------------------------- | ------------------------------------------------- |
| **Gate Count (bare core, ASIC)** | **2,828 GE** / 17,690.72 µm² (SKY130HD, area-opt, 13.56 MHz) — see [`ASIC_SYNTH_RESULTS.md`](ASIC_SYNTH_RESULTS.md) | Sub-AES (AES-128 ~3,000–3,500 GE); NIST-LWC class |
| **LUT Count (bare core, FPGA)** | **~580 LUT** (cipher_engine.v, single direction, Tang Primer 20K)                       | ~6× smaller than AES-128 (~3,500 LUT)             |
| **Latency**               | **1 Clock Cycle**                                                                            | Instant "Zero-Wait" Wakeup                        |
| **Multipliers**           | **ZERO (0)**                                                                                 | Negligible dynamic power / heat                   |
| **Statistical quality**   | Passes **NIST SP 800-22** (in-house, all 15 families)                                        | Conditioned output                                |

**Envelope verdict (Phase 0).** The 2,828 GE figure passes the NIST-LWC IoT envelope (<3,000 GE) and is comparable to Ascon (~2,300–3,000 GE) and smaller than AES-128 (~3,000–3,500 GE). It does *not* fit the passive-RFID smart-label envelope (<1,000 GE) or smart-dust envelope (<500 GE); a smart-label narrative is not available at this footprint. The honest positioning is **sub-AES, NIST-LWC class**.

**Note on deployed configurations.** Both core figures (2,828 GE / ~580 LUT) are the bare DAD core. Real demonstrators wrap it in transport, framing, and tag logic; measured full-bidirectional demo footprints range from ~900 LUT (Rolling Identity RoT) to ~2,400 LUT (Secure Link) on the FPGA suite. See `formal_verification/` and the two-FPGA demo suite for per-configuration synth reports.

**What is and isn't shown here.** Hardware-validated: deterministic synchronization, keystream generation, and rolling integrity tags between two devices on real silicon. *Not* shown on this FPGA suite: sub-10 µW ASIC power (projection only), radiation tolerance (architectural property; beam test pending), and cryptographic-strength against cryptanalysis (DAD is a lightweight, non-vetted construction; passing NIST SP 800-22 is not a security proof — independent cryptanalytic review is pursued separately).

---

## 2. Repository Contents

This repository contains the **Academic Reference Implementation** of the Drift Engine. It is intended for verification, statistical analysis, and simulation purposes.

- `dad_core.sv` - Synthesizable SystemVerilog source code (Soft IP).
- `dad_tool.cpp` - C++ software model for high-speed stream generation.
- `dad_config.h` - Configuration header containing the "Golden Shift" topology constants.
- `crypto_audit.py` - Python verification script for in-house NIST SP 800-22 pre-testing.

---

## 3. Technology & Applications

The Drift architecture addresses critical bottlenecks in three primary sectors:

### A. Defense & Space (Rad-Tolerant)

- **Problem:** Triple Modular Redundancy (TMR) for radiation hardening triples the size of standard chips.
- **Drift Solution:** **Architectural SEU detection.** The engine detects Single Event Upsets (SEUs) in 1 cycle without 3x hardware overhead — an architectural property, not yet beam-validated.
- **Use Case:** CubeSats, Hypersonic Seekers, Legacy Avionics Retrofit.

### B. Cloud & Infrastructure (Zero-Latency)

- **Problem:** "Entropy Starvation" during VM boot storms (Azure Confidential Computing) and 5G Fronthaul Jitter.
- **Drift Solution:** **Stateless Expansion.** Deterministically expands a seed into a high-rate keystream with flat-line latency (pairs with a standard entropy source for seeding).
- **Use Case:** 5G O-RAN, Azure Sphere, DDoS Defense.

### C. Artificial Intelligence (Provenance)

- **Problem:** Metadata-based watermarks are easily stripped from Generative AI images.
- **Drift Solution:** **"Injection, Not Addition."** The Drift Engine replaces the Gaussian noise seed in Diffusion models, embedding provenance into the pixel physics at generation time.

---

## 4. Validation status

SP 800-22 results are **in-house statistical testing of the conditioned output** (12 of 15 families via a public library + custom control-validated implementations for the rest; all pass). SP 800-22 is a statistical test suite, **not** a certification. The Drift recurrence is a *conditioning component* that pairs with a standard physical noise source; a formal **SP 800-90B** entropy-source validation (which assesses the physical source) and any **FIPS 140-3 / CAVP** validation are handled at module integration.

---

## 5. Licensing & Commercial Use

**⚠️ IMPORTANT LEGAL NOTICE:**

This source code is provided for **Academic Peer Review and Non-Commercial Evaluation** only.

- **You MAY:** Compile, simulate, and verify the statistical performance of the core.
- **You MAY NOT:** Synthesize this code onto physical silicon (FPGA/ASIC) for a commercial product or embed it into firmware distributed to third parties without a license.

**Intellectual Property Protection:** This technology is protected by a priority portfolio of **US Patent Applications**, including:

- **US 63/921,874:** Core Architecture & Stream Generation
- **US 63/926,563:** Space & Radiation Hardened Implementations
- **US 63/926,586:** Legacy Retrofit & Sensor Fusion Systems
- **US 63/922,200:** AI Content Attribution

For commercial licensing (RTL IP, FPGA Bitstreams, or Source Code), please contact:

**Drift Systems Inc.** 📧 **<licensing@driftsystems.io>** 🌐 **[driftsystems.io](https://driftsystems.io)**

---

*Copyright © 2025 Drift Systems Inc. All Rights Reserved.*
