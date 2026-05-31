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
| **Gate Count (bare Drift Core, ASIC)** | **2,828 GE** / 17,690.72 µm² (SKY130HD, area-opt, 13.56 MHz) — see [`ASIC_SYNTH_RESULTS.md`](ASIC_SYNTH_RESULTS.md) | Sub-AES (AES-128 ~3,000–3,500 GE); NIST-LWC class |
| **LUT Count (bare Drift Core, FPGA)** | **~580 LUT** (Tang Primer 20K, GW2A-18)                                              | ~6× smaller than AES-128 (~3,500 LUT)             |
| **Latency**               | **1 Clock Cycle**                                                                            | Instant "Zero-Wait" Wakeup                        |
| **Multipliers**           | **ZERO (0)**                                                                                 | Negligible dynamic power / heat                   |
| **Statistical quality**   | Passes **NIST SP 800-22** (in-house, all 15 families)                                        | Conditioned output                                |

**ASIC Phase 0 footprint table — measured 2026-05-29 (SKY130HD, AREA-0, 13.56 MHz, all-standard-cell synthesis).**

| Module | Configuration | GE | Area (µm²) | Notes |
|---|---|---|---|---|
| `dad_core` | bare PRG | **2,828** | 17,690.72 | Baseline. NIST-LWC class. |
| `rolling_token` | 128-bit iterated-permutation MAC | **2,914** | 18,229.98 | Only ~3% over `dad_core`. |
| `rolling_mac` | sponge MAC, 128-bit accumulator | **4,717** | 29,504.55 | Sub-AES; +67% vs `dad_core` for the accumulator + 128-bit whiten cascade. |
| `cipher_engine` | MAXWORDS=4 (32-byte msg max) | **5,736** | 35,881.91 | Short control msgs (BLE adverts, MQTT-SN). |
| `cipher_engine` | **MAXWORDS=8 (64-byte msg max)** | **7,482** | 46,806.14 | **Covers >95% of LoRaWAN/Zigbee/BLE traffic — recommended IoT deployment configuration.** |
| `cipher_engine` | MAXWORDS=16 (128-byte msg max) | **11,096** | 69,416.58 | Medium control + small data. |
| `cipher_engine` | MAXWORDS=32 (256-byte msg max) | **18,280** | 114,359.68 | Canonical / full FPGA-bitstream-matching. |
| `freqhop_top` (Test 02) | full demo, MAXWORDS=32 | **23,202** | 145,149.21 | Hardware-validated 2026-05-25. |
| `iff_top` (Test 03) | full demo, MAXWORDS=32 | **42,695** | 267,098.67 | Hardware-validated 2026-05-25 (paired-pass + wrong-secret-reject). |

**Linear scaling model for `cipher_engine`**: `footprint ≈ 4,000 GE overhead + 446 GE per 64-bit keystream word`. The overhead is `dad_core` + FSM + read mux + nonce path; the per-word term is the flip-flop storage and read-mux growth. Sweep validated to within 0.65% against the composition-level `iff_top` measurement at MW=8.

**Envelope verdict (Phase 0).** The bare Drift Core (2,828 GE) passes the NIST-LWC IoT envelope (<3,000 GE) and is comparable to Ascon (~2,300–3,000 GE) and smaller than AES-128 (~3,000–3,500 GE). It does *not* fit the passive-RFID smart-label envelope (<1,000 GE) or smart-dust envelope (<500 GE). Honest positioning: **sub-AES, NIST-LWC class**.

**Width-parameterized scaling family (measured 2026-05-29).** The Drift Core recurrence extends naturally to wider state widths. SKY130HD measurements at W=128/256/512/1024:

| State width W (bits) | GE | Area (µm²) | GE per state-bit |
|---|---|---|---|
| 128 (baseline) | **2,828** | 17,690.72 | 22.10 |
| 256 | **5,696** | 35,617.28 | 22.25 |
| 512 | **11,408** | 71,322.50 | 22.28 |
| 1024 | **23,021** | 144,021.88 | 22.49 |

Per-bit variance is 1.8% across the 8× width range — clean linear scaling at ~22.3 GE per state bit. Wider state widths cover post-quantum-relevant security tiers via the Grover bound (Grover-effective post-quantum security ≈ W/2 bits): W=256 covers CNSA 2.0 IoT minimums (Grover-effective 128-bit, the standard PQC bar for symmetric primitives); W=512 covers high-classification deployments; W=1024 provides deep margin against potential future symmetric-cryptanalysis advances for buyers requiring headroom beyond the Grover-effective bar (not a quantum hedge — Shor's algorithm does not apply to symmetric crypto).

**Temporal state extension via narrow-physical-ALU iteration (measured 2026-05-29).** A second silicon-implementation embodiment of the same algorithm family — see US PPA 63/929,897, filed 2025-12-03 — places the same wide-W operation behind a narrower physical ALU that iterates over a wide virtual state stored in a register buffer, trading multi-cycle latency per virtual step for footprint. Production-variant measurements:

| Variant | Virtual state | Cycles per step | GE | GE per virtual-bit | Savings vs single-cycle |
|---|---|---|---|---|---|
| `drift_flex_v3_p32_v128` | 128 bits | 9 | **2,064** | 16.1 | -27% vs 2,828 |
| `drift_flex_v3_p64_v256` | 256 bits | 9 | **3,841** | 15.0 | -33% vs 5,696 |
| `drift_flex_v3_p64_v512` | 512 bits | 17 | **6,799** | 13.3 | -40% vs 11,408 |
| `drift_flex_v3_p64_v1024` | 1024 bits | 33 | **12,667** | 12.4 | -45% vs 23,021 |

At W=1024 the per-virtual-bit cost is 12.4 GE — at the architectural floor for SKY130 standard-cell synthesis (bottom-up estimate: ~6 GE/bit state storage + ~3 GE/bit whitening cascade + ~2 GE/bit shift muxes + ~1 GE/bit control ≈ 12 GE/bit). At W=128 the per-virtual-bit cost is 16.1 GE; the variant undercuts the bare Drift Core baseline (2,828 GE) at the same security tier by 27%, and lands below AES-128 (~3,000–3,500 GE) and Ascon (~2,300–3,000 GE) while competitive vs SIMON/SPECK (~1,500–2,500 GE at 128-bit). The chunked computation produces output bit-exactly equivalent to the native physical-width-W variant — validated via C oracle over 5×10⁶ consecutive virtual-step iterations (5 configurations × 10⁶ iterations each, all pass).

**Honest framing on these silicon-data results.** We are not aware of a published symmetric-cryptographic primitive with a 256-bit state below 3,841 GE on SKY130 specifically, or a published 1024-bit symmetric cryptographic state silicon-measured below 12,667 GE on any open-source standard-cell PDK. Smaller GE figures for 256-bit-state primitives exist on commercial 130–180 nm processes (e.g., SPONGENT-256 ≈ 1,950 GE on UMC 0.13 µm, PHOTON-256 ≈ 2,177 GE on UMC 0.18 µm); direct GE-to-GE comparisons across PDKs are approximate due to cell-library normalization differences. Wider symmetric states are routine on commercial nodes (Keccak-f[1600], SHA-512 1024-bit message schedule); the open-PDK + silicon-measured + 1024-bit-symmetric-state combination is the specific novelty here.

**Note on `cipher_engine` keystream buffer.** The `MAXWORDS` parameter sets the keystream-buffer size (32 by default; 4/8/16/32 measured). On SKY130HD with all-standard-cell synthesis the buffer maps to discrete flip-flops, so footprint scales linearly with the parameter. For typical IoT messaging (LoRaWAN, Zigbee, BLE), MAXWORDS=8 (64-byte payload per nonce, 7,482 GE) is the recommended deployment configuration. For full TLS-class 256-byte payloads, the canonical MAXWORDS=32 (18,280 GE) is used — this is the configuration validated in the FPGA bitstreams.

**ASIC Phase 2/3 sign-off — completed 2026-05-30 (SKY130HD, OpenLane full flow, 100 MHz target).** Five designs taken through the complete OpenLane flow (synth → floorplan → placement → CTS → detailed route → multi-corner STA → power → GDSII), speed-optimized. **All five DRC-clean, LVS-clean, no setup/hold violations at the typical corner, with GDSII.**

| Design | Cells | GE | Routed die | fmax (tt / ss) | Dynamic P @ 100 MHz | @ 13.56 MHz | Leakage |
|---|---|---|---|---|---|---|---|
| `dad_core` (bare PRG) | 2,081 | 3,557 | 0.072 mm² | 182 / 93 MHz | **4.72 mW** ◊ | ~640 µW | 14.7 nW |
| `cipher_engine` (keystream) | 10,797 | 19,270 | 0.364 mm² | 113 / 76 MHz | **25.5 mW** ◊ | ~3.5 mW | 88.2 nW |
| `secure_link_top` (full TX+RX) | 25,465 | 46,675 | 0.865 mm² | 161 / 82 MHz | **58.2 mW** ◊ | ~7.9 mW | 212 nW |
| `lr_top_primer` (Test 04 verifier) | 6,453 | 11,113 | 0.213 mm² | 161 / 81 MHz | 51.6 mW † | ~7.0 mW | 46.4 nW |
| `rt_top_primer` (Test 05 verifier) | 5,754 | 10,836 | 0.208 mm² | 177 / 91 MHz | 43.2 mW † | ~5.9 mW | 46.8 nW |

**◊** = VCD-backannotated from a real gate-level simulation (true switching activity). **†** = default-activity `report_power` upper bound (verifier tops need framed-input stimulus for VCD; pending).

- **Frequency:** ~80–90 MHz guaranteed across all PVT corners, ~160–200 MHz typical. `dad_core` is **delay-bound at the 128-bit adder** — fmax saturates at ~200 MHz typical / ~105 MHz worst-corner; spending more cell area buys < 20% more speed, then nothing.
- **Power (VCD-backannotated, real workload):** the default-activity `report_power` upper bound overstates dynamic power by **3.9× / 2.7× / 2.8×** on the three core designs (largest on the pure datapath, smaller where activity-independent flip-flop clock power dominates). Leakage is identical under both methods — a clean cross-check. **Net: the bare PRG is sub-mW dynamic at carrier rates; the full TX+RX link is single-digit-mW.**

**Phase 1 generic-cell Yosys cross-check** reproduces the Phase 0 area numbers within **+15–34%** with a **constant per-family delta across widths**, independently validating both the area figures and the linear-scaling claim.

**Note on deployed configurations.** Real demonstrators wrap the bare core in transport, framing, and tag logic; measured full-bidirectional FPGA footprints range from ~900 LUT (Rolling Identity RoT) to ~2,400 LUT (Secure Link). See `formal_verification/` and the two-FPGA demo suite for per-configuration synth reports.

**What is and isn't shown here.** Hardware-validated: deterministic synchronization, keystream generation, and rolling integrity tags between two devices on real silicon. ASIC power characterized through Phase 2/3 SKY130HD post-route sign-off (2026-05-30): bare `dad_core` draws **~640 µW at 13.56 MHz** (4.72 mW @ 100 MHz, VCD-backannotated from a real gate-level workload) with **14.7 nW leakage** — **sub-mW dynamic / nW leakage** for the bare core. *Not* shown on this FPGA suite: radiation tolerance (architectural property; beam test pending), and cryptographic-strength against cryptanalysis (DAD is a lightweight, non-vetted construction; passing NIST SP 800-22 is not a security proof — independent cryptanalytic review is pursued separately).

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

**Two-FPGA demonstration suite — 6 of 6 tests silicon-validated (completed 2026-05-30):**

| # | Test | Claim shown on silicon | Hardware result |
|---|------|------------------------|-----------------|
| 01 | **Secure Link** | cross-device keystream sync + nonce-seeded stream cipher | bidirectional link + eavesdrop + wrong-key reject |
| 02 | **Freq-Hop / Anti-Jam** | both ends derive the same hop sequence from the seed | master/slave hop in lockstep, **59/59 dwells (100%)** |
| 03 | **IFF / Mutual Auth** | paired devices prove a shared secret; non-paired cannot | **all AUTH PASS** paired; **33 FAIL / 0 PASS** wrong-secret |
| 04 | **Line-Rate Integrity** | rolling-MAC tamper-evidence at one word per cycle | **8 clean PASS lines, fail = 0** |
| 05 | **Rolling Identity (RoT)** | continuously rotating per-device token | verifier **all-PASS**; observer (secret off by 1 bit) **all-FAIL**, captured simultaneously |
| 06 | **Clock / Phase Sync** | lockstep as a distributed time/phase reference | shared clock → `off=000000` cycle-exact; free-run → offset drifts **~0.1–0.6 ppm** |

Hardware: Tang Nano 9K (Gowin GW1N-9; Tests 01–04 TX side, since retired IO-dead), Tang Primer 20K (GW2A-18C), 2× Tang Primer 25K (GW5A-25A / MG121). The digital synchronization / keystream / identity-tag layer works deterministically across independent silicon devices. **Test 06 explicitly demonstrates the independent-crystal drift limit** — the honest boundary of clock-only sync.

**ASIC characterization — open-source PDK, EDA sign-off (no tapeout):**
- **Phase 0** area-optimized synthesis: ~30 designs characterized; 2,828 GE bare `dad_core` baseline; linear width-scaling at ~22.3 GE/bit across W=128 / 256 / 512 / 1024 (per-bit variance 1.8%).
- **Phase 1** generic-cell Yosys cross-check: reproduces Phase 0 numbers within +15–34% with constant per-family delta — independently validates the area figures and the linear-scaling claim.
- **Phase 2/3** full place-and-route sign-off (2026-05-30): 5 designs through complete OpenLane flow with **DRC-clean / LVS-clean GDSII**; no setup/hold violations at the typical corner; VCD-backannotated dynamic power.
- **RTL equivalence:** all 13 Drift-Flex width / temporal-extension variants verified bit-exact to a native wide-W reference via iverilog testbenches (1,000 virtual steps each) — closes PPA 63/929,897 Claim 2 ("global bitwise diffusion") obligation at RTL.

**Statistical testing — SP 800-22:** results are **in-house statistical testing of the conditioned output** (12 of 15 families via a public library + custom control-validated implementations for the rest; all pass). SP 800-22 is a statistical test suite, **not** a certification.

**Out of scope of this work:**
- Cryptanalytic strength against differential / linear / algebraic cryptanalysis — pursued separately (DAD is a lightweight non-vetted construction; passing NIST SP 800-22 is not a security proof).
- **SP 800-90B** entropy-source validation (assesses the physical source; the Drift recurrence is a conditioning component that pairs with a standard hardware noise source) and any **FIPS 140-3 / CAVP** module validation — handled at module integration.
- Fabricated-silicon ASIC results — no tapeout; SKY130 sign-off is EDA characterization, not a measured die.
- Radiation tolerance — architectural property; beam test pending.
- RF performance / over-the-air range / measured jam-resistance — the FPGAs are a functional vehicle; no radio in this work.

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
- **US 63/929,897:** Elastic State Extension of Arithmetic Entropy Sources via Temporal Carry Propagation (Drift-Flex)

For commercial licensing (RTL IP, FPGA Bitstreams, or Source Code), please contact:

**Drift Systems Inc.** 📧 **<licensing@driftsystems.io>** 🌐 **[driftsystems.io](https://driftsystems.io)**

---

*Copyright © 2025 Drift Systems Inc. All Rights Reserved.*
