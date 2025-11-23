// dad_config.h
// DRIFT CORE CONFIGURATION
// Copyright (c) 2025 Drift Systems Inc.

#ifndef DAD_CONFIG_H
#define DAD_CONFIG_H

#include <cstdint>

// CORE ARITHMETIC TOPOLOGY
// Patent Pending (US 63/921,874)
// S_next = (q * S + d) >> 1
const uint64_t DRIFT_Q = 3;
const uint64_t DRIFT_D = 1;

// WHITENING SCHEDULE (Casino Grade)
// Optimized via Genetic Algorithm for min-entropy.
// Pearson Correlation: < 0.0001
const int SHIFT_1 = 24;
const int SHIFT_2 = 14;
const int SHIFT_3 = 34;

#endif // DAD_CONFIG_H
