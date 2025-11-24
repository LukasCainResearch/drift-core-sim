/*
 * DRIFT SYSTEMS INC. - CONFIDENTIAL & PROPRIETARY
 * 
 * This file is part of the Drift Core™ IP Portfolio.
 * Copyright (c) 2025 Drift Systems Inc. All Rights Reserved.
 * 
 * Usage is subject to the license terms found in the LICENSE file.
 * Unauthorized copying, distribution, or synthesis is strictly prohibited.
 */
// dad_tool.cpp
// High-Performance Drift Stream Generator
// Usage: ./dad_tool [bytes] > output.bin

#include <iostream>
#include <vector>
#include <chrono>
#include "dad_config.h"

class DriftCore {
private:
    unsigned __int128 state; 

public:
    DriftCore(uint64_t seed) {
        // SplitMix64 Seed Expansion to ensure avalanche compliance
        uint64_t z = (seed + 0x9e3779b97f4a7c15ULL);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        uint64_t mixed_seed = z ^ (z >> 31);
        state = (unsigned __int128)mixed_seed | 1; 
    }

    inline uint64_t next() {
        // 1. DRIFT: Affine Expansion
        state = (state * DRIFT_Q + DRIFT_D) >> 1;

        // 2. FOLD: Dimensionality Reduction
        uint64_t output = (uint64_t)(state) ^ (uint64_t)(state >> 64);

        // 3. WHITEN: Bitwise Permutation
        output ^= (output >> SHIFT_1);
        output ^= (output << SHIFT_2);
        output ^= (output >> SHIFT_3);

        return output;
    }
};

int main(int argc, char* argv[]) {
    std::ios_base::sync_with_stdio(false);
    std::cin.tie(NULL);

    size_t total_bytes = 1024 * 1024 * 10; // Default 10MB
    if (argc > 1) {
        total_bytes = std::stoull(argv[1]);
    }

    size_t bytes_per_batch = 65536; 
    size_t batches = total_bytes / bytes_per_batch;
    size_t remainder = total_bytes % bytes_per_batch;

    // Auto-seed from clock
    auto now = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    DriftCore core(now);

    std::vector<uint64_t> buffer(bytes_per_batch / 8);

    // Batch Output
    for (size_t i = 0; i < batches; i++) {
        for (size_t j = 0; j < buffer.size(); j++) {
            buffer[j] = core.next();
        }
        std::cout.write(reinterpret_cast<const char*>(buffer.data()), bytes_per_batch);
    }

    // Remainder Output
    for (size_t i = 0; i < remainder; i++) {
        uint64_t val = core.next();
        std::cout.write(reinterpret_cast<const char*>(&val), 1);
    }

    return 0;
}
