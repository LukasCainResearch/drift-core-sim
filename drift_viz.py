# DRIFT SYSTEMS INC. - CONFIDENTIAL & PROPRIETARY
# 
# This file is part of the Drift Core™ IP Portfolio.
# Copyright (c) 2025 Drift Systems Inc. All Rights Reserved.
# 
# Usage is subject to the license terms found in the LICENSE file.
# Unauthorized copying, distribution, or synthesis is strictly prohibited.
import numpy as np
from PIL import Image
import time

class DriftEngine:
    def __init__(self, seed, q=3, d=1):
        self.state = int(seed) | 1 # Ensure odd
        self.q = q
        self.d = d

    def generate_stream(self, count, mode='whitened'):
        """
        Generates a stream of bytes.
        """
        data = bytearray(count)
        
        # We loop through byte by byte. 
        # Python is slower than C++, but fine for image generation (512x512).
        s = self.state
        q = self.q
        d = self.d
        
        for i in range(count):
            # 1. The Drift Step (Arithmetic Dynamics)
            # S_next = (3S + 1) / 2
            s = (s * q + d) >> 1
            
            if mode == 'whitened':
                # HARDWARE SIMULATION: XORSHIFT
                # We take the bottom 64 bits to simulate the register
                x = s & 0xFFFFFFFFFFFFFFFF
                x ^= (x << 13) & 0xFFFFFFFFFFFFFFFF
                x ^= (x >> 7) 
                x ^= (x << 17) & 0xFFFFFFFFFFFFFFFF
                data[i] = x & 0xFF
            
            elif mode == 'texture':
                # RAW DRIFT: Good for procedural generation
                # We take the "middle" bits to show the 2-adic structure
                # This reveals the "Cloud" patterns hidden in the math
                data[i] = (s >> 16) & 0xFF
                
        self.state = s
        return data

def save_image(filename, data, width, height):
    # Convert byte array to numpy image
    img_data = np.frombuffer(data, dtype=np.uint8).reshape((height, width))
    img = Image.fromarray(img_data, mode='L') # L = Grayscale
    img.save(filename)
    print(f"[+] Saved: {filename}")

def main():
    WIDTH = 512
    HEIGHT = 512
    TOTAL_PIXELS = WIDTH * HEIGHT
    
    print(f"--- DRIFT VISUALIZER ---")
    print(f"Generating {WIDTH}x{HEIGHT} bitmaps...")

    # 1. GENERATE "CRYPTO" NOISE (For Security/Watermarking)
    # This should look like random TV static.
    print("\n1. Generating Whitened Entropy (Security)...")
    start = time.time()
    crypto_engine = DriftEngine(seed=123456789, q=3, d=1)
    crypto_data = crypto_engine.generate_stream(TOTAL_PIXELS, mode='whitened')
    save_image("drift_crypto_static.png", crypto_data, WIDTH, HEIGHT)
    print(f"   Time: {time.time() - start:.2f}s")

    # 2. GENERATE "TEXTURE" NOISE (For Gaming)
    # This should reveal the underlying structure of the Drift.
    print("\n2. Generating Raw Drift (Terrain/Clouds)...")
    start = time.time()
    texture_engine = DriftEngine(seed=123456789, q=3, d=1) # Same seed!
    texture_data = texture_engine.generate_stream(TOTAL_PIXELS, mode='texture')
    save_image("drift_texture_map.png", texture_data, WIDTH, HEIGHT)
    print(f"   Time: {time.time() - start:.2f}s")
    
    print("\n[Done] Check the folder for .png files.")

if __name__ == "__main__":
    main()
