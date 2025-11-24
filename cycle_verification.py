import itertools
import math
from multiprocessing import Pool
import time

# --- CONFIGURATION ---
D_VALUE = 1        # The 'd' in 3n+d
MAX_K = 12         # Max cycle length to search
NUM_PROCESSES = 8  # Adjust based on your CPU cores

def get_valuation_2(n):
    """Returns the number of times n is divisible by 2."""
    if n == 0: return float('inf')
    v2 = 0
    while n > 0 and n % 2 == 0:
        n //= 2
        v2 += 1
    return v2

def calculate_C(v_tuple):
    """Calculates the cycle coefficient C."""
    k = len(v_tuple)
    C_sum = 0
    sum_v_j = 0
    for i in range(1, k + 1):
        term_3 = 3**(k - i)
        term_2 = 2**sum_v_j
        C_sum += term_3 * term_2
        sum_v_j += v_tuple[i-1]
    return C_sum

def verify_cycle(n_start, v_tuple, d):
    """Verifies if a candidate n1 actually forms a cycle."""
    n = n_start
    path = [n_start]
    
    for v_expected in v_tuple:
        n_next_full = 3 * n + d
        if n_next_full == 0: return False
        
        v_actual = get_valuation_2(abs(n_next_full))
        if v_actual != v_expected: return False # Modular constraint failure
        
        n = n_next_full // (2**v_actual)
        
        if n == n_start: return True
        if n in path: return False # Sub-cycle
        path.append(n)
    
    return n == n_start

def get_partitions(V, k):
    """Generates integer partitions of V into k parts."""
    if k == 1:
        if V >= 1: yield (V,)
        return
    for i in range(1, V - k + 2):
        for p in get_partitions(V - i, k - 1):
            yield (i,) + p

def solve_for_k(k):
    """Worker function to solve for a specific cycle length k."""
    results = []
    
    # Heuristic bounds for V (Total Valuation)
    # For d=1 positive cycles, 2^V > 3^k is required.
    # We verify a wide range to catch negative/hybrid cycles too.
    min_V = math.ceil(k * 1.58) # log2(3) approx
    max_V = k * 5 # Reasonable search depth
    
    print(f"   [Worker] Checking k={k} (V range: {min_V}-{max_V})...")
    
    for V in range(min_V, max_V + 1):
        A = 2**V - 3**k
        if A == 0: continue
        
        # 1. Generate Partitions
        partitions = get_partitions(V, k)
        
        for p in partitions:
            # 2. Generate Unique Permutations
            # set() handles duplicates automatically
            perms = set(itertools.permutations(p))
            
            for v_tuple in perms:
                # 3. Solve Equation
                C = calculate_C(v_tuple)
                B = D_VALUE * C
                
                if B % A == 0:
                    n1 = B // A
                    # 4. Verify Solution
                    if n1 != 0 and verify_cycle(n1, v_tuple, D_VALUE):
                        results.append((n1, v_tuple))
                        
    return results

def main():
    print(f"=== 3n + {D_VALUE} Cycle Solver (Python Optimized) ===")
    print(f"Searching for cycles up to length k={MAX_K}...")
    start_time = time.time()
    
    # Use multiprocessing to check different k values in parallel
    with Pool(NUM_PROCESSES) as pool:
        # Create a list of k values to check
        k_values = range(1, MAX_K + 1)
        all_results = pool.map(solve_for_k, k_values)
    
    print("\n=== FINAL RESULTS ===")
    found_any = False
    for k_res in all_results:
        for n1, v_tuple in k_res:
            found_any = True
            print(f"FOUND CYCLE: n0 = {n1}")
            print(f"  Length k={len(v_tuple)}, V={sum(v_tuple)}")
            print(f"  Structure: {v_tuple}")
            print("-" * 30)
            
    if not found_any:
        print(f"No cycles found for d={D_VALUE} up to k={MAX_K}.")
        
    print(f"\nSearch completed in {time.time() - start_time:.2f} seconds.")

if __name__ == '__main__':
    main()
