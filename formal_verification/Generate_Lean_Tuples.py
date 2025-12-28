#!/usr/bin/env python3
"""
Generate Lean code for viable tuple verification.

This creates the complete list of viable tuples and generates
Lean theorem statements for each one.
"""

import itertools

def cycle_rhs_python(v_list):
    """Calculate RHS of cycle equation (for verification)."""
    k = len(v_list)
    rhs = 0
    cumulative_v = 0
    for i in range(k):
        power_of_3 = k - 1 - i
        power_of_2 = cumulative_v
        term = (3 ** power_of_3) * (2 ** power_of_2)
        rhs += term
        cumulative_v += v_list[i]
    return rhs

def cycle_lhs_python(v_list):
    """Calculate LHS coefficient."""
    k = len(v_list)
    V = sum(v_list)
    return (2 ** V) - (3 ** k)

def is_viable(v_list):
    """Check if v-tuple is viable (LHS > 0)."""
    return cycle_lhs_python(v_list) > 0

def find_viable_window(v_strong, max_k=20):
    """Find max k where viability holds."""
    for k in range(1, max_k + 1):
        # Best case: all other steps are v=1
        m = k - 1
        V = v_strong + m
        if not ((2 ** V) > (3 ** k)):
            return k - 1
    return max_k

def generate_all_tuples(k, v_strong):
    """Generate all v-tuples of length k containing v_strong."""
    tuples = set()
    
    # Number of v_strong occurrences
    for num_strong in range(1, k + 1):
        remaining = k - num_strong
        
        # Fill remaining with 1s and 2s
        for num_ones in range(remaining + 1):
            num_twos = remaining - num_ones
            
            base = [v_strong] * num_strong + [1] * num_ones + [2] * num_twos
            
            # All permutations
            for perm in set(itertools.permutations(base)):
                tuples.add(perm)
    
    return sorted(list(tuples))

def generate_lean_list(v_strong, max_k):
    """Generate Lean list definition for viable tuples."""
    all_tuples = []
    
    for k in range(2, max_k + 1):
        tuples = generate_all_tuples(k, v_strong)
        # Filter to viable only
        viable = [t for t in tuples if is_viable(list(t))]
        all_tuples.extend(viable)
    
    # Generate Lean syntax
    lean_entries = []
    for t in all_tuples:
        lean_entries.append(f"  [{', '.join(map(str, t))}]")
    
    return f"def viable_v{v_strong} : List (List Nat) := [\n" + ",\n".join(lean_entries) + "\n]"

def generate_lean_theorem(v_tuple, theorem_name):
    """Generate a Lean theorem for a specific v-tuple."""
    lhs = cycle_lhs_python(v_tuple)
    rhs = cycle_rhs_python(v_tuple)
    
    v_str = str(list(v_tuple))
    
    theorem = f"""
theorem {theorem_name} :
    let v := {v_str}
    let lhs := cycle_lhs v
    let rhs := cycle_rhs v
    lhs = {lhs} ∧ rhs = {rhs} ∧ ∀ n : Int, n > 1 → lhs * n ≠ rhs := by
  intro v lhs rhs
  have hL : lhs = {lhs} := by norm_num [lhs, cycle_lhs]
  have hR : rhs = {rhs} := by native_decide
  refine ⟨hL, hR, ?_⟩
  intro n hn
  rw [hL, hR]
  intro hEq
  have : ({lhs} : Int) * n = {rhs} := hEq
  have : n >= 2 := by linarith
  nlinarith
"""
    return theorem

def generate_trapped_tuples(max_k=10):
    """Generate all trapped set tuples (v ∈ {1,2})."""
    all_tuples = []
    
    for k in range(2, max_k + 1):
        for num_twos in range(k + 1):
            num_ones = k - num_twos
            base = [1] * num_ones + [2] * num_twos
            
            for perm in set(itertools.permutations(base)):
                if is_viable(list(perm)):
                    all_tuples.append(perm)
    
    return sorted(list(set(all_tuples)))

# ============================================================================
# MAIN GENERATION
# ============================================================================

if __name__ == "__main__":
    print("="*70)
    print("LEAN CODE GENERATOR FOR VIABLE TUPLES")
    print("="*70)
    
    # Generate for each v_strong
    for v_strong in [3, 4, 5]:
        max_k = find_viable_window(v_strong)
        print(f"\nv_strong = {v_strong}, max viable k = {max_k}")
        
        lean_list = generate_lean_list(v_strong, max_k)
        
        print(f"\n-- Generated {len(lean_list.split(','))} tuples")
        print("\n" + lean_list)
    
    print("\n" + "="*70)
    print("TRAPPED SET (v ∈ {1,2})")
    print("="*70)
    
    trapped = generate_trapped_tuples(max_k=8)
    print(f"\nTotal trapped tuples (k ≤ 8): {len(trapped)}")
    
    lean_entries = []
    for t in trapped[:20]:  # Show first 20
        lean_entries.append(f"  [{', '.join(map(str, t))}]")
    
    print("\ndef viable_trapped : List (List Nat) := [")
    print(",\n".join(lean_entries))
    print("  -- ... (continues)")
    print("]")
    
    # Generate sample theorems
    print("\n" + "="*70)
    print("SAMPLE LEAN THEOREMS")
    print("="*70)
    
    sample_tuples = [
        [1, 3],
        [3, 1],
        [1, 1, 3],
        [1, 4],
        [2, 2, 2]
    ]
    
    for i, v in enumerate(sample_tuples):
        if is_viable(v):
            v_str = "_".join(map(str, v))
            theorem_name = f"case_v{v_str}_no_solution"
            print(generate_lean_theorem(v, theorem_name))
    
    print("\n" + "="*70)
    print("STATISTICS")
    print("="*70)
    
    for v_strong in range(3, 11):
        max_k = find_viable_window(v_strong)
        total = 0
        for k in range(2, max_k + 1):
            tuples = generate_all_tuples(k, v_strong)
            viable = [t for t in tuples if is_viable(list(t))]
            total += len(viable)
        print(f"v_strong={v_strong:2d}: max_k={max_k:2d}, total viable tuples: {total:5d}")
