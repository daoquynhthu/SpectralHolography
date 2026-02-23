
import numpy as np
import matplotlib.pyplot as plt
import math

def simulate_original_leak():
    print("\n=== 1. Original Richardson Logic (The 'Singularity Leak') ===")
    key = 0.0
    # Simulate scanning near the key
    x_vals = np.linspace(-0.0000001, 0.0000001, 20)
    
    print(f"{'x (Offset)':<20} | {'Value':<25} | {'Status'}")
    print("-" * 60)
    
    for x in x_vals:
        # Original logic: Huge * Tan(Sharp * x)
        # Note: In real code, x is difference from key.
        # We use a large coefficient (1e50) and high frequency (1e9) as in the rust code.
        try:
            term = 1e50 * math.tan(1e9 * x)
            val = x + term
            
            status = "Normal"
            if abs(val) > 1e20:
                status = "HUGE (LEAK!)"
            if math.isinf(val):
                status = "INF (LEAK!)"
            if math.isnan(val):
                status = "NaN (LEAK!)"
                
            print(f"{x:<20.8e} | {val:<25.2e} | {status}")
        except OverflowError:
             print(f"{x:<20.8e} | {'OVERFLOW':<25} | INF (LEAK!)")

    print("\n[!] ATTACKER CONCLUSION: The key is exactly where the value explodes.")


def simulate_spectral_holography():
    print("\n=== 2. Isotropic Spectral Holography (Proposed) ===")
    print("Generating 1000-wave spectral landscape...")
    
    # Parameters
    N_WAVES = 1000
    KEY = 0.123456789
    TARGET_P = 42.0
    
    np.random.seed(42) # For reproducibility
    
    # Generate random waves for A(x)
    # k_a: frequencies, phi_a: phases
    k_a = np.random.uniform(1.0, 10000.0, N_WAVES)
    phi_a = np.random.uniform(0, 2*np.pi, N_WAVES)
    
    # Generate random waves for B(x) part 1 (Noise)
    k_b = np.random.uniform(1.0, 10000.0, N_WAVES)
    phi_b = np.random.uniform(0, 2*np.pi, N_WAVES)
    
    def eval_A(x):
        # A(x) = sum(cos(k*x + phi))
        # Vectorized evaluation for a single x scalar
        phases = k_a * x + phi_a
        return np.sum(np.cos(phases))
        
    def eval_B_raw(x):
        # B_raw(x) = sum(cos(k*x + phi))
        phases = k_b * x + phi_b
        return np.sum(np.cos(phases))

    # Calculate offset to ensure exact recovery at KEY
    # We want -B(KEY) / A(KEY) = P  =>  B(KEY) = -P * A(KEY)
    # Our B(x) = B_raw(x) + C
    # So B_raw(KEY) + C = -P * A(KEY)
    # C = -P * A(KEY) - B_raw(KEY)
    
    val_A_key = eval_A(KEY)
    val_B_raw_key = eval_B_raw(KEY)
    
    C_offset = -TARGET_P * val_A_key - val_B_raw_key
    
    def eval_B(x):
        return eval_B_raw(x) + C_offset

    def recover_P(x):
        a = eval_A(x)
        b = eval_B(x)
        if abs(a) < 1e-9: return float('nan') # Avoid division by zero (rare)
        return -b / a

    print(f"Key: {KEY}")
    print(f"Target P: {TARGET_P}")
    print(f"A(Key): {val_A_key:.4f}")
    print(f"B(Key): {eval_B(KEY):.4f} (Should be {-TARGET_P * val_A_key:.4f})")
    
    recovered_at_key = recover_P(KEY)
    print(f"Recovered P at Key: {recovered_at_key:.10f}")
    assert abs(recovered_at_key - TARGET_P) < 1e-6
    
    print("\n--- Scanning near Key (Attacker View) ---")
    offsets = np.linspace(-0.0001, 0.0001, 10)
    
    print(f"{'x (Offset from Key)':<25} | {'Recovered P':<20} | {'Gradient (approx)'}")
    print("-" * 75)
    
    prev_val = None
    
    for offset in offsets:
        x = KEY + offset
        val = recover_P(x)
        
        grad = "N/A"
        if prev_val is not None:
            # Simple finite difference
            diff = val - prev_val
            grad = f"{diff:.2e}"
            
        print(f"{offset:<25.8f} | {val:<20.4f} | {grad}")
        prev_val = val
        
    print("\n[!] ATTACKER CONCLUSION:")
    print("    1. The recovered value fluctuates wildly near the key.")
    print("    2. At offset 0.0, the value is exactly 42.0, but...")
    print("    3. At offset 0.00002, it might be -5000.0 or 300.0.")
    print("    4. There is no 'singularity' or 'infinity' marking the spot.")
    print("    5. Gradient is chaotic, changing sign and magnitude randomly.")

if __name__ == "__main__":
    simulate_original_leak()
    simulate_spectral_holography()
