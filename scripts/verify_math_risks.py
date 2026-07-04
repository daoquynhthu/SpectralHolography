import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import cauchy
import time

def generate_field(n_waves=1000, seed=None):
    """
    Simulates the Rust generate_field function.
    Sum of N cosines with random phase and direction.
    """
    if seed is not None:
        np.random.seed(seed)
        
    # Parameters matching Rust impl
    K_MAGNITUDE = 10.0
    AMPLITUDE = 1.0
    
    phases = np.random.uniform(0, 2*np.pi, n_waves)
    thetas = np.random.uniform(0, 2*np.pi, n_waves)
    
    k_x = K_MAGNITUDE * np.cos(thetas)
    k_y = K_MAGNITUDE * np.sin(thetas)
    
    return k_x, k_y, phases, AMPLITUDE

def eval_field(x, y, k_x, k_y, phases, amp):
    """
    Evaluates field at (x, y).
    x, y can be scalars or arrays.
    """
    # broadcasting: (N,) vs (M,) -> (N, M) if needed, but here we sum over N
    # Let's assume x, y are scalars or same-shape arrays
    
    # argument = k_x * x + k_y * y + phase
    # If x is array (H, W), we need to align dimensions.
    
    if np.isscalar(x):
        arg = k_x * x + k_y * y + phases
        return np.sum(amp * np.cos(arg))
    elif x.ndim == 1:
        # x, y are 1D arrays
        # arg: (N, L)
        arg = k_x[:, None] * x[None, :] + k_y[:, None] * y[None, :] + phases[:, None]
        return np.sum(amp * np.cos(arg), axis=0)
    else:
        # x, y are 2D arrays. k_x is 1D array.
        # We want result of shape x.shape
        # term: (N, H, W)
        arg = k_x[:, None, None] * x[None, :, :] + k_y[:, None, None] * y[None, :, :] + phases[:, None, None]
        return np.sum(amp * np.cos(arg), axis=0)

def simulate_singularity_risk(n_trials=100000):
    print(f"[*] Simulating {n_trials} points to check for singularities (A(x) ~ 0)...")
    
    # Generate field A
    k_x, k_y, phases, amp = generate_field(1000, seed=42)
    
    # Random points in [-1000, 1000]
    xs = np.random.uniform(-1000, 1000, n_trials)
    ys = np.random.uniform(-1000, 1000, n_trials)
    
    # Evaluate A
    # Optimized batch eval
    # Split into chunks to avoid memory issues
    chunk_size = 1000
    vals = []
    
    for i in range(0, n_trials, chunk_size):
        end = min(i + chunk_size, n_trials)
        x_batch = xs[i:end]
        y_batch = ys[i:end]
        
        # Manual broadcasting for 1D batch
        arg = k_x[:, None] * x_batch[None, :] + k_y[:, None] * y_batch[None, :] + phases[:, None]
        batch_vals = np.sum(amp * np.cos(arg), axis=0)
        vals.extend(batch_vals)
        
    vals = np.array(vals)
    
    # Check for near-zero values
    thresholds = [1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6]
    print("\n--- Singularity Analysis ---")
    print(f"Total points: {n_trials}")
    print(f"Mean(abs(A)): {np.mean(np.abs(vals)):.4f}")
    print(f"Std(A): {np.std(vals):.4f}")
    
    min_val = np.min(np.abs(vals))
    print(f"Closest to zero: {min_val:.8e}")
    
    for th in thresholds:
        count = np.sum(np.abs(vals) < th)
        prob = count / n_trials
        print(f"|A(x)| < {th}: {count} points ({prob*100:.4f}%)")
        
    return vals

def simulate_reconstruction_stability(min_a_val=1e-6):
    print(f"\n[*] Simulating Reconstruction Stability with |A(x)| ~ {min_a_val}...")
    
    # Case: A(x) is very small.
    val_a = min_a_val
    val_b = 10.0 # Random value
    p_target = 128.0 # Mid-range byte
    
    # Encrypt
    # delta = -p * a - b
    delta = -p_target * val_a - val_b
    
    print(f"Val A: {val_a}")
    print(f"Val B: {val_b}")
    print(f"Target P: {p_target}")
    print(f"Delta: {delta}")
    
    # Decrypt with floating point noise
    # Simulate f64 precision (approx 15-17 decimal digits)
    # But let's add some tiny noise representing calculation differences
    epsilon = 1e-15 
    val_a_noisy = val_a + epsilon
    val_b_noisy = val_b + epsilon
    delta_noisy = delta # Transmitted perfectly usually, but let's assume...
    
    # P = -(B + Delta) / A
    p_recovered_raw = -(val_b_noisy + delta_noisy) / val_a_noisy
    p_recovered = int(round(p_recovered_raw))
    p_recovered = max(0, min(255, p_recovered))
    
    print(f"Recovered P (Raw): {p_recovered_raw:.10f}")
    print(f"Recovered P (Int): {p_recovered}")
    print(f"Error: {abs(p_recovered_raw - p_target):.10e}")
    
    if p_recovered != int(p_target):
        print("FAIL: Reconstruction failed due to instability!")
    else:
        print("PASS: Reconstruction successful despite small A.")

def visualize_landscape():
    print("\n[*] Generating Landscape Visualization (1D Slice)...")
    k_x, k_y, phases, amp = generate_field(1000, seed=123)
    
    x = np.linspace(-10, 10, 1000)
    y = np.zeros_like(x)
    
    val_a = eval_field(x, y, k_x, k_y, phases, amp)
    
    # Plot A(x)
    # We want to see how "wiggly" it is
    # Expected zero crossings
    zero_crossings = np.where(np.diff(np.sign(val_a)))[0]
    print(f"Zero crossings in range [-10, 10]: {len(zero_crossings)}")
    
    # Check distribution of A
    # Should be Gaussian
    plt.figure(figsize=(10, 6))
    plt.hist(val_a, bins=50, density=True, alpha=0.6, color='b', label='Empirical A(x)')
    
    # Theoretical Gaussian
    sigma = np.sqrt(1000 * 0.5 * 1.0**2) # N * E[cos^2] * amp^2 = 1000 * 0.5 * 1
    # Actually, var = sum(amp^2/2) = 1000 * 0.5 = 500. sigma = sqrt(500) approx 22.36
    
    xmin, xmax = plt.xlim()
    x_pdf = np.linspace(xmin, xmax, 100)
    p_pdf = (1/(sigma * np.sqrt(2 * np.pi))) * np.exp(-0.5 * (x_pdf / sigma)**2)
    plt.plot(x_pdf, p_pdf, 'r', linewidth=2, label='Theoretical Gaussian')
    
    plt.title('Distribution of Field Value A(x)')
    plt.legend()
    plt.grid(True)
    plt.savefig('field_distribution.png')
    print("Saved field_distribution.png")

if __name__ == "__main__":
    vals = simulate_singularity_risk()
    simulate_reconstruction_stability(1e-4)
    simulate_reconstruction_stability(1e-8)
    visualize_landscape()
