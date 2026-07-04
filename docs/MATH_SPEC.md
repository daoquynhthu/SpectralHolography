
# Mathematical Specification: Isotropic Spectral Holography (ISH)

## 1. Introduction

Isotropic Spectral Holography (ISH) is a cryptographic construction that hides information within the phase relationships of high-dimensional spectral landscapes. Unlike traditional encryption which relies on number-theoretic hardness (e.g., factorization), ISH relies on the computational intractability of finding the global optimum in a rugged, high-dimensional continuous landscape.

The current implementation upgrades the spectral domain to **3D Space** ($\mathbb{R}^3$) and introduces **Z1 Compression** for efficient storage.

## 2. Core Hardness Assumption

**Assumption (Global Optimization of Random Trigonometric Polynomials)**: 
Given two random trigonometric polynomials $A(\mathbf{x})$ and $B(\mathbf{x})$ constructed from $N$ independent frequency components in $\mathbb{R}^3$, finding a vector $\mathbf{x}_0 \in \mathbb{R}^3$ such that $B(\mathbf{x}_0) / A(\mathbf{x}_0) = -P$ (where $P$ is a target value) is computationally intractable for sufficiently large $N$, provided no auxiliary gradient information is leaked.

The hardness arises from the **Kac-Rice Theorem**, which states that the expected number of critical points (local minima/maxima) in such a random field grows exponentially with $N$.

$$ \mathbb{E}[\text{Crit}(f)] \sim C^N $$

For $N = 1000$, the number of local traps exceeds the computational capacity of any physical adversary, rendering gradient-based attacks ineffective.

## 3. Construction (3D)

### 3.1. Basis Generation

Let $\mathcal{K} = \{ (\mathbf{k}_i, \phi_i, c_i) \}_{i=1}^N$ be a set of spectral components, where:
*   $\mathbf{k}_i \in \mathbb{R}^3$ are wave vectors, sampled uniformly from an isotropic distribution (spherical shell).
*   $\phi_i \in [0, 2\pi)$ are phases, sampled uniformly.
*   $c_i \in \mathbb{R}$ are amplitudes, sampled such that $\sum c_i^2$ is normalized.

### 3.2. Surface Synthesis

We define the "Carrier Field" $A(\mathbf{x})$ as:
$$ A(\mathbf{x}) = \sum_{i=1}^N c_i \cos(\mathbf{k}_i \cdot \mathbf{x} + \phi_i) $$

We define the "Holographic Field" $B(\mathbf{x})$ similarly, but derived from a secret reference salt (making it statistically independent from A to an observer without the key).

### 3.3. Geometric Encoding (The "Delta" Method)

To encode a payload value $P$ at a secret location $\mathbf{x}_{key}$, we calculate a difference term $\Delta$:

We require:
$$ \frac{B(\mathbf{x}_{key}) + \Delta}{A(\mathbf{x}_{key})} = -P $$

Solving for $\Delta$:
$$ B(\mathbf{x}_{key}) + \Delta = -P \cdot A(\mathbf{x}_{key}) $$
$$ \Delta = -P \cdot A(\mathbf{x}_{key}) - B(\mathbf{x}_{key}) $$

The value $\Delta$ is the ciphertext. It looks like random noise because $A(\mathbf{x}_{key})$ and $B(\mathbf{x}_{key})$ are effectively random Gaussian variables.

### 3.4. Recovery Function

The recovered value field $R(\mathbf{x})$ is defined as:
$$ R(\mathbf{x}) = -\frac{B(\mathbf{x}) + \Delta}{A(\mathbf{x})} $$

At $\mathbf{x} = \mathbf{x}_{key}$, $R(\mathbf{x}_{key}) = P$.
Everywhere else, $R(\mathbf{x})$ behaves as the ratio of two independent Gaussian processes (Cauchy distribution), exhibiting heavy tails and extreme volatility.

## 4. Advanced Protocols

### 4.1. Chaotic Trajectory (Anti-Smoothness)
To prevent "Smoothness Attacks" where an attacker traces the gradient of $P$ across adjacent bytes, we do not use a contiguous path in space.
Instead, for every data chunk/byte, the sampling location $\mathbf{x}_{sample}$ jumps pseudo-randomly:

$$ \mathbf{x}_{sample} = \text{ChaCha20}(\text{Seed} = \text{Hash}(IV || \mathbf{x}_{key} || \text{Index})) $$

This ensures that adjacent bytes in the file are mapped to uncorrelated points in the 3D field, destroying any local smoothness.

### 4.2. Constant-Time Sampling (Side-Channel Protection)
To prevent timing attacks that could reveal information about the field values or the validity of a point:
1.  **Fixed Iterations**: The sampling loop always runs for exactly **12 iterations**, regardless of when a valid point is found.
2.  **Bitwise Selection**: The final coordinate and value are selected using bitwise logic (`subtle` crate) based on validity flags, avoiding secret-dependent branches.
3.  **Singularity Threshold**: Points where $|A(\mathbf{x})| < \epsilon$ are rejected to ensure numerical stability, but this rejection is done in constant time.

### 4.3. Z1 Compression Mode (Pure Geometric)
Standard ISH encodes 1 byte into one `f64` (8 bytes), resulting in 8x expansion.
**Z1 Mode** improves this to **2x expansion** (4 bytes per `f64`) by exploiting the precision of double-precision floating point format.

*   **Packing**: 4 bytes ($b_0, b_1, b_2, b_3$) are packed into a `u32`.
*   **Length Encoding**: The number of valid bytes (1-4) is encoded in the high bits.
*   **Precision Safety**: The 53-bit significand of IEEE 754 `f64` can losslessly represent integers up to $2^{53}$. We use a **50-bit mask** to whiten the data, ensuring the total integer value never exceeds precision limits.

$$ P_{target} \leftarrow \text{Pack}(b_0..b_3) \oplus \text{Mask}_{50bit} $$
$$ \Delta = -P_{target} \cdot A - B $$

Recovery involves reversing the formula and rounding to the nearest integer.

## 5. Security Proof Sketch

We claim indistinguishability from random noise:
$$ (A(\mathbf{x}), B(\mathbf{x})) \approx_{comp} (\mathcal{N}(0, \sigma_A), \mathcal{N}(0, \sigma_B)) $$
for all $\mathbf{x} \neq \mathbf{x}_{key}$.

By the Central Limit Theorem (Berry-Esseen bound), the divergence from Gaussianity decreases as $1/\sqrt{N}$. With $N=1000$ (default), the statistical deviation is negligible.
The 3D field structure adds an additional layer of complexity ($N^3$ scaling in phase space volume) compared to 2D.
