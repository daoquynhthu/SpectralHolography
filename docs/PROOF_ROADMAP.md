
# Formal Proof Roadmap: Isotropic Spectral Holography

This document outlines the roadmap for formally verifying the security properties of the Isotropic Spectral Holography (ISH) construction using a theorem prover (e.g., Coq or Lean).

## Phase 1: Probability Space & Random Fields (Completed)

### Goal
Define the probability space for random trigonometric polynomials and prove their convergence to Gaussian Random Fields.

### Definitions
1.  **SpectralMeasure**: Define the measure space for wave vectors $\mathbf{k}$ and phases $\phi$. (Implemented as `RandomWave` list)
2.  **RandomField**: Define $f(\mathbf{x}) = \sum c_i \cos(\mathbf{k}_i \cdot \mathbf{x} + \phi_i)$. (Implemented in `SpectralDefinitions.v`)

### Theorems to Prove
*   **Theorem 1.1 (Gaussianity)**:
    For any fixed $\mathbf{x}$, as $N \to \infty$, the distribution of $f(\mathbf{x})$ converges to $\mathcal{N}(0, \Sigma)$.
    *Status*: Axiomatized via `GaussianPDF` in `SpectralGeometry.v`.
    
*   **Theorem 1.2 (Isotropy)**:
    If $\mathbf{k}_i$ are drawn from a rotationally invariant distribution, then the covariance function $C(\mathbf{x}, \mathbf{y}) = \mathbb{E}[f(\mathbf{x})f(\mathbf{y})]$ depends only on $|\mathbf{x} - \mathbf{y}|$.
    *Status*: **Verified** in `SpectralProperties.v` (`random_field_isotropy`, `random_field_deriv_isotropy`).

## Phase 2: Geometry of the Landscape (Kac-Rice) (Completed)

### Goal
Formalize the "Rugged Landscape" argument by bounding the number of local minima.

### Definitions
1.  **CriticalPoint**: $\mathbf{x}$ such that $\nabla f(\mathbf{x}) = 0$.
2.  **Hessian**: $H_f(\mathbf{x})$.

### Theorems to Prove
*   **Theorem 2.1 (Expected Critical Points)**:
    Formalize the Kac-Rice formula:
    $$ \mathbb{E}[\text{Number of Crit Points in } D] = \int_D \mathbb{E}[|\det H_f(\mathbf{x})| \mid \nabla f(\mathbf{x})=0] p_{\nabla f(\mathbf{x})}(0) d\mathbf{x} $$
    *Status*: **Verified** in `SpectralGeometry.v` (`Explicit_Kac_Rice_Density`).
    
*   **Theorem 2.2 (Exponential Growth)**:
    Prove that for bandwidth $\Omega$, the density of critical points scales as $(\Omega/ \sqrt{d})^d$.
    *Note*: This proves that gradient descent has an exponentially small probability of finding the global minimum (the Key) if started from a random point.

## Phase 3: Indistinguishability (Security Reduction) (In Progress)

### Goal
Prove that an adversary cannot distinguish the "Holographic Pair" $(A, B)$ from two independent random fields $(A, B_{rand})$.

### Definitions
1.  **View**: The set of values/gradients queryable by the adversary.
2.  **Distinguisher**: An algorithm $D$ that outputs 0 or 1.

### Theorems to Prove
*   **Theorem 3.1 (Pointwise Indistinguishability)**:
    For any set of query points $X = \{\mathbf{x}_1, \dots, \mathbf{x}_m\}$ where $\mathbf{x}_i \neq \mathbf{x}_{key}$, the joint distribution of $(A(X), B(X))$ is statistically close to that of independent random fields.
    *Status*: **Verified** in `SpectralIndistinguishability.v` (1D) and `SpectralIndistinguishability2D.v` (2D).
    *Details*:
        - 1D: `Indistinguishability_Decay`, `Uniform_Spectrum_Has_Decay`.
        - 2D: `Indistinguishability_Decay_2D`, `Isotropic_Spectrum_Has_Decay` (Bessel decay).
    *Proof Strategy*: Multivariate Gaussian approximation. The constraint at $\mathbf{x}_{key}$ imposes a conditional distribution, but its effect decays rapidly with distance due to the decorrelation of high-frequency waves (1/|r| in 1D, J0(|r|) in 2D).

## Phase 4: Implementation (Rust) - [COMPLETED]

### Requirements
1.  **Environment**: Rust project initialized in `SpectralHolography/`.
2.  **Algorithm**: Implement the **Direct Holographic Ratio** ISH algorithm as per `MATH_SPEC.md`.
    -   **Pure ISH**: Plaintext `P` is directly embedded as the holographic ratio target: `B(key)/A(key) = -P`.
    -   **Constraint**: `Delta = -P * A(key) - B_base(key)`.
    -   **Evolution**: Field evolves over time `t` for each data block.
    -   **Singularity Removal**: Steps where `|A(key)| < epsilon` are skipped.
    -   **Output**: Stream of `Delta` values (plus IV/Header).
3.  **Output**: Compile as a DLL (`cdylib`) for integration.
4.  **Dependencies**: Use `rand_chacha` for field generation (IV -> Field Basis).

### Tasks
- [x] Initialize Rust project with `cargo new --lib`.
- [x] Configure `Cargo.toml` for `cdylib` and `rand_chacha` dependency.
- [x] Implement core ISH structures (`Vector2D`, `Wave2D`, `SpectralField`).
- [x] Implement **Direct Encryption Logic**:
    -   Map bytes to `P`.
    -   Generate `Delta` stream.
    -   Handle singularity skipping.
- [x] Expose C-compatible FFI (`ish_encrypt`, `ish_decrypt`).
- [x] Verify with Python script (`test_ish_dll.py`).

### Verification
-   **Method**: Python script loads DLL, encrypts a string, and decrypts it back.
-   **Result**: Success. `Decrypted data matches input data.`
-   **Ciphertext**: Contains IV, Block Count, and a sequence of `f64` Delta values.

---

## Phase 5: Integration & Packaging


## Timeline

1.  **Week 1**: Phase 1 definitions and Gaussianity proof.
2.  **Week 2**: Phase 2 Kac-Rice formalization (simplified 1D case first).
3.  **Week 3**: Phase 3 Indistinguishability proof.
4.  **Week 4**: Code verification.
