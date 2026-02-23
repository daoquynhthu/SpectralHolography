
# Formal Proof Roadmap: Isotropic Spectral Holography

This document outlines the roadmap for formally verifying the security properties of the Isotropic Spectral Holography (ISH) construction using a theorem prover (e.g., Coq or Lean).

## Phase 1: Probability Space & Random Fields

### Goal
Define the probability space for random trigonometric polynomials and prove their convergence to Gaussian Random Fields.

### Definitions
1.  **SpectralMeasure**: Define the measure space for wave vectors $\mathbf{k}$ and phases $\phi$.
2.  **RandomField**: Define $f(\mathbf{x}) = \sum c_i \cos(\mathbf{k}_i \cdot \mathbf{x} + \phi_i)$.

### Theorems to Prove
*   **Theorem 1.1 (Gaussianity)**:
    For any fixed $\mathbf{x}$, as $N \to \infty$, the distribution of $f(\mathbf{x})$ converges to $\mathcal{N}(0, \Sigma)$.
    *Proof Strategy*: Use the Berry-Esseen theorem for sums of independent random variables.

*   **Theorem 1.2 (Isotropy)**:
    If $\mathbf{k}_i$ are drawn from a rotationally invariant distribution, then the covariance function $C(\mathbf{x}, \mathbf{y}) = \mathbb{E}[f(\mathbf{x})f(\mathbf{y})]$ depends only on $|\mathbf{x} - \mathbf{y}|$.

## Phase 2: Geometry of the Landscape (Kac-Rice)

### Goal
Formalize the "Rugged Landscape" argument by bounding the number of local minima.

### Definitions
1.  **CriticalPoint**: $\mathbf{x}$ such that $\nabla f(\mathbf{x}) = 0$.
2.  **Hessian**: $H_f(\mathbf{x})$.

### Theorems to Prove
*   **Theorem 2.1 (Expected Critical Points)**:
    Formalize the Kac-Rice formula:
    $$ \mathbb{E}[\text{Number of Crit Points in } D] = \int_D \mathbb{E}[|\det H_f(\mathbf{x})| \mid \nabla f(\mathbf{x})=0] p_{\nabla f(\mathbf{x})}(0) d\mathbf{x} $$
    
*   **Theorem 2.2 (Exponential Growth)**:
    Prove that for bandwidth $\Omega$, the density of critical points scales as $(\Omega/ \sqrt{d})^d$.
    *Note*: This proves that gradient descent has an exponentially small probability of finding the global minimum (the Key) if started from a random point.

## Phase 3: Indistinguishability (Security Reduction)

### Goal
Prove that an adversary cannot distinguish the "Holographic Pair" $(A, B)$ from two independent random fields $(A, B_{rand})$.

### Definitions
1.  **View**: The set of values/gradients queryable by the adversary.
2.  **Distinguisher**: An algorithm $D$ that outputs 0 or 1.

### Theorems to Prove
*   **Theorem 3.1 (Pointwise Indistinguishability)**:
    For any set of query points $X = \{\mathbf{x}_1, \dots, \mathbf{x}_m\}$ where $\mathbf{x}_i \neq \mathbf{x}_{key}$, the joint distribution of $(A(X), B(X))$ is statistically close to that of independent random fields.
    *Proof Strategy*: Multivariate Gaussian approximation. The constraint at $\mathbf{x}_{key}$ imposes a conditional distribution, but its effect decays rapidly with distance due to the decorrelation of high-frequency waves.

## Phase 4: Implementation Verification (Rust <-> Spec)

### Goal
Verify that the Rust implementation correctly implements the mathematical specification.

### Tasks
1.  **Refinement Proof**: Prove that the `SpectralGenerator` struct in Rust correctly samples from the distributions defined in Phase 1.
2.  **Floating Point Safety**: Bound the accumulated error of `f64` summation to ensure it does not introduce side-channel biases (e.g., denormals revealing structure).

## Timeline

1.  **Week 1**: Phase 1 definitions and Gaussianity proof.
2.  **Week 2**: Phase 2 Kac-Rice formalization (simplified 1D case first).
3.  **Week 3**: Phase 3 Indistinguishability proof.
4.  **Week 4**: Code verification.
