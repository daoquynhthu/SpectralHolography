# Isotropic Spectral Holography (ISH)

High-performance Rust implementation of **Isotropic Spectral Holography (ISH)**, a cryptographic primitive based on the hardness of finding global optima in high-dimensional random fields.

## Features

- **3D Spectral Domain**: Operates in $\mathbb{R}^3$, leveraging complex topological traps to prevent gradient-based attacks.
- **Z1 Compression Mode**: **2x expansion ratio** (down from 8x) by packing 4 bytes into a single high-precision spectral delta.
- **Side-Channel Hardened**: Constant-time sampling with branchless selection logic; AVX2-accelerated field evaluation.
- **Integrity Protection**: Built-in HMAC-SHA256 verification.

## Documentation

- **[Mathematical Specification](docs/MATH_SPEC.md)** — 3D construction, hardness assumptions, Z1 compression
- **[API Reference](docs/API.md)** — C-compatible FFI for cross-language integration
- **[Security Analysis](docs/SECURITY_ANALYSIS.md)** — Attack vectors and mitigations
- **[Proof Roadmap](docs/PROOF_ROADMAP.md)** — Coq formal verification progress
- **[Coq Proofs](docs/proof/)** — Formal proof source files

## Building

```bash
cargo build --release
cargo test
cargo bench
```

## Quick Start

```rust
use spectral_holography::ISHContext;

let ctx = ISHContext::new_with_password("my_secret_password");
ish_encrypt_file_z1(&ctx, "plain.txt", "encrypted.ish");
ish_decrypt_file_z1(&ctx, "encrypted.ish", "decrypted.txt");
```

## Scripts

Utility scripts are in [`scripts/`](scripts/):
- `test_ish_dll.py` — Test the compiled DLL via FFI
- `measure_ratio.py` — Measure plaintext/ciphertext volume ratios
- `verify_math_risks.py` — Verify mathematical security properties
- `prototypes/poc.py` — Proof-of-concept simulation

## License

Apache 2.0
