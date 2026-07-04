use spectral_holography::{ish_encrypt_chunk, ISHContext};

#[test]
fn test_variance_leakage() {
    let x = 100.0;
    let y = 200.0;
    let z = 300.0;
    let seed_u64 = 12345;
    let mac_key = [0u8; 32];
    // Create a context
    let ctx = ISHContext::new(x, y, z, seed_u64, None, mac_key);

    let iv = 9999;

    // Test Case 1: All zeros
    let n_samples = 1000; // Reduced size for unit test
    let zeros = vec![0u8; n_samples];
    let deltas_zeros = ish_encrypt_chunk(iv, 0, &zeros, &ctx);

    // Test Case 2: All 255s
    let max_vals = vec![255u8; n_samples];
    let deltas_max = ish_encrypt_chunk(iv, 0, &max_vals, &ctx);

    // Parse deltas (f64 from bytes)
    let deltas_zeros_f64 = parse_deltas(&deltas_zeros);
    let deltas_max_f64 = parse_deltas(&deltas_max);

    // Calculate Variance
    let var_zeros = variance(&deltas_zeros_f64);
    let var_max = variance(&deltas_max_f64);

    println!("Variance (Zeros): {:.2}", var_zeros);
    println!("Variance (255s): {:.2}", var_max);

    // Check for division by zero if variance is 0 (unlikely)
    if var_zeros.abs() < 1e-9 {
        println!("Variance is zero, skipping ratio check.");
    } else {
        let ratio = var_max / var_zeros;
        println!("Ratio: {:.2}", ratio);
        // Ideally, the variance should be indistinguishable.
        assert!(
            (ratio - 1.0).abs() < 0.2,
            "Variance leakage detected! Ratio: {}",
            ratio
        );
    }
}

fn parse_deltas(bytes: &[u8]) -> Vec<f64> {
    let mut res = Vec::new();
    for chunk in bytes.chunks(8) {
        if chunk.len() == 8 {
            let mut arr = [0u8; 8];
            arr.copy_from_slice(chunk);
            res.push(f64::from_le_bytes(arr));
        }
    }
    res
}

fn variance(data: &[f64]) -> f64 {
    let mean = data.iter().sum::<f64>() / data.len() as f64;
    let sum_sq_diff: f64 = data.iter().map(|&x| (x - mean).powi(2)).sum();
    sum_sq_diff / data.len() as f64
}
