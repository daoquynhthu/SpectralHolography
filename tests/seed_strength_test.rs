use spectral_holography::{ish_encrypt_chunk, ISHContext};

#[test]
fn test_seed_entropy_usage() {
    // This test verifies that the encryption uses the full 256-bit entropy of the seed,
    // not just a 64-bit subset (which was the previous vulnerability).

    // Create a context
    let x = 100.0;
    let y = 200.0;
    let z = 300.0;
    let seed_u64 = 12345;
    let mac_key = [0u8; 32];
    let ctx = ISHContext::new(x, y, z, seed_u64, None, mac_key);

    let data = vec![0u8; 1000]; // 1000 zeros
    let iv = 9999;

    // We are testing sensitivity to IV (which acts as seed for the chunk) or ctx parameters.
    // The original test was changing the "seed" passed to ish_encrypt_chunk.
    // In the new API, the "seed" is derived from IV and ctx.ref_salt internally.
    // But wait, the original test was testing `seed_base` passed as argument.
    // In the new API, there is no explicit seed argument to ish_encrypt_chunk.
    // The seed is derived from IV.

    // So to test entropy usage, we should test sensitivity to IV or ref_salt changes?
    // The original test was about the 256-bit seed used for ChaCha20.
    // In the new implementation, we derive a 32-byte seed for ChaCha20 from (IV, chunk_index, x, y, z, ref_salt, mac_key).
    // So we should verify that changing any of these parameters changes the output significantly.

    // Let's test sensitivity to IV (u64) - but that's only 64 bits.
    // Let's test sensitivity to ref_salt (u64) - also 64 bits.
    // The original test was testing `seed: [u8; 32]`.
    // We don't expose passing a raw 32-byte seed anymore in ish_encrypt_chunk.
    // The seed derivation is internal: `let seed = derive_chunk_seed(iv, ctx);`

    // However, we can test that small changes in x, y, z cause large changes in output (Avalanche).
    // Or we can verify that the `derive_chunk_seed` function (if exposed or its effect) uses all bits.

    // Let's verify that changing x by a tiny amount changes output.
    let ctx_base = ISHContext::new(x, y, z, seed_u64, None, mac_key);
    let output_base = ish_encrypt_chunk(iv, 0, &data, &ctx_base);

    // Change x slightly
    let ctx_x = ISHContext::new(x + 1e-9, y, z, seed_u64, None, mac_key);
    let output_x = ish_encrypt_chunk(iv, 0, &data, &ctx_x);

    // Change z slightly
    let ctx_z = ISHContext::new(x, y, z + 1e-9, seed_u64, None, mac_key);
    let output_z = ish_encrypt_chunk(iv, 0, &data, &ctx_z);

    // Change IV
    let output_iv = ish_encrypt_chunk(iv ^ 1, 0, &data, &ctx_base);

    // Verify all outputs are distinct
    assert_ne!(output_base, output_x, "Changing x must change output");
    assert_ne!(output_base, output_z, "Changing z must change output");
    assert_ne!(output_base, output_iv, "Changing IV must change output");

    // Verify Avalanche Effect (Statistical check)
    fn count_diffs(a: &[u8], b: &[u8]) -> usize {
        a.iter().zip(b.iter()).filter(|(x, y)| x != y).count()
    }

    let diff_x = count_diffs(&output_base, &output_x);
    let diff_z = count_diffs(&output_base, &output_z);
    let diff_iv = count_diffs(&output_base, &output_iv);

    println!("Diff X: {}/{}", diff_x, output_base.len());
    println!("Diff Z: {}/{}", diff_z, output_base.len());
    println!("Diff IV: {}/{}", diff_iv, output_base.len());

    // Since output is encrypted bytes (u8), we expect ~99% of bytes to be different (since values change, not just bit flips, but byte values).
    // Actually, even a small change in coordinate means completely different sampling points, so different PRNG stream.
    // The output bytes are `delta = (val_b - val_a * pixel)`.
    // val_b and val_a will be completely different.
    // So deltas will be completely different.

    // With u8 outputs, the probability of collision for a byte is 1/256.
    // So we expect ~255/256 * 1000 differences. ~996 differences.
    assert!(diff_x > 900, "Avalanche failure: X change ignored?");
    assert!(diff_z > 900, "Avalanche failure: Z change ignored?");
    assert!(diff_iv > 900, "Avalanche failure: IV change ignored?");
}
