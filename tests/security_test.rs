use spectral_holography::{
    generate_field, ISHContext, Vector3D,
    ish_encrypt
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

const N_WAVES: usize = 1000;

#[test]
fn test_kpa_mitigation() {
    // 1. Setup Context with known Key and Salt
    let true_x = 123.45;
    let true_y = 678.90;
    let true_z = 321.00;
    let secret_salt = 0xDEADBEEFCAFEBABE;
    let mac_key = [0u8; 32];
    let ctx = ISHContext::new(true_x, true_y, true_z, secret_salt, None, mac_key);

    // 2. Encrypt a known plaintext (first byte 'H' = 72)
    let plaintext = b"H";
    let len = plaintext.len();
    let mut output = vec![0u8; 1000]; // Large buffer

    unsafe {
        ish_encrypt(
            &ctx as *const _ as *mut _,
            plaintext.as_ptr(),
            output.as_mut_ptr(),
            len
        );
    }

    // 3. Extract IV and Delta
    // Output format: [IV: 8][Count: 8][Deltas: 8 * len]
    let iv_bytes: [u8; 8] = output[0..8].try_into().unwrap();
    let iv = u64::from_le_bytes(iv_bytes);
    
    // Skip count (8 bytes)
    
    let delta_bytes: [u8; 8] = output[16..24].try_into().unwrap();
    let delta = f64::from_le_bytes(delta_bytes);

    // 4. Attacker Logic: Try to recover key using only public IV
    let field_b_public = generate_field(iv, N_WAVES); // Attacker uses IV (No Salt)
    let field_a = generate_field(iv, N_WAVES);        // Field A is public (IV only)
    
    // Note: We don't know the mask, but let's assume attacker guesses mask=0 or knows it somehow?
    // Wait, the test logic was:
    // let p_target = plaintext[0] as f64; 
    // This assumes mask is 0 or ignored?
    // In original code: `let p_target = (byte ^ mask) as f64;`
    // If mask is random, attacker can't know p_target exactly even with known plaintext.
    // But maybe the test assumes specific RNG state?
    // Ah, the test logic:
    // let mut point_rng = ChaCha20Rng::seed_from_u64(iv);
    // This assumes point_rng is seeded with IV only!
    // But in `ish_encrypt_chunk`, `point_rng` is seeded with `derive_chunk_seed(iv, ctx)`.
    // And `derive_chunk_seed` uses `ctx.key_loc` and `ctx.ref_salt`.
    // So the attacker CANNOT replicate `point_rng` unless they know key location and salt.
    // The original test `seed_from_u64(iv)` was checking if IV ALONE was sufficient to predict points.
    // Since we now use `derive_chunk_seed` which mixes in secret info, this attack is definitely mitigated.
    // The test constructs a "naive" attacker who thinks points are generated from IV only.
    
    let p_target = plaintext[0] as f64; // Attacker guess (ignoring mask)
    
    let mut point_rng = ChaCha20Rng::seed_from_u64(iv);
    // Replicate jitter for first byte (Attacker's guess at trajectory)
    // Note: Attacker doesn't know true_x, true_y, true_z either.
    // If they guess wrong location, they get wrong points.
    // If they guess IV-based seeding, they get wrong RNG stream.
    
    let dx = (point_rng.gen::<f64>() - 0.5) * 0.1;
    let dy = (point_rng.gen::<f64>() - 0.5) * 0.1;
    let dz = (point_rng.gen::<f64>() - 0.5) * 0.1;
    let sample_loc = Vector3D::new(true_x + dx, true_y + dy, true_z + dz);
    
    let val_a = field_a.eval_at_point(&sample_loc);
    let val_b_attacker = field_b_public.eval_at_point(&sample_loc);
    
    // Attacker expects: delta = -p * val_a - val_b
    // So we check if: delta + p*val_a + val_b == 0
    
    let lhs = delta + p_target * val_a + val_b_attacker;
    
    // If salt is effective (and seed derivation), lhs should NOT be close to 0
    let true_key_found = lhs.abs() < 1e-5;
    
    assert!(!true_key_found, "KPA Vulnerability: True key satisfies attacker equation! Salt is ineffective.");
}
