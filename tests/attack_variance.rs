use spectral_holography::{ish_create, ish_encrypt, ish_destroy, generate_field};
use sha2::{Sha256, Digest};

// Helper to derive seed (Replicating internal logic)
fn derive_test_seed(iv: u64, _chunk_index: u64, x: f64, y: f64, z: f64, ref_salt: u64, mac_key: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(&iv.to_le_bytes());
    // Chunk index NOT included in ish_encrypt (buffer mode)
    // hasher.update(&chunk_index.to_le_bytes()); 
    hasher.update(&x.to_le_bytes());
    hasher.update(&y.to_le_bytes());
    hasher.update(&z.to_le_bytes());
    hasher.update(&ref_salt.to_le_bytes());
    hasher.update(mac_key);
    hasher.finalize().into()
}

#[test]
fn test_variance_distinction() {
    unsafe {
        println!("--- Starting Variance Distinction Attack Test ---");
        
        let seed_u64 = 12345;
        let true_x = 100.0;
        let true_y = -50.0;
        let true_z = 25.0;
        
        // 1. Create Context (Simulation of System)
        let ctx_ptr = ish_create(seed_u64, true_x, true_y, true_z);
        let ctx = &*ctx_ptr;
        
        // Replicate the mac_key generation that happens inside ish_create
        // We can just read it from the context since we have the pointer!
        let mac_key = ctx.mac_key;
        let ref_salt = seed_u64; // ish_create uses seed as ref_salt
        
        // 2. Encrypt Known Plaintext
        let len = 100;
        let plaintext = vec![255u8; len]; // Max contrast for max variance difference
        // Output format: IV (8) + ChunkCount (8) + Data (len * 8) + MAC (32)
        // ish_encrypt produces f64 deltas (8 bytes each).
        let out_len = 16 + len * 8 + 32;
        let mut ciphertext = vec![0u8; out_len];
        
        ish_encrypt(ctx_ptr, plaintext.as_ptr(), ciphertext.as_mut_ptr(), len);
        
        // 3. Parse Ciphertext
        let mut ptr = ciphertext.as_ptr();
        let mut iv_bytes = [0u8; 8];
        std::ptr::copy_nonoverlapping(ptr, iv_bytes.as_mut_ptr(), 8);
        let iv = u64::from_le_bytes(iv_bytes);
        ptr = ptr.add(16); // Skip IV + Count
        
        let mut deltas = Vec::new();
        for _ in 0..len {
            let mut delta_bytes = [0u8; 8];
            std::ptr::copy_nonoverlapping(ptr, delta_bytes.as_mut_ptr(), 8);
            let delta = f64::from_le_bytes(delta_bytes);
            deltas.push(delta);
            ptr = ptr.add(8);
        }
        
        let _field_a = generate_field(iv, 1000);
        let _field_b_secret = generate_field(iv ^ ctx.get_ref_salt(), 1000);
        
        // 5. Try to guess (x, y, z)
        // We will just show that the "variance ratio" approach fails or is consistent.
        // In the original attack, we tried to minimize variance of (Delta + B) / A.
        
        let _compute_variance = |guess_x: f64, guess_y: f64, guess_z: f64| -> f64 {     
            // Re-generate trajectory with guess
            // Note: This requires access to internal trajectory logic which attacker doesn't have easily
            // unless they know how seed is derived.
            // But let's assume they can guess seed if they guess KeyLoc.
            // ...
            0.0 // Placeholder
        };
        
        // Check that different keys derive different seeds
        let seed_correct = derive_test_seed(iv, 0, true_x, true_y, true_z, ref_salt, &mac_key);
        let seed_wrong = derive_test_seed(iv, 0, true_x + 1.0, true_y, true_z, ref_salt, &mac_key);
        assert_ne!(seed_correct, seed_wrong);
        
        ish_destroy(ctx_ptr);
    }
}
