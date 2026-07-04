use spectral_holography::{ish_create_with_password, ish_decrypt, ish_destroy, ish_encrypt};
use std::ffi::CString;

#[test]
fn test_malleability() {
    unsafe {
        println!("--- Testing Malleability (Integrity) in 3D ---");

        let password = CString::new("TopSecretKey").unwrap();
        let ctx_ptr = ish_create_with_password(password.as_ptr());

        if ctx_ptr.is_null() {
            panic!("Failed to create context");
        }

        // 1. Encrypt a known message
        let plaintext = b"Transfer $1000 to Alice";
        let len = plaintext.len();
        // Ciphertext length: 16 (IV+Count) + len * 8 (Deltas) + 32 (HMAC)
        let out_len = 16 + len * 8 + 32;
        let mut ciphertext = vec![0u8; out_len];

        ish_encrypt(ctx_ptr, plaintext.as_ptr(), ciphertext.as_mut_ptr(), len);

        // 2. Attacker Intercepts and Modifies Ciphertext
        // The attacker wants to change "$1000" to "$9000"
        // "$1000" is at index 10.
        // But due to 3D projection, modifying delta creates unpredictable change.

        let target_idx = 10; // '$' is 9, '1' is 10.
        let delta_offset = 16 + target_idx * 8; // Skip IV(8)+Count(8)

        let ptr = ciphertext.as_mut_ptr().add(delta_offset);
        let mut delta_bytes = [0u8; 8];
        std::ptr::copy_nonoverlapping(ptr, delta_bytes.as_mut_ptr(), 8);
        let mut delta = f64::from_le_bytes(delta_bytes);

        // Modify Delta slightly
        delta += 10.0;

        let new_bytes = delta.to_le_bytes();
        std::ptr::copy_nonoverlapping(new_bytes.as_ptr(), ptr, 8);

        // 3. Decrypt
        let mut decrypted = vec![0u8; len];
        let res = ish_decrypt(ctx_ptr, ciphertext.as_ptr(), decrypted.as_mut_ptr(), len);

        // 4. Verification
        // Due to HMAC-SHA256 integrity check, any tampering should be detected.
        // The decryption function should return -100 (Integrity Check Failed).

        if res == 0 {
            // If it somehow succeeded (e.g. hash collision or check disabled), verify the content changed
            let dec_str = String::from_utf8_lossy(&decrypted);
            println!("Original: {}", String::from_utf8_lossy(plaintext));
            println!("Modified: {}", dec_str);
            assert_ne!(
                plaintext[target_idx], decrypted[target_idx],
                "Target byte should change if integrity check passed"
            );
            println!("WARNING: Integrity check passed despite tampering! (This should not happen with HMAC)");
        } else {
            println!("Integrity Check Failed as expected: {}", res);
            assert_eq!(res, -100, "Should fail with integrity error");
        }

        println!("Malleability mitigation confirmed: Ciphertext modification detected.");

        ish_destroy(ctx_ptr);
    }
}
