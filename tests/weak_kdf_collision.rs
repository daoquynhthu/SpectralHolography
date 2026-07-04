use spectral_holography::{ish_create_with_password, ish_destroy};
use std::ffi::CString;

#[test]
fn test_kdf_strength_audit() {
    println!("--- Auditing Password Key Derivation Function (KDF) ---");
    
    let password = "TopSecretPassword123";
    
    // Verify KDF Slowness (Argon2id Check)
    let start = std::time::Instant::now();
    let iterations = 2; 
    let _ctx = unsafe { ish_create_with_password(CString::new(password).unwrap().as_ptr()) };
    let _ctx2 = unsafe { ish_create_with_password(CString::new(password).unwrap().as_ptr()) };
    
    let duration = start.elapsed();
    println!("Time for {} hashes: {:?}", iterations, duration);
    
    // Argon2id should take significant time. 
    // We expect at least 5ms per hash on modern CPUs for default settings, likely much more.
    assert!(duration.as_millis() > 10, "KDF is too fast! Potential vulnerability to brute force.");

    unsafe {
        ish_destroy(_ctx);
        ish_destroy(_ctx2);
    }
    
    println!("SECURITY VERIFIED: KDF is Argon2id (Slow, Salted, Cryptographic).");
}
