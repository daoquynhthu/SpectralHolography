use spectral_holography::{ISHContext, ish_encrypt_file, ish_decrypt_file, ish_encrypt_file_z1, ish_decrypt_file_z1, ish_create_with_password, ish_extract_salt, ish_create_with_salt, ish_free_string};
use std::fs::{self, File};
use std::io::{Write, Read};
use std::ffi::{CString, CStr};

#[test]
fn test_file_encryption_decryption() {
    let input_path = "test_input.txt";
    let encrypted_path = "test_encrypted.ish";
    let decrypted_path = "test_decrypted.txt";

    // 1. Create Input File
    let plaintext = b"Hello, World! This is a test of the ISH encryption system.";
    {
        let mut f = File::create(input_path).unwrap();
        f.write_all(plaintext).unwrap();
    }

    // 2. Setup Context
    let ctx = ISHContext::new(10.0, 20.0, 30.0, 12345, None, [0u8; 32]);

    // 3. Encrypt File
    let in_c = CString::new(input_path).unwrap();
    let out_c = CString::new(encrypted_path).unwrap();
    
    let result = unsafe {
        ish_encrypt_file(
            &ctx as *const _ as *mut _,
            in_c.as_ptr(),
            out_c.as_ptr()
        )
    };
    assert_eq!(result, 0, "Encryption failed");

    // 4. Decrypt File
    let dec_c = CString::new(decrypted_path).unwrap();
    let result = unsafe {
        ish_decrypt_file(
            &ctx as *const _ as *mut _,
            out_c.as_ptr(),
            dec_c.as_ptr()
        )
    };
    // The previous test run failed with -100 (Integrity Check Failed) here.
    // Why? Because we are decrypting 'encrypted_path' which was created by 'ish_encrypt_file'.
    // 'ish_encrypt_file' appends MAC.
    // 'ish_decrypt_file' verifies MAC.
    // So it should work if the MAC key is correct.
    // In this test 'test_file_encryption_decryption', we use a manually created ctx with MAC key [0u8; 32].
    // Both encrypt and decrypt use the same ctx, so same MAC key.
    // Wait, the failure was likely due to the previous run not having updated code compiled or something?
    // Or maybe the MAC calculation is wrong?
    // Let's look at the error: left: -100, right: 0.
    // So integrity check failed.
    
    // Ah, 'ish_encrypt_file' writes to 'writer' (BufWriter).
    // Then it drops 'writer'.
    // Then 'ish_append_integrity' opens the file again to append MAC.
    // This seems correct.
    
    // 'ish_decrypt_file' reads the file.
    // It calls 'ish_verify_integrity' first.
    // 'ish_verify_integrity' reads the whole file except last 32 bytes as content, and last 32 bytes as MAC.
    // Then it calculates MAC over content and compares.
    
    // One potential issue: BufWriter might not have flushed everything to disk before 'ish_append_integrity' opens it?
    // We called 'writer.flush()' and 'drop(writer)'. That should be enough.
    
    assert_eq!(result, 0, "Decryption failed");

    // 5. Verify Content
    let mut decrypted_content = Vec::new();
    {
        let mut f = File::open(decrypted_path).unwrap();
        f.read_to_end(&mut decrypted_content).unwrap();
    }

    // Remove null bytes (failed blocks) if any, or just compare
    // Since failed blocks are rare, we expect exact match or match with 0s.
    // For this short text, failure is unlikely.
    assert_eq!(decrypted_content, plaintext, "Decrypted content does not match plaintext");

    // Cleanup
    let _ = fs::remove_file(input_path);
    let _ = fs::remove_file(encrypted_path);
    let _ = fs::remove_file(decrypted_path);
}

#[test]
fn test_compression_ratio() {
    let input_path = "test_ratio_input.txt";
    let enc_std_path = "test_ratio_std.ish";
    let enc_z1_path = "test_ratio_z1.ish";

    // Create a larger file to minimize header impact
    let plaintext = vec![b'A'; 1000];
    {
        let mut f = File::create(input_path).unwrap();
        f.write_all(&plaintext).unwrap();
    }

    let ctx = ISHContext::new(10.0, 20.0, 30.0, 12345, None, [0u8; 32]);

    // Encrypt Standard
    let in_c = CString::new(input_path).unwrap();
    let out_std = CString::new(enc_std_path).unwrap();
    
    unsafe {
        ish_encrypt_file(
            &ctx as *const _ as *mut _,
            in_c.as_ptr(),
            out_std.as_ptr()
        );
    }

    // Encrypt Z1
    let out_z1 = CString::new(enc_z1_path).unwrap();
    unsafe {
        ish_encrypt_file_z1(
            &ctx as *const _ as *mut _,
            in_c.as_ptr(),
            out_z1.as_ptr()
        );
    }

    // Check sizes
    let size_std = fs::metadata(enc_std_path).unwrap().len();
    let size_z1 = fs::metadata(enc_z1_path).unwrap().len();

    println!("Std Size: {}, Z1 Size: {}", size_std, size_z1);

    // Standard: 8 bytes/byte (f64 per byte)
    // Z1: Optimized to ~2 bytes/byte (f64 per 4 bytes)
    // + header overhead

    let ratio_std = size_std as f64 / 1000.0;
    let ratio_z1 = size_z1 as f64 / 1000.0;

    println!("Ratio Std: {:.2}, Ratio Z1: {:.2}", ratio_std, ratio_z1);

    assert!(ratio_std > 7.5 && ratio_std < 8.5, "Standard mode should have ~8x expansion");
    // Z1 mode packs 4 bytes into 1 f64 (8 bytes), so expansion is 8/4 = 2x.
    // Allow some margin for header/padding
    assert!(ratio_z1 > 1.8 && ratio_z1 < 2.5, "Z1 mode should have ~2x expansion");

    // Cleanup
    let _ = fs::remove_file(input_path);
    let _ = fs::remove_file(enc_std_path);
    let _ = fs::remove_file(enc_z1_path);
}

#[test]
fn test_z1_roundtrip_correctness() {
    let input_path = "test_z1_rt_input.txt";
    let encrypted_path = "test_z1_rt.ish";
    let decrypted_path = "test_z1_rt_dec.txt";

    // Test with data length not divisible by 4 to verify padding/length handling
    // 1001 bytes = 250 chunks of 4 bytes + 1 chunk of 1 byte
    let plaintext = vec![b'B'; 1001]; 
    {
        let mut f = File::create(input_path).unwrap();
        f.write_all(&plaintext).unwrap();
    }

    let ctx = ISHContext::new(10.0, 20.0, 30.0, 54321, None, [0u8; 32]);
    let in_c = CString::new(input_path).unwrap();
    let out_c = CString::new(encrypted_path).unwrap();
    let dec_c = CString::new(decrypted_path).unwrap();

    // Encrypt Z1
    unsafe {
        ish_encrypt_file_z1(
            &ctx as *const _ as *mut _,
            in_c.as_ptr(),
            out_c.as_ptr()
        );
    }

    // Decrypt Z1
    let result = unsafe {
        ish_decrypt_file_z1(
            &ctx as *const _ as *mut _,
            out_c.as_ptr(),
            dec_c.as_ptr()
        )
    };
    assert_eq!(result, 0, "Z1 Decryption failed");

    // Verify
    let mut decrypted_content = Vec::new();
    {
        let mut f = File::open(decrypted_path).unwrap();
        f.read_to_end(&mut decrypted_content).unwrap();
    }

    assert_eq!(decrypted_content.len(), plaintext.len(), "Decrypted length mismatch");
    assert_eq!(decrypted_content, plaintext, "Decrypted content mismatch");

    // Cleanup
    let _ = fs::remove_file(input_path);
    let _ = fs::remove_file(encrypted_path);
    let _ = fs::remove_file(decrypted_path);
}

#[test]
fn test_integrity_check() {
    let input_path = "test_integrity_input.txt";
    let encrypted_path = "test_integrity.ish";
    let decrypted_path = "test_integrity_decrypted.txt";
    let password = "IntegrityTestPassword";

    // 1. Create Input
    {
        let mut f = File::create(input_path).unwrap();
        f.write_all(b"Integrity check content").unwrap();
    }

    // 2. Encrypt
    let pass_c = CString::new(password).unwrap();
    let ctx_ptr = unsafe { ish_create_with_password(pass_c.as_ptr()) };
    
    let in_c = CString::new(input_path).unwrap();
    let out_c = CString::new(encrypted_path).unwrap();
    
    unsafe { ish_encrypt_file(ctx_ptr, in_c.as_ptr(), out_c.as_ptr()) };

    // 3. Extract Salt (needed for decryption context)
    let salt_ptr = unsafe { ish_extract_salt(out_c.as_ptr()) };
    let ctx_dec = unsafe { ish_create_with_salt(pass_c.as_ptr(), salt_ptr) };

    // 4. Verify Decryption Works (Integrity OK)
    // We need to re-create the context because ish_decrypt_file doesn't consume it but we need it for tamper check
    // Wait, pointers are raw, they persist until freed.
    let dec_c = CString::new(decrypted_path).unwrap();
    let res = unsafe { ish_decrypt_file(ctx_dec, out_c.as_ptr(), dec_c.as_ptr()) };
    assert_eq!(res, 0, "Decryption should succeed with valid file");

    // 5. Tamper with Encrypted File
    {
        let mut data = fs::read(encrypted_path).unwrap();
        let len = data.len();
        // Flip a bit in the middle
        data[len / 2] ^= 0x01; 
        fs::write(encrypted_path, &data).unwrap();
    }

    // 6. Verify Decryption Fails
    let res_tampered = unsafe { ish_decrypt_file(ctx_dec, out_c.as_ptr(), dec_c.as_ptr()) };
    assert_eq!(res_tampered, -100, "Decryption should fail with integrity error");

    // Cleanup
    unsafe {
        ish_free_string(salt_ptr);
        let _ = Box::from_raw(ctx_ptr);
        let _ = Box::from_raw(ctx_dec);
    }
    let _ = fs::remove_file(input_path);
    let _ = fs::remove_file(encrypted_path);
    let _ = fs::remove_file(decrypted_path);
}

#[test]
fn test_file_encryption_decryption_z1() {
    let input_path = "test_input_z1.txt";
    let encrypted_path = "test_encrypted_z1.ish";
    let decrypted_path = "test_decrypted_z1.txt";

    // 1. Create Input File
    let plaintext = b"ISH-Z1 Compression Test Data.";
    {
        let mut f = File::create(input_path).unwrap();
        f.write_all(plaintext).unwrap();
    }

    // 2. Setup Context
    let ctx = ISHContext::new(10.0, 20.0, 30.0, 12345, None, [0u8; 32]);

    // 3. Encrypt File (Z1)
    let in_c = CString::new(input_path).unwrap();
    let out_c = CString::new(encrypted_path).unwrap();
    
    let result = unsafe {
        ish_encrypt_file_z1(
            &ctx as *const _ as *mut _,
            in_c.as_ptr(),
            out_c.as_ptr()
        )
    };
    assert_eq!(result, 0, "Z1 Encryption failed");

    // 4. Decrypt File (Z1)
    let dec_c = CString::new(decrypted_path).unwrap();
    let result = unsafe {
        ish_decrypt_file_z1(
            &ctx as *const _ as *mut _,
            out_c.as_ptr(),
            dec_c.as_ptr()
        )
    };
    assert_eq!(result, 0, "Z1 Decryption failed");

    // 5. Verify Content
    let mut decrypted_content = Vec::new();
    {
        let mut f = File::open(decrypted_path).unwrap();
        f.read_to_end(&mut decrypted_content).unwrap();
    }

    // Z1 is lossy due to quantization (f32) and potentially thresholding.
    // However, with f32 delta, precision should be enough for byte recovery (u8).
    // Let's see if it matches exactly.
    assert_eq!(decrypted_content, plaintext, "Z1 Decrypted content does not match plaintext");

    // Cleanup
    let _ = fs::remove_file(input_path);
    let _ = fs::remove_file(encrypted_path);
    let _ = fs::remove_file(decrypted_path);
}

#[test]
fn test_salt_storage_and_recovery() {
    let input_path = "test_salt_input.txt";
    let encrypted_path = "test_salt_encrypted.ish";
    let decrypted_path = "test_salt_decrypted.txt";
    let password = "MySecurePassword123!";

    // 1. Create Input File
    let plaintext = b"Salt storage verification test.";
    {
        let mut f = File::create(input_path).unwrap();
        f.write_all(plaintext).unwrap();
    }

    // 2. Encrypt with Password (creates random salt and stores it)
    let pass_c = CString::new(password).unwrap();
    let ctx_ptr = unsafe { ish_create_with_password(pass_c.as_ptr()) };
    assert!(!ctx_ptr.is_null(), "Context creation failed");

    let in_c = CString::new(input_path).unwrap();
    let out_c = CString::new(encrypted_path).unwrap();

    let enc_result = unsafe {
        ish_encrypt_file(
            ctx_ptr,
            in_c.as_ptr(),
            out_c.as_ptr()
        )
    };
    assert_eq!(enc_result, 0, "Encryption failed");

    // 3. Extract Salt independently
    let salt_ptr = unsafe { ish_extract_salt(out_c.as_ptr()) };
    assert!(!salt_ptr.is_null(), "Salt extraction failed");
    
    let salt_str = unsafe { CStr::from_ptr(salt_ptr).to_string_lossy().into_owned() };
    println!("Extracted Salt: {}", salt_str);
    assert!(salt_str.starts_with("$argon2id$"), "Invalid salt format");

    // 4. Decrypt using Password AND Extracted Salt
    // This simulates a fresh session where we only have the file and password
    let ctx_dec_ptr = unsafe { ish_create_with_salt(pass_c.as_ptr(), salt_ptr) };
    assert!(!ctx_dec_ptr.is_null(), "Context recreation with salt failed");

    let dec_c = CString::new(decrypted_path).unwrap();
    let dec_result = unsafe {
        ish_decrypt_file(
            ctx_dec_ptr,
            out_c.as_ptr(),
            dec_c.as_ptr()
        )
    };
    assert_eq!(dec_result, 0, "Decryption failed");

    // 5. Verify Content
    let mut decrypted_content = Vec::new();
    {
        let mut f = File::open(decrypted_path).unwrap();
        f.read_to_end(&mut decrypted_content).unwrap();
    }
    assert_eq!(decrypted_content, plaintext, "Decrypted content mismatch with salt recovery");

    // Cleanup
    unsafe {
        ish_free_string(salt_ptr);
        let _ = Box::from_raw(ctx_ptr);
        let _ = Box::from_raw(ctx_dec_ptr);
    }
    let _ = fs::remove_file(input_path);
    let _ = fs::remove_file(encrypted_path);
    let _ = fs::remove_file(decrypted_path);
}
