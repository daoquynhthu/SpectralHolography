use spectral_holography::{
    ish_create_with_password, ish_create_with_salt, ish_decrypt_file, ish_encrypt_file,
    ish_encrypt_file_z1, ish_extract_salt, ish_free_string,
};
use std::ffi::CString;
use std::fs::{self};
use std::time::Instant;

const TEST_SIZES: [usize; 4] = [100, 1024, 10 * 1024, 1024 * 1024]; // 100B, 1KB, 10KB, 1MB
const PASSWORD: &str = "PerformanceTestPassword123!";

fn run_test_for_size(size: usize) {
    println!("\n--- Testing with Plaintext Size: {} bytes ---", size);

    let input_path = format!("perf_test_{}.bin", size);
    let enc_path = format!("perf_test_{}.ish", size);
    let enc_z1_path = format!("perf_test_{}.z1.ish", size);
    let dec_path = format!("perf_test_{}_dec.bin", size);

    // 1. Create random input file
    let mut data = vec![0u8; size];
    for i in 0..size {
        data[i] = (i % 255) as u8;
    }
    fs::write(&input_path, &data).expect("Failed to write input file");

    let pass_c = CString::new(PASSWORD).unwrap();
    let in_c = CString::new(input_path.clone()).unwrap();
    let enc_c = CString::new(enc_path.clone()).unwrap();
    let enc_z1_c = CString::new(enc_z1_path.clone()).unwrap();
    let dec_c = CString::new(dec_path.clone()).unwrap();

    // --- Standard ISH Encryption ---
    println!("[Standard ISH]");
    let ctx = unsafe { ish_create_with_password(pass_c.as_ptr()) };

    let start = Instant::now();
    let res = unsafe { ish_encrypt_file(ctx, in_c.as_ptr(), enc_c.as_ptr()) };
    let duration = start.elapsed();
    assert_eq!(res, 0, "Encryption failed");

    let enc_size = fs::metadata(&enc_path).unwrap().len();
    let ratio = enc_size as f64 / size as f64;
    let speed = (size as f64 / 1024.0) / duration.as_secs_f64();

    println!("  Encryption Time: {:.4} s", duration.as_secs_f64());
    println!("  Speed:           {:.2} KB/s", speed);
    println!("  Ciphertext Size: {} bytes", enc_size);
    println!(
        "  Expansion Ratio: {:.2}x (Overhead: {} bytes)",
        ratio,
        enc_size - size as u64
    );

    // Verify Decryption (Standard)
    let salt_ptr = unsafe { ish_extract_salt(enc_c.as_ptr()) };
    let ctx_dec = unsafe { ish_create_with_salt(pass_c.as_ptr(), salt_ptr) };

    let start_dec = Instant::now();
    let res_dec = unsafe { ish_decrypt_file(ctx_dec, enc_c.as_ptr(), dec_c.as_ptr()) };
    let duration_dec = start_dec.elapsed();
    assert_eq!(res_dec, 0, "Decryption failed");

    let speed_dec = (size as f64 / 1024.0) / duration_dec.as_secs_f64();
    println!("  Decryption Time: {:.4} s", duration_dec.as_secs_f64());
    println!("  Decryption Speed:{:.2} KB/s", speed_dec);

    // Clean up contexts
    unsafe {
        let _ = Box::from_raw(ctx);
        let _ = Box::from_raw(ctx_dec);
        ish_free_string(salt_ptr);
    }

    // --- ISH-Z1 Encryption (Compressed) ---
    println!("[ISH-Z1 (Compressed)]");
    let ctx_z1 = unsafe { ish_create_with_password(pass_c.as_ptr()) };

    let start_z1 = Instant::now();
    let res_z1 = unsafe { ish_encrypt_file_z1(ctx_z1, in_c.as_ptr(), enc_z1_c.as_ptr()) };
    let duration_z1 = start_z1.elapsed();
    assert_eq!(res_z1, 0, "Z1 Encryption failed");

    let enc_z1_size = fs::metadata(&enc_z1_path).unwrap().len();
    let ratio_z1 = enc_z1_size as f64 / size as f64;
    let speed_z1 = (size as f64 / 1024.0) / duration_z1.as_secs_f64();

    println!("  Encryption Time: {:.4} s", duration_z1.as_secs_f64());
    println!("  Speed:           {:.2} KB/s", speed_z1);
    println!("  Ciphertext Size: {} bytes", enc_z1_size);
    println!("  Expansion Ratio: {:.2}x", ratio_z1);

    // Clean up Z1
    unsafe {
        let _ = Box::from_raw(ctx_z1);
    }

    // Cleanup files
    let _ = fs::remove_file(input_path);
    let _ = fs::remove_file(enc_path);
    let _ = fs::remove_file(enc_z1_path);
    let _ = fs::remove_file(dec_path);
}

#[test]
fn test_performance_and_ratio() {
    println!("Starting Performance and Ratio Tests...");
    for &size in &TEST_SIZES {
        run_test_for_size(size);
    }
}
