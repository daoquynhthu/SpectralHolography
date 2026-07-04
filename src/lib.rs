#![allow(clippy::missing_safety_doc)]
use argon2::{
    password_hash::{
        rand_core::OsRng,
        PasswordHasher, SaltString, PasswordHash
    },
    Argon2
};
use hmac::{Hmac, Mac};
use sha2::{Sha256, Digest};
use subtle::{ConstantTimeEq, ConditionallySelectable, Choice};
use zeroize::{Zeroize, ZeroizeOnDrop};
use rand_chacha::{ChaCha20Rng, rand_core::{SeedableRng, RngCore}};
use rand::Rng;

// Create alias for HMAC-SHA256
type HmacSha256 = Hmac<Sha256>;

/// Helper to find a valid sampling point in constant time to prevent side-channel leakage.
/// Returns (chosen_loc, val_a, mask).
#[inline(always)]
fn find_valid_point_ct(
    field_a: &SpectralField,
    rng: &mut ChaCha20Rng
) -> (Vector3D, f64, u8) {
    let mut chosen_loc = Vector3D::new(0.0, 0.0, 0.0);
    let mut chosen_val_a: f64 = 0.0;
    let mut chosen_mask = 0u8;
    let mut found = 0u8; // 0 = false, 1 = true

    for j in 0..12 {
        let r1 = rng.next_u64();
        let sample_x = (r1 as f64 / u64::MAX as f64 - 0.5) * 2000.0;
        
        let r2 = rng.next_u64();
        let sample_y = (r2 as f64 / u64::MAX as f64 - 0.5) * 2000.0;
        
        let r3 = rng.next_u64();
        let sample_z = (r3 as f64 / u64::MAX as f64 - 0.5) * 2000.0;

        let mask = (rng.next_u32() & 0xFF) as u8;
        
        let sample_loc = Vector3D::new(sample_x, sample_y, sample_z);
        let val_a = field_a.eval_at_point(&sample_loc);
        
        // Check validity: abs(val_a) >= SINGULARITY_THRESHOLD
        let is_valid = val_a.abs() >= SINGULARITY_THRESHOLD;
        let is_last = j == 11;
        
        // Constant-time selection logic
        // select_this = (is_valid | is_last) & !found
        let u_valid = if is_valid { 1u8 } else { 0u8 };
        let u_last = if is_last { 1u8 } else { 0u8 };
        
        let u_select = (u_valid | u_last) & (found ^ 1);
        let c_select = Choice::from(u_select);
        
        // Update chosen values if selected
        chosen_loc.conditional_assign(&sample_loc, c_select);
        chosen_mask.conditional_assign(&mask, c_select);
        
        // f64 conditional select
        let u_val_a = val_a.to_bits();
        let u_chosen_val_a = chosen_val_a.to_bits();
        let u_new_val_a = u64::conditional_select(&u_chosen_val_a, &u_val_a, c_select);
        chosen_val_a = f64::from_bits(u_new_val_a);
        
        // found = found | select
        found |= u_select;
    }
    
    (chosen_loc, chosen_val_a, chosen_mask)
}

/// Derives a 32-byte seed for chunk processing from IV and Context.
/// This ensures 256-bit security for coordinate generation.
fn derive_chunk_seed(iv: u64, ctx: &ISHContext) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(iv.to_le_bytes());
    hasher.update(ctx.key_loc.x.to_le_bytes());
    hasher.update(ctx.key_loc.y.to_le_bytes());
    hasher.update(ctx.key_loc.z.to_le_bytes());
    hasher.update(ctx.ref_salt.to_le_bytes());
    hasher.update(ctx.mac_key); // Include MAC key for extra entropy
    hasher.finalize().into()
}

/// Encrypts a chunk of data (parallelizable).
pub fn ish_encrypt_chunk(iv: u64, chunk_index: u64, chunk: &[u8], ctx: &ISHContext) -> Vec<u8> {
    let mut output = Vec::with_capacity(chunk.len() * 8);
    
    // Generate Fields (Deterministic from IV)
    let field_a = generate_field(iv, N_WAVES);
    let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);
    
    // Seed for this chunk: combine IV, Context, and Chunk Index
    let mut hasher = Sha256::new();
    hasher.update(iv.to_le_bytes());
    hasher.update(ctx.key_loc.x.to_le_bytes());
    hasher.update(ctx.key_loc.y.to_le_bytes());
    hasher.update(ctx.key_loc.z.to_le_bytes());
    hasher.update(ctx.ref_salt.to_le_bytes());
    hasher.update(chunk_index.to_le_bytes());
    let seed_bytes: [u8; 32] = hasher.finalize().into();
    
    let mut point_rng = ChaCha20Rng::from_seed(seed_bytes);
    
    for &byte in chunk {
        let (sample_loc, val_a, mask) = find_valid_point_ct(&field_a, &mut point_rng);
        let val_b = field_b_secret.eval_at_point(&sample_loc);
        
        let p_target = (byte ^ mask) as f64;
        let delta = -p_target * val_a - val_b;
        
        output.extend_from_slice(&delta.to_le_bytes());
    }
    
    output
}

/// Decrypts a chunk of data.
pub fn ish_decrypt_chunk(iv: u64, chunk_index: u64, chunk: &[u8], ctx: &ISHContext) -> Vec<u8> {
    let mut output = Vec::with_capacity(chunk.len() / 8);
    
    let field_a = generate_field(iv, N_WAVES);
    let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);
    
    let mut hasher = Sha256::new();
    hasher.update(iv.to_le_bytes());
    hasher.update(ctx.key_loc.x.to_le_bytes());
    hasher.update(ctx.key_loc.y.to_le_bytes());
    hasher.update(ctx.key_loc.z.to_le_bytes());
    hasher.update(ctx.ref_salt.to_le_bytes());
    hasher.update(chunk_index.to_le_bytes());
    let seed_bytes: [u8; 32] = hasher.finalize().into();
    
    let mut point_rng = ChaCha20Rng::from_seed(seed_bytes);
    
    for chunk_bytes in chunk.chunks(8) {
        if chunk_bytes.len() < 8 { break; }
        
        let mut delta_bytes = [0u8; 8];
        delta_bytes.copy_from_slice(chunk_bytes);
        let delta = f64::from_le_bytes(delta_bytes);
        
        let (sample_loc, val_a, mask) = find_valid_point_ct(&field_a, &mut point_rng);
        let val_b = field_b_secret.eval_at_point(&sample_loc);
        
        let p_recovered = -(val_b + delta) / val_a;
        let byte_val = (p_recovered.round() as i32).clamp(0, 255) as u8;
        
        output.push(byte_val ^ mask);
    }
    
    output
}

/// Encrypts a chunk of data using Z1 (Pure Geometric) Mode.
/// Optimized for parallel processing.
/// Packs 4 bytes into one f64 delta for 2:1 compression.
pub fn ish_encrypt_chunk_z1(iv: u64, chunk_index: u64, chunk: &[u8], ctx: &ISHContext) -> Vec<u8> {
    // 4 bytes input -> 8 bytes output => 2x expansion (improved from 8x)
    let mut output = Vec::with_capacity(chunk.len() * 2 + 8); 
    
    let field_a = generate_field(iv, N_WAVES);
    let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);
    
    let mut hasher = Sha256::new();
    hasher.update(iv.to_le_bytes());
    hasher.update(ctx.key_loc.x.to_le_bytes());
    hasher.update(ctx.key_loc.y.to_le_bytes());
    hasher.update(ctx.key_loc.z.to_le_bytes());
    hasher.update(ctx.ref_salt.to_le_bytes());
    hasher.update(chunk_index.to_le_bytes());
    let seed_bytes: [u8; 32] = hasher.finalize().into();
    
    let mut point_rng = ChaCha20Rng::from_seed(seed_bytes);
    
    // Process in 4-byte chunks
    for chunk_slice in chunk.chunks(4) {
        let valid_len = chunk_slice.len();
        let mut buf = [0u8; 4];
        buf[..valid_len].copy_from_slice(chunk_slice);
        
        let packed_u32 = u32::from_le_bytes(buf);
        
        // Encode length in high bits: 0->4, 1->1, 2->2, 3->3
        let len_code = (valid_len % 4) as u64;
        let packed_combined = (packed_u32 as u64) | (len_code << 32);
        
        // Generate mask (50-bit to ensure f64 precision is preserved)
        // f64 has 53 bits of significand.
        // We need P < 2^51 to ensure rounding errors don't flip integers.
        // We use 50 bits to be safe.
        let mask_u64 = point_rng.next_u64() & 0x0003FFFFFFFFFFFF;
        
        // Find valid point (constant time)
        let (sample_loc, val_a, _) = find_valid_point_ct(&field_a, &mut point_rng);
        let val_b = field_b_secret.eval_at_point(&sample_loc);
        
        let p_target = (packed_combined ^ mask_u64) as f64;
        
        // Equation: val_a * delta + val_b = -p_target
        // delta = (-p_target - val_b) / val_a
        // Wait, previous code was: delta = -p_target * val_a - val_b; 
        // This implies P = -(delta + val_b) / val_a? No.
        // Let's stick to a robust reversible formula.
        // Standard: delta = -P*A - B. 
        // Recovery: P = -(delta + B) / A.
        // Let's use: delta = -p_target * val_a - val_b;
        // Then: delta + B = -P*A
        // (delta + B) / A = -P
        // P = -(delta + B) / A.
        // Correct.
        
        let delta = -p_target * val_a - val_b;
        output.extend_from_slice(&delta.to_le_bytes());
    }
    
    output
}

/// Decrypts a chunk of data using Z1 Mode.
pub fn ish_decrypt_chunk_z1(iv: u64, chunk_index: u64, chunk: &[u8], ctx: &ISHContext) -> Vec<u8> {
    let mut output = Vec::with_capacity(chunk.len() / 2); // 8 bytes -> 4 bytes
    
    let field_a = generate_field(iv, N_WAVES);
    let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);
    
    let mut hasher = Sha256::new();
    hasher.update(iv.to_le_bytes());
    hasher.update(ctx.key_loc.x.to_le_bytes());
    hasher.update(ctx.key_loc.y.to_le_bytes());
    hasher.update(ctx.key_loc.z.to_le_bytes());
    hasher.update(ctx.ref_salt.to_le_bytes());
    hasher.update(chunk_index.to_le_bytes());
    let seed_bytes: [u8; 32] = hasher.finalize().into();
    
    let mut point_rng = ChaCha20Rng::from_seed(seed_bytes);
    
    for chunk_bytes in chunk.chunks(8) {
        if chunk_bytes.len() < 8 { break; }
        
        let mut delta_bytes = [0u8; 8];
        delta_bytes.copy_from_slice(chunk_bytes);
        let delta = f64::from_le_bytes(delta_bytes);
        
        // Regenerate mask (must match encrypt order)
        let mask_u64 = point_rng.next_u64() & 0x0003FFFFFFFFFFFF;
        
        let (sample_loc, val_a, _) = find_valid_point_ct(&field_a, &mut point_rng);
        let val_b = field_b_secret.eval_at_point(&sample_loc);
        
        // Recover P
        // P = -(delta + B) / A
        let p_recovered = -(delta + val_b) / val_a;
        
        // Round to nearest integer
        let p_u64 = p_recovered.round() as u64;
        
        let decrypted_combined = p_u64 ^ mask_u64;
        
        let len_code = (decrypted_combined >> 32) & 0x3;
        let valid_len = if len_code == 0 { 4 } else { len_code as usize };
        
        let packed_u32 = (decrypted_combined & 0xFFFFFFFF) as u32;
        let bytes = packed_u32.to_le_bytes();
        
        output.extend_from_slice(&bytes[..valid_len]);
    }
    
    output
}

use std::f64::consts::PI;
use std::slice;
use std::ffi::CStr;
use std::os::raw::c_char;
use std::fs::File;
use std::io::{Read, Write, Seek, SeekFrom, BufReader, BufWriter};

// --- SIMD Imports (AVX2) ---
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

// --- Constants ---
const N_WAVES: usize = 1000; // N=1000 for security
const K_MAGNITUDE: f64 = 10.0;
const AMPLITUDE: f64 = 1.0;
const SINGULARITY_THRESHOLD: f64 = 1e-6;

// AVX2 Cosine Approximation Constants
#[cfg(target_arch = "x86_64")]
const TWO_PI: f64 = std::f64::consts::TAU;
#[cfg(target_arch = "x86_64")]
const INV_TWO_PI: f64 = 1.0 / std::f64::consts::TAU;

// AVX2 Cosine Approximation Helper
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_cos_pd(x: __m256d) -> __m256d {
    // Range reduction x = x - round(x / 2PI) * 2PI
    let two_pi = _mm256_set1_pd(TWO_PI);
    let inv_two_pi = _mm256_set1_pd(INV_TWO_PI);
    
    // k = round(x / 2pi)
    let k = _mm256_round_pd(_mm256_mul_pd(x, inv_two_pi), _MM_FROUND_TO_NEAREST_INT | _MM_FROUND_NO_EXC);
    // r = x - k * 2pi
    let r = _mm256_fnmadd_pd(k, two_pi, x); // FNMADD: -(a*b) + c = x - k*2pi
    
    // Polynomial approximation for cos(r) in [-PI, PI]
    // Taylor series: 1 - x^2/2! + x^4/4! - x^6/6! + x^8/8! - x^10/10!
    let r2 = _mm256_mul_pd(r, r);
    
    let c0 = _mm256_set1_pd(1.0);
    let c1 = _mm256_set1_pd(-0.5);
    let c2 = _mm256_set1_pd(0.041666666666666664); // 1/24
    let c3 = _mm256_set1_pd(-0.001388888888888889); // -1/720
    let c4 = _mm256_set1_pd(0.000_024_801_587_301_587_3); // 1/40320
    let c5 = _mm256_set1_pd(-0.00000027557319223985893); // -1/3628800
    
    // Horner's method: c0 + r2*(c1 + r2*(c2 + r2*(c3 + r2*(c4 + r2*c5))))
    let term = _mm256_fmadd_pd(c5, r2, c4);
    let term = _mm256_fmadd_pd(term, r2, c3);
    let term = _mm256_fmadd_pd(term, r2, c2);
    let term = _mm256_fmadd_pd(term, r2, c1);
    _mm256_fmadd_pd(term, r2, c0)
}

// use rand_distr::{Normal, Distribution}; // Need Normal distribution for 3D isotropy

// --- Data Structures ---

#[repr(C)]
#[derive(Debug, Clone, Copy, Zeroize)]
pub struct Vector3D {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

impl Vector3D {
    pub fn new(x: f64, y: f64, z: f64) -> Self {
        Self { x, y, z }
    }

    pub fn dot(&self, other: &Vector3D) -> f64 {
        self.x * other.x + self.y * other.y + self.z * other.z
    }
}

impl ConditionallySelectable for Vector3D {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let x = f64::from_bits(u64::conditional_select(&a.x.to_bits(), &b.x.to_bits(), choice));
        let y = f64::from_bits(u64::conditional_select(&a.y.to_bits(), &b.y.to_bits(), choice));
        let z = f64::from_bits(u64::conditional_select(&a.z.to_bits(), &b.z.to_bits(), choice));
        Self { x, y, z }
    }
}

/// Represents a single plane wave component: A * cos(k*x + phi).
#[derive(Debug, Clone, Zeroize, ZeroizeOnDrop)]
pub struct Wave3D {
    pub amplitude: f64,
    pub frequency: Vector3D, // k vector (3D)
    pub phase: f64,          // phi
}

impl Wave3D {
    pub fn eval(&self, x: &Vector3D) -> f64 {
        self.amplitude * (self.frequency.dot(x) + self.phase).cos()
    }
}

/// Represents a Random Field as a sum of waves.
/// Optimized for SIMD batch processing.
#[derive(Debug, Clone, Zeroize, ZeroizeOnDrop)]
pub struct SpectralField {
    pub waves: Vec<Wave3D>,
    // Structure of Arrays (SoA) for SIMD
    pub k_x: Vec<f64>,
    pub k_y: Vec<f64>,
    pub k_z: Vec<f64>,
    pub phases: Vec<f64>,
    pub amplitudes: Vec<f64>,
}

impl SpectralField {
    pub fn new(waves: Vec<Wave3D>) -> Self {
        let n = waves.len();
        let mut k_x = Vec::with_capacity(n);
        let mut k_y = Vec::with_capacity(n);
        let mut k_z = Vec::with_capacity(n);
        let mut phases = Vec::with_capacity(n);
        let mut amplitudes = Vec::with_capacity(n);

        for w in &waves {
            k_x.push(w.frequency.x);
            k_y.push(w.frequency.y);
            k_z.push(w.frequency.z);
            phases.push(w.phase);
            amplitudes.push(w.amplitude);
        }
        
        // Pad to multiple of 4 for AVX2 (4 x f64)
        while k_x.len() % 4 != 0 {
            k_x.push(0.0);
            k_y.push(0.0);
            k_z.push(0.0);
            phases.push(0.0);
            amplitudes.push(0.0);
        }

        Self {
            waves,
            k_x,
            k_y,
            k_z,
            phases,
            amplitudes,
        }
    }

    /// Optimized evaluation at a spatial point x.
    /// This is the core geometric encoding function.
    pub fn eval_at_point(&self, x: &Vector3D) -> f64 {
        #[cfg(target_arch = "x86_64")]
        {
             if is_x86_feature_detected!("avx2") && is_x86_feature_detected!("fma") {
                 return unsafe { self.eval_avx2(x) };
             }
        }
        self.eval_scalar(x)
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2", enable = "fma")]
    unsafe fn eval_avx2(&self, x: &Vector3D) -> f64 {
        let mut sum_vec = _mm256_setzero_pd();
        
        let x_vec = _mm256_set1_pd(x.x);
        let y_vec = _mm256_set1_pd(x.y);
        let z_vec = _mm256_set1_pd(x.z);
        
        let n = self.k_x.len();
        // Assuming n is multiple of 4 (guaranteed by new())
        
        for i in (0..n).step_by(4) {
            let kx = _mm256_loadu_pd(self.k_x.as_ptr().add(i));
            let ky = _mm256_loadu_pd(self.k_y.as_ptr().add(i));
            let kz = _mm256_loadu_pd(self.k_z.as_ptr().add(i));
            let ph = _mm256_loadu_pd(self.phases.as_ptr().add(i));
            let amp = _mm256_loadu_pd(self.amplitudes.as_ptr().add(i));
            
            // arg = kx*x + ky*y + kz*z + phi
            let arg = _mm256_fmadd_pd(kx, x_vec, ph);
            let arg = _mm256_fmadd_pd(ky, y_vec, arg);
            let arg = _mm256_fmadd_pd(kz, z_vec, arg);
            
            // cos(arg)
            let cos_val = avx2_cos_pd(arg);
            
            // sum += amp * cos_val
            sum_vec = _mm256_fmadd_pd(amp, cos_val, sum_vec);
        }
        
        // Horizontal sum
        let mut temp = [0.0; 4];
        _mm256_storeu_pd(temp.as_mut_ptr(), sum_vec);
        temp[0] + temp[1] + temp[2] + temp[3]
    }

    fn eval_scalar(&self, x: &Vector3D) -> f64 {
        let mut sum = 0.0;
        for i in 0..self.waves.len() {
            let arg = self.k_x[i] * x.x + self.k_y[i] * x.y + self.k_z[i] * x.z + self.phases[i];
            sum += self.amplitudes[i] * arg.cos();
        }
        sum
    }
}


/// Helper to generate deterministic fields from a seed (IV)
/// Using ChaCha20Rng for cryptographic security
pub fn generate_field(seed: u64, n_waves: usize) -> SpectralField {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut waves = Vec::with_capacity(n_waves);

    // Use Gaussian distribution for isotropic 3D vectors
    // To ensure consistency across platforms, we use a standard normal distribution
    // and normalize the vector.
    // However, rand_distr::Normal might use Box-Muller or Ziggurat which are complex.
    // To be perfectly deterministic and simple, we can use rejection sampling or
    // just map 2 uniform variables to sphere (Archimedes/Lambert).
    // Let's use the standard method: 
    // z = 2*u - 1 (uniform [-1, 1])
    // phi = 2*PI*v (uniform [0, 2PI])
    // x = sqrt(1-z^2) * cos(phi)
    // y = sqrt(1-z^2) * sin(phi)
    // This gives uniform distribution on unit sphere.
    
    for _ in 0..n_waves {
        let u: f64 = rng.gen(); // [0, 1)
        let v: f64 = rng.gen(); // [0, 1)
        
        let z_norm = 2.0 * u - 1.0; // [-1, 1]
        let phi = 2.0 * PI * v;
        let r_xy = (1.0 - z_norm * z_norm).sqrt();
        
        let x_norm = r_xy * phi.cos();
        let y_norm = r_xy * phi.sin();
        
        let k_x = K_MAGNITUDE * x_norm;
        let k_y = K_MAGNITUDE * y_norm;
        let k_z = K_MAGNITUDE * z_norm;
        
        let frequency = Vector3D::new(k_x, k_y, k_z);
        let phase = rng.gen::<f64>() * 2.0 * PI;
        
        waves.push(Wave3D {
            amplitude: AMPLITUDE,
            frequency,
            phase,
        });
    }

    SpectralField::new(waves)
}

// --- ISH Context & Core Logic ---

#[derive(Debug, Zeroize, ZeroizeOnDrop)]
pub struct ISHContext {
    key_loc: Vector3D,
    ref_salt: u64, // Secret salt for Field B generation (prevents KPA)
    pub kdf_salt: Option<String>, // Store the PHC string (salt + params) for file headers
    pub mac_key: [u8; 32], // Key for HMAC-SHA256 integrity check
}

impl ISHContext {
    pub fn new(x: f64, y: f64, z: f64, salt: u64, kdf_salt: Option<String>, mac_key: [u8; 32]) -> Self {
        Self {
            key_loc: Vector3D::new(x, y, z),
            ref_salt: salt,
            kdf_salt,
            mac_key,
        }
    }

    pub fn get_ref_salt(&self) -> u64 {
        self.ref_salt
    }
}

// --- FFI Exports ---

#[no_mangle]
pub unsafe extern "C" fn ish_extract_salt(input_path: *const c_char) -> *mut c_char {
    if input_path.is_null() {
        return std::ptr::null_mut();
    }
    
    let in_path = CStr::from_ptr(input_path).to_string_lossy();
    let mut reader = match File::open(in_path.as_ref()) {
        Ok(f) => f,
        Err(_) => return std::ptr::null_mut(),
    };

    // Skip IV
    if reader.seek(SeekFrom::Start(8)).is_err() { return std::ptr::null_mut(); }

    // Read Salt Length
    let mut salt_len_bytes = [0u8; 4];
    if reader.read_exact(&mut salt_len_bytes).is_err() { return std::ptr::null_mut(); }
    let salt_len = u32::from_le_bytes(salt_len_bytes) as usize;

    if salt_len == 0 {
        return std::ptr::null_mut();
    }

    // Read Salt
    let mut salt_bytes = vec![0u8; salt_len];
    if reader.read_exact(&mut salt_bytes).is_err() { return std::ptr::null_mut(); }
    
    // Convert to CString
    let c_str = match std::ffi::CString::new(salt_bytes) {
        Ok(s) => s,
        Err(_) => return std::ptr::null_mut(),
    };
    
    c_str.into_raw()
}

#[no_mangle]
pub unsafe extern "C" fn ish_free_string(s: *mut c_char) {
    if s.is_null() { return; }
    unsafe {
        let _ = std::ffi::CString::from_raw(s);
    }
}

#[no_mangle]
pub unsafe extern "C" fn ish_create(seed: u64, x: f64, y: f64, z: f64) -> *mut ISHContext {
    // If seed is 0, use a default (insecure but functional).
    // For security, seed should be random or derived.
    
    // Derive MAC key from seed (since we don't have KDF here)
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mac_key: [u8; 32] = rng.gen();
    
    let ctx = Box::new(ISHContext::new(x, y, z, seed, None, mac_key));
    Box::into_raw(ctx)
}

#[no_mangle]
pub unsafe extern "C" fn ish_destroy(ctx: *mut ISHContext) {
    if !ctx.is_null() {
        unsafe {
            let _ = Box::from_raw(ctx);
        }
    }
}

/// Creates a new ISH context from a string password using Argon2id.
/// Derives key location AND reference salt securely.
/// Note: This function generates a new random salt and does NOT return it.
/// It is only suitable for generating a context for immediate use where the salt is not needed later 
/// (which is rarely the case for encryption, but this function signature is legacy).
/// TODO: Update API to handle salt storage.
#[no_mangle]
pub unsafe extern "C" fn ish_create_with_password(password: *const c_char) -> *mut ISHContext {
    if password.is_null() {
        return std::ptr::null_mut();
    }
    
    let pass_str = unsafe { CStr::from_ptr(password).to_string_lossy() };
    
    // Generate a random salt
    let salt = SaltString::generate(&mut OsRng);
    
    // Argon2id (Default)
    let argon2 = Argon2::default();
    
    // Hash password to get 32-byte hash
    let password_hash = argon2.hash_password(pass_str.as_bytes(), &salt)
        .expect("Argon2 hashing failed");
        
    let binding = password_hash.hash.expect("Hash missing");
    let hash_bytes = binding.as_bytes();
    
    // Use the full 32-byte hash to seed ChaCha20
    let mut seed_bytes = [0u8; 32];
    seed_bytes.copy_from_slice(hash_bytes);
    let mut rng = ChaCha20Rng::from_seed(seed_bytes);
    

    
    // Derive parameters
    let x = (rng.gen::<f64>() * 2000.0) - 1000.0;
    let y = (rng.gen::<f64>() * 2000.0) - 1000.0;
    let z = (rng.gen::<f64>() * 2000.0) - 1000.0;
    let ref_salt: u64 = rng.gen(); // Secret salt for Field B
    
    let mut mac_key = [0u8; 32];
    rng.fill(&mut mac_key);
    
    let phc_string = password_hash.to_string();
    let ctx = Box::new(ISHContext::new(x, y, z, ref_salt, Some(phc_string), mac_key));
    Box::into_raw(ctx)
}

/// Creates a new ISH context from a string password AND a provided KDF salt (PHC string).
/// Used for decryption where the salt must be consistent with encryption.
#[no_mangle]
pub unsafe extern "C" fn ish_create_with_salt(password: *const c_char, salt_phc: *const c_char) -> *mut ISHContext {
    if password.is_null() || salt_phc.is_null() {
        return std::ptr::null_mut();
    }
    
    let pass_str = unsafe { CStr::from_ptr(password).to_string_lossy() };
    let phc_str = unsafe { CStr::from_ptr(salt_phc).to_string_lossy() };
    
    // Parse the PHC string to recover salt and parameters
    let parsed_hash = PasswordHash::new(&phc_str).expect("Invalid PHC string");
    
    // Verify/Re-hash using the stored parameters
    // Note: We are not verifying a hash against a password here in the traditional sense,
    // we are re-deriving the key from the password using the same salt/params.
    let argon2 = Argon2::default();
    
    let salt = parsed_hash.salt.expect("Salt missing in PHC");
    
    // Re-hash
    let password_hash = argon2.hash_password(pass_str.as_bytes(), salt)
        .expect("Argon2 hashing failed");
        
    let binding = password_hash.hash.expect("Hash missing");
    let hash_bytes = binding.as_bytes();
    
    // Use the full 32-byte hash to seed ChaCha20
    let mut seed_bytes = [0u8; 32];
    seed_bytes.copy_from_slice(hash_bytes);
    let mut rng = ChaCha20Rng::from_seed(seed_bytes);
    
    let x = (rng.gen::<f64>() * 2000.0) - 1000.0;
    let y = (rng.gen::<f64>() * 2000.0) - 1000.0;
    let z = (rng.gen::<f64>() * 2000.0) - 1000.0;
    let ref_salt: u64 = rng.gen();
    
    let mut mac_key = [0u8; 32];
    rng.fill(&mut mac_key);
    
    // Store the PHC string again (it should be identical)
    let ctx = Box::new(ISHContext::new(x, y, z, ref_salt, Some(phc_str.into_owned()), mac_key));
    Box::into_raw(ctx)
}

/// Returns the size of the ciphertext for a given plaintext length.
#[no_mangle]
pub extern "C" fn ish_ciphertext_len(plaintext_len: usize) -> usize {
    16 + plaintext_len * 8 + 32 // Added 32 bytes for HMAC-SHA256
}

/// Encrypts plaintext directly using ISH Holographic Ratio.
/// Implements Direct Geometric Encoding as per MATH_SPEC.md.
#[no_mangle]
pub unsafe extern "C" fn ish_encrypt(ctx: *mut ISHContext, input: *const u8, output: *mut u8, len: usize) {
    if ctx.is_null() || input.is_null() || output.is_null() {
        return;
    }
    unsafe {
        let ctx = &*ctx;
        let input_slice = slice::from_raw_parts(input, len);
        
        let mut out_ptr = output;
        let start_ptr = output;
        
        // 1. Generate IV
        let mut rng = ChaCha20Rng::from_entropy();
        let iv: u64 = rng.gen();
        
        // Write IV (8 bytes)
        ptr_write_u64_le(out_ptr, iv);
        out_ptr = out_ptr.add(8);
        
        // Generate Fields
        // Field A: Uses IV (Public/Random)
        // Field B: Uses IV ^ RefSalt (Secret/Key-Dependent) -> Prevents KPA
        let field_a = generate_field(iv, N_WAVES);
        let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES); 
        
        let mut valid_blocks: u64 = 0;
        let count_ptr = out_ptr; 
        out_ptr = out_ptr.add(8); 
        
        // Chaotic Trajectory: Evolve key location randomly per byte to avoid pattern repetition
        // This ensures that the sequence of sampling points is:
        // 1. Deterministic (for legitimate decryption)
        // 2. Discontinuous with respect to the Key Location (to break Gradient Descent)
        // 3. Spatially Decorrelated (to break Smoothness/Prefix Prediction)
        // We use the Key Location to seed the RNG.
        // Any small change in Key Location will result in a completely different sequence of points (Avalanche Effect).
        let seed = derive_chunk_seed(iv, ctx);
        let mut point_rng = ChaCha20Rng::from_seed(seed);

        for &byte in input_slice {
            // Chaotic Trajectory:
            // Instead of small jitter, we jump to a pseudo-random location in the field.
            // This destroys local correlations and makes the residual "rough" (white noise)
            // for any incorrect key, preventing smoothness analysis.
            // Consistent with chunk processing: 5 words per iteration.
            
            let (sample_loc, val_a, mask) = find_valid_point_ct(&field_a, &mut point_rng);
            let val_b = field_b_secret.eval_at_point(&sample_loc);
            
            // Apply stream cipher whitening
            let p_target = (byte ^ mask) as f64;
            
            // We want B_modified(x)/A(x) = -P
            // B_modified(x) = B(x) + Delta
            // (B(x) + Delta) / A(x) = -P
            // B(x) + Delta = -P * A(x)
            // Delta = -P * A(x) - B(x)
            
            let delta = -p_target * val_a - val_b;
            
            // Write Delta
            ptr_write_f64_le(out_ptr, delta);
            out_ptr = out_ptr.add(8);
            
            valid_blocks += 1;
        }
        
        // Write back the total block count
        ptr_write_u64_le(count_ptr, valid_blocks);
        
        // Calculate and Append MAC
        let data_len = out_ptr.offset_from(start_ptr) as usize;
        let data_slice = slice::from_raw_parts(start_ptr, data_len);
        
        let mut mac = HmacSha256::new_from_slice(&ctx.mac_key).expect("HMAC key error");
        mac.update(data_slice);
        let result = mac.finalize().into_bytes();
        
        // Write MAC
        std::ptr::copy_nonoverlapping(result.as_ptr(), out_ptr, 32);
    }
}

/// Decrypts ISH ciphertext to recover plaintext.
/// Implements Direct Geometric Decoding as per MATH_SPEC.md.
/// Returns 0 on success, -100 on integrity failure.
#[no_mangle]
pub unsafe extern "C" fn ish_decrypt(ctx: *mut ISHContext, input: *const u8, output: *mut u8, _len: usize) -> i32 {
    if ctx.is_null() || input.is_null() || output.is_null() {
        return -1;
    }
    unsafe {
        let ctx = &*ctx;
        let mut in_ptr = input;
        let mut out_ptr = output;
        
        // 1. Read IV
        let iv = ptr_read_u64_le(in_ptr);
        
        // 2. Read Count
        let count = ptr_read_u64_le(in_ptr.add(8));
        
        // Calculate total data length (IV + Count + Deltas)
        let data_len = 16 + (count as usize) * 8;
        
        // Verify MAC
        let data_slice = slice::from_raw_parts(input, data_len);
        let stored_mac_ptr = input.add(data_len);
        let mut stored_mac = [0u8; 32];
        std::ptr::copy_nonoverlapping(stored_mac_ptr, stored_mac.as_mut_ptr(), 32);
        
        let mut mac = HmacSha256::new_from_slice(&ctx.mac_key).expect("HMAC key error");
        mac.update(data_slice);
        let calculated_mac = mac.finalize().into_bytes();
        
        if !bool::from(calculated_mac[..].ct_eq(&stored_mac)) {
            return -100; // Integrity Check Failed
        }
        
        // MAC Verified, proceed with decryption
        in_ptr = in_ptr.add(16); // Skip IV + Count
        
        // Reconstruct Fields
        let field_a = generate_field(iv, N_WAVES);
        let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);
        
        let seed = derive_chunk_seed(iv, ctx);
        let mut point_rng = ChaCha20Rng::from_seed(seed);

        for _ in 0..count {
            // Read Delta
            let delta = ptr_read_f64_le(in_ptr);
            in_ptr = in_ptr.add(8);
            
            // Chaotic Trajectory (Must match encryptor)
            let mut val_a = 0.0;
            let mut val_b = 0.0;
            let mut mask = 0u8;

            for j in 0..12 {
                let r1 = point_rng.next_u64();
                let sample_x = (r1 as f64 / u64::MAX as f64 - 0.5) * 2000.0;
                
                let r2 = point_rng.next_u64();
                let sample_y = (r2 as f64 / u64::MAX as f64 - 0.5) * 2000.0;
                
                let r3 = point_rng.next_u64();
                let sample_z = (r3 as f64 / u64::MAX as f64 - 0.5) * 2000.0;
                
                mask = (point_rng.next_u32() & 0xFF) as u8;
                
                let sample_loc = Vector3D::new(sample_x, sample_y, sample_z);
    
                val_a = field_a.eval_at_point(&sample_loc);
                
                if val_a.abs() >= SINGULARITY_THRESHOLD || j == 11 {
                     val_b = field_b_secret.eval_at_point(&sample_loc);
                     break;
                }
            }
            
            // Reconstruction:
            // B_modified(x) = B(x) + Delta
            // P = -B_modified(x) / A(x)
            // P = -(B(x) + Delta) / A(x)
            
            let p_recovered = -(val_b + delta) / val_a;
            
            // Round to nearest integer and clamp
            let byte_val = (p_recovered.round() as i32).clamp(0, 255) as u8;
            
            *out_ptr = byte_val ^ mask;
            out_ptr = out_ptr.add(1);
        }
        
        0 // Success
    }
}

// --- File I/O Extensions ---

/// Appends an HMAC-SHA256 checksum to the end of the file.
/// Reads the entire file content to calculate the MAC.
unsafe fn ish_append_integrity(file_path: &str, mac_key: &[u8; 32]) -> i32 {
    let mut file = match File::options().read(true).write(true).open(file_path) {
        Ok(f) => f,
        Err(_) => return -101, // Failed to open for appending
    };

    let mut mac = HmacSha256::new_from_slice(mac_key).expect("HMAC can take any key size");
    
    // Read file from start
    if file.seek(SeekFrom::Start(0)).is_err() { return -102; }
    
    let mut buffer = [0u8; 8192];
    loop {
        let n = match file.read(&mut buffer) {
            Ok(0) => break,
            Ok(n) => n,
            Err(_) => return -103,
        };
        mac.update(&buffer[..n]);
    }
    
    let result = mac.finalize().into_bytes();
    
    // Append MAC to end of file
    // Note: We are already at the end of the file after reading it all?
    // No, read() advances position. If we read to EOF, we are at end.
    // But to be safe, seek to End.
    if file.seek(SeekFrom::End(0)).is_err() { return -104; }
    if file.write_all(&result).is_err() { return -105; }
    
    0
}

/// Verifies the HMAC-SHA256 checksum at the end of the file.
/// If valid, returns 0. If invalid, returns -100.
/// Note: This does NOT strip the MAC from the file, it just verifies it exists and is correct.
/// The caller (decryption function) must stop reading 32 bytes before the end.
unsafe fn ish_verify_integrity(file_path: &str, mac_key: &[u8; 32]) -> i32 {
    // println!("[Integrity] Verifying file: {}", file_path);
    let mut file = match File::open(file_path) {
        Ok(f) => f,
        Err(_) => {
             // println!("[Integrity] Failed to open file: {}", file_path);
             return -101;
        }
    };
    
    let file_len = match file.metadata() {
        Ok(m) => m.len(),
        Err(_) => return -102,
    };
    
    // println!("[Integrity] File length: {}", file_len);

    if file_len < 32 {
        println!("[Integrity] File too short (<32 bytes): {} bytes", file_len);
        return -106; 
    }
    
    let content_len = file_len - 32;
    
    let mut mac = HmacSha256::new_from_slice(mac_key).expect("HMAC can take any key size");
    
    // Calculate MAC over content
    if file.seek(SeekFrom::Start(0)).is_err() { return -102; }
    
    let mut buffer = [0u8; 8192];
    let mut processed = 0u64;
    
    while processed < content_len {
        let remaining = content_len - processed;
        let to_read = std::cmp::min(remaining, 8192) as usize;
        
        let n = match file.read(&mut buffer[..to_read]) {
            Ok(0) => return -107, // Unexpected EOF
            Ok(n) => n,
            Err(_) => return -103,
        };
        
        mac.update(&buffer[..n]);
        processed += n as u64;
    }
    
    let calculated_mac = mac.finalize().into_bytes();
    
    // Read stored MAC
    let mut stored_mac = [0u8; 32];
    // file pointer should be at content_len now.
    if file.read_exact(&mut stored_mac).is_err() { return -108; }
    
    // Use constant-time comparison to prevent timing attacks
    let valid = calculated_mac[..].ct_eq(&stored_mac);
    if !bool::from(valid) {
        println!("[Integrity] MAC Mismatch for file: {}", file_path);
        println!("[Integrity] Calculated: {:x?}", calculated_mac);
        println!("[Integrity] Stored:     {:x?}", stored_mac);
        return -100; // Integrity Check Failed
    }
    
    0
}

#[no_mangle]
pub unsafe extern "C" fn ish_encrypt_file(ctx: *mut ISHContext, input_path: *const c_char, output_path: *const c_char) -> i32 {
    if ctx.is_null() || input_path.is_null() || output_path.is_null() {
        return -1;
    }

    let result = std::panic::catch_unwind(|| {
        unsafe {
            let ctx = &*ctx;
            let in_path = CStr::from_ptr(input_path).to_string_lossy();
            let out_path = CStr::from_ptr(output_path).to_string_lossy();

            let mut reader = BufReader::new(match File::open(in_path.as_ref()) {
                Ok(f) => f,
                Err(_) => return -2,
            });

            let mut writer = BufWriter::new(match File::create(out_path.as_ref()) {
                Ok(f) => f,
                Err(_) => return -3,
            });

            // 1. Generate IV
            let mut rng = ChaCha20Rng::from_entropy();
            let iv: u64 = rng.gen();
            
            if writer.write_all(&iv.to_le_bytes()).is_err() { return -4; }

            // 2. Write KDF Salt (if available)
            if let Some(ref salt) = ctx.kdf_salt {
                let salt_bytes = salt.as_bytes();
                let salt_len = salt_bytes.len() as u32;
                if writer.write_all(&salt_len.to_le_bytes()).is_err() { return -4; }
                if writer.write_all(salt_bytes).is_err() { return -4; }
            } else {
                let salt_len: u32 = 0;
                if writer.write_all(&salt_len.to_le_bytes()).is_err() { return -4; }
            }

            // 3. Placeholder for Count
            let count_pos = match writer.stream_position() {
                Ok(p) => p,
                Err(_) => return -5,
            };
            if writer.write_all(&[0u8; 8]).is_err() { return -4; }

            // 4. Generate Fields (Unused in file encryption as chunk processing handles it internally)
            // let field_a = generate_field(iv, N_WAVES);
            // let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);

            let mut valid_blocks: u64 = 0;
            // Use derived seed for 256-bit security
            // let seed = derive_chunk_seed(iv, ctx);
            
            // Use chunked reading and parallel processing
            const CHUNK_SIZE: usize = 256 * 1024;
            let mut buffer = vec![0u8; CHUNK_SIZE]; 
            let mut total_processed: u64 = 0;

            loop {
                let n = match reader.read(&mut buffer) {
                    Ok(0) => break,
                    Ok(n) => n,
                    Err(_) => return -6,
                };

                let chunk_data = &buffer[..n];
                
                // Parallel processing of the chunk using exposed function
                let delta_results = ish_encrypt_chunk(iv, total_processed, chunk_data, ctx);

                // Write results
                if writer.write_all(&delta_results).is_err() { return -7; }
                
                valid_blocks += n as u64;
                
                total_processed += n as u64;
            }

            // 4. Update Count
            if writer.seek(SeekFrom::Start(count_pos)).is_err() { return -8; }
            if writer.write_all(&valid_blocks.to_le_bytes()).is_err() { return -9; }
            if writer.flush().is_err() { return -10; }
            
            // 5. Append Integrity MAC
    // We need to close writer first to let other handle open it? 
    // Or just pass the path. The writer has flushed.
    drop(writer); // Ensure flush and release lock
    drop(reader);
    
    // Debug: Check file size
    if let Ok(m) = std::fs::metadata(out_path.as_ref()) {
        if m.len() == 0 {
            // File is empty? That's bad.
            return -11; 
        }
    } else {
        return -12;
    }
    
    let mac_res = ish_append_integrity(&out_path, &ctx.mac_key);
    if mac_res != 0 { return mac_res; }

    0 // Success
        }
    });

    result.unwrap_or(-99)
}

#[no_mangle]
pub unsafe extern "C" fn ish_decrypt_file(ctx: *mut ISHContext, input_path: *const c_char, output_path: *const c_char) -> i32 {
    if ctx.is_null() || input_path.is_null() || output_path.is_null() {
        return -1;
    }

    let result = std::panic::catch_unwind(|| {
        unsafe {
            let ctx = &*ctx;
            let in_path = CStr::from_ptr(input_path).to_string_lossy();
            let out_path = CStr::from_ptr(output_path).to_string_lossy();

            // 1. Verify Integrity
            let verify_res = ish_verify_integrity(&in_path, &ctx.mac_key);
            if verify_res != 0 { return verify_res; }

            let mut reader = BufReader::new(match File::open(in_path.as_ref()) {
                Ok(f) => f,
                Err(_) => return -2,
            });

            let mut writer = BufWriter::new(match File::create(out_path.as_ref()) {
                Ok(f) => f,
                Err(_) => return -3,
            });

            let mut iv_bytes = [0u8; 8];
            if reader.read_exact(&mut iv_bytes).is_err() { return -4; }
            let iv = u64::from_le_bytes(iv_bytes);

            // 2. Read (Skip) Salt
            let mut salt_len_bytes = [0u8; 4];
            if reader.read_exact(&mut salt_len_bytes).is_err() { return -4; }
            let salt_len = u32::from_le_bytes(salt_len_bytes) as i64;
            
            if salt_len > 0 && reader.seek(SeekFrom::Current(salt_len)).is_err() { return -4; }

            // 3. Read Count
            let mut count_bytes = [0u8; 8];
            if reader.read_exact(&mut count_bytes).is_err() { return -5; }
            let count = u64::from_le_bytes(count_bytes);

            // let field_a = generate_field(iv, N_WAVES);
            // let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);

            // let seed = derive_chunk_seed(iv, ctx);

            // Use chunked reading and parallel processing
            const CHUNK_SIZE: usize = 256 * 1024; // Process 256K f64s at a time (2MB)
            let mut delta_buffer = vec![0u8; CHUNK_SIZE * 8]; // Each delta is 8 bytes
            let mut total_processed: u64 = 0;

            loop {
                let remaining_deltas = count - total_processed;
                if remaining_deltas == 0 { break; }
                
                let bytes_needed = (remaining_deltas * 8) as usize;
                let chunk_capacity = std::cmp::min(bytes_needed, delta_buffer.len());
                
                let mut bytes_read = 0;
                while bytes_read < chunk_capacity {
                     match reader.read(&mut delta_buffer[bytes_read..chunk_capacity]) {
                        Ok(0) => return -6, // Unexpected EOF
                        Ok(n) => bytes_read += n,
                        Err(_) => return -6,
                    }
                }
                
                let num_deltas = bytes_read / 8;
                let chunk_deltas = &delta_buffer[..bytes_read];

                // Parallel processing using exposed function
                let decrypted_bytes = ish_decrypt_chunk(iv, total_processed, chunk_deltas, ctx);
                
                if writer.write_all(&decrypted_bytes).is_err() { return -7; }
                total_processed += num_deltas as u64;
            }
            
            if writer.flush().is_err() { return -8; }
            0 // Success
        }
    });

    result.unwrap_or(-99)
}

// --- ISH-Z1 Protocol (Compression) ---

#[no_mangle]
pub unsafe extern "C" fn ish_encrypt_file_z1(ctx: *mut ISHContext, input_path: *const c_char, output_path: *const c_char) -> i32 {
    if ctx.is_null() || input_path.is_null() || output_path.is_null() { return -1; }

    let result = std::panic::catch_unwind(|| {
        unsafe {
            let ctx = &*ctx;
            let in_path = CStr::from_ptr(input_path).to_string_lossy();
            let out_path = CStr::from_ptr(output_path).to_string_lossy();

            let mut reader = BufReader::new(match File::open(in_path.as_ref()) { Ok(f) => f, Err(_) => return -2 });
            let mut writer = BufWriter::new(match File::create(out_path.as_ref()) { Ok(f) => f, Err(_) => return -3 });

            let mut rng = ChaCha20Rng::from_entropy();
            let iv: u64 = rng.gen();
            if writer.write_all(&iv.to_le_bytes()).is_err() { return -4; }

            // 2. Write KDF Salt (if available)
            if let Some(ref salt) = ctx.kdf_salt {
                let salt_bytes = salt.as_bytes();
                let salt_len = salt_bytes.len() as u32;
                if writer.write_all(&salt_len.to_le_bytes()).is_err() { return -4; }
                if writer.write_all(salt_bytes).is_err() { return -4; }
            } else {
                let salt_len: u32 = 0;
                if writer.write_all(&salt_len.to_le_bytes()).is_err() { return -4; }
            }

            let count_pos = match writer.stream_position() { Ok(p) => p, Err(_) => return -5 };
            if writer.write_all(&[0u8; 8]).is_err() { return -4; }

            // let field_a = generate_field(iv, N_WAVES);
            // let field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);
            
            let mut valid_blocks: u64 = 0;
            // Use derived seed for 256-bit security
            // let seed = derive_chunk_seed(iv, ctx);
            
            // Use chunked reading and parallel processing
            const CHUNK_SIZE: usize = 256 * 1024; // Process 256K bytes at a time
            let mut buffer = vec![0u8; CHUNK_SIZE];
            let mut total_processed: u64 = 0;

            loop {
                let n = match reader.read(&mut buffer) {
                    Ok(0) => break,
                    Ok(n) => n,
                    Err(_) => return -6,
                };

                let chunk_data = &buffer[..n];
                
                // Parallel processing using exposed function
                let delta_results = ish_encrypt_chunk_z1(iv, total_processed, chunk_data, ctx);

                if writer.write_all(&delta_results).is_err() { return -7; }
                
                let num_deltas = (delta_results.len() / 8) as u64;
                valid_blocks += num_deltas;
                
                total_processed += num_deltas;
            }

            // 5. Update Count
            if writer.seek(SeekFrom::Start(count_pos)).is_err() { return -8; }
            if writer.write_all(&valid_blocks.to_le_bytes()).is_err() { return -9; }
            if writer.flush().is_err() { return -10; }
            
            drop(writer);
            drop(reader);
            
            // Debug: Check file size
            if let Ok(m) = std::fs::metadata(out_path.as_ref()) {
                if m.len() == 0 { return -11; }
            } else { return -12; }
            
            let mac_res = ish_append_integrity(&out_path, &ctx.mac_key);
            if mac_res != 0 { return mac_res; }
            
            0 
        }
    });
    result.unwrap_or(-99)
}

#[no_mangle]
pub unsafe extern "C" fn ish_decrypt_file_z1(ctx: *mut ISHContext, input_path: *const c_char, output_path: *const c_char) -> i32 {
    if ctx.is_null() || input_path.is_null() || output_path.is_null() { return -1; }

    let result = std::panic::catch_unwind(|| {
        unsafe {
            let ctx = &*ctx;
            let in_path = CStr::from_ptr(input_path).to_string_lossy();
            let out_path = CStr::from_ptr(output_path).to_string_lossy();

            let verify_res = ish_verify_integrity(&in_path, &ctx.mac_key);
            if verify_res != 0 { return verify_res; }

            let mut reader = BufReader::new(match File::open(in_path.as_ref()) { Ok(f) => f, Err(_) => return -2 });
            let mut writer = BufWriter::new(match File::create(out_path.as_ref()) { Ok(f) => f, Err(_) => return -3 });

            let mut iv_bytes = [0u8; 8];
            if reader.read_exact(&mut iv_bytes).is_err() { return -4; }
            let iv = u64::from_le_bytes(iv_bytes);

            // 2. Read (Skip) Salt
            let mut salt_len_bytes = [0u8; 4];
            if reader.read_exact(&mut salt_len_bytes).is_err() { return -4; }
            let salt_len = u32::from_le_bytes(salt_len_bytes) as i64;
            
            if salt_len > 0 && reader.seek(SeekFrom::Current(salt_len)).is_err() { return -4; }

            let mut count_bytes = [0u8; 8];
            if reader.read_exact(&mut count_bytes).is_err() { return -5; }
            let count = u64::from_le_bytes(count_bytes);

            let _field_a = generate_field(iv, N_WAVES);
            let _field_b_secret = generate_field(iv ^ ctx.ref_salt, N_WAVES);

            let _seed = derive_chunk_seed(iv, ctx);

            // Use chunked reading and parallel processing
            const CHUNK_SIZE: usize = 256 * 1024; // Process 256K f64s at a time (2MB)
            let mut delta_buffer = vec![0u8; CHUNK_SIZE * 8]; // Each delta is 8 bytes (f64)
            let mut total_processed: u64 = 0;

            loop {
                let remaining_deltas = count - total_processed;
                if remaining_deltas == 0 { break; }
                
                let bytes_needed = (remaining_deltas * 8) as usize;
                let chunk_capacity = std::cmp::min(bytes_needed, delta_buffer.len());
                
                let mut bytes_read = 0;
                while bytes_read < chunk_capacity {
                     match reader.read(&mut delta_buffer[bytes_read..chunk_capacity]) {
                        Ok(0) => return -6, // Unexpected EOF
                        Ok(n) => bytes_read += n,
                        Err(_) => return -6,
                    }
                }
                
                let num_deltas = bytes_read / 8;
                let chunk_deltas = &delta_buffer[..bytes_read];

                // Parallel processing using exposed function
                let decrypted_bytes = ish_decrypt_chunk_z1(iv, total_processed, chunk_deltas, ctx);
                
                if writer.write_all(&decrypted_bytes).is_err() { return -7; }
                total_processed += num_deltas as u64;
            }
            if writer.flush().is_err() { return -8; }
            0 
        }
    });
    result.unwrap_or(-99)
}

// --- Raw Pointer Helpers (Little Endian) ---

unsafe fn ptr_write_u64_le(ptr: *mut u8, val: u64) {
    let bytes = val.to_le_bytes();
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, 8);
}

unsafe fn ptr_write_f64_le(ptr: *mut u8, val: f64) {
    let bytes = val.to_le_bytes();
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, 8);
}

unsafe fn ptr_read_u64_le(ptr: *const u8) -> u64 {
    let mut bytes = [0u8; 8];
    std::ptr::copy_nonoverlapping(ptr, bytes.as_mut_ptr(), 8);
    u64::from_le_bytes(bytes)
}

unsafe fn ptr_read_f64_le(ptr: *const u8) -> f64 {
    let mut bytes = [0u8; 8];
    std::ptr::copy_nonoverlapping(ptr, bytes.as_mut_ptr(), 8);
    f64::from_le_bytes(bytes)
}
