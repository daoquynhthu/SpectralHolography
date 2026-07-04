use criterion::{black_box, criterion_group, criterion_main, Criterion};
use spectral_holography::{
    generate_field, ish_ciphertext_len, ish_create_with_password, ish_decrypt, ish_decrypt_chunk,
    ish_decrypt_chunk_z1, ish_destroy, ish_encrypt, ish_encrypt_chunk, ish_encrypt_chunk_z1,
    ISHContext, SpectralField, Vector3D,
};
use std::ffi::CString;

fn bench_field_generation(c: &mut Criterion) {
    let seed = 12345;
    let n_waves = 1000;
    c.bench_function("generate_field_1000", |b| {
        b.iter(|| generate_field(black_box(seed), black_box(n_waves)))
    });
}

fn bench_field_evaluation(c: &mut Criterion) {
    let seed = 12345;
    let n_waves = 1000;
    let field = generate_field(seed, n_waves);
    let loc = Vector3D::new(10.0, 20.0, 30.0);

    c.bench_function("eval_at_point_avx2", |b| {
        b.iter(|| field.eval_at_point(black_box(&loc)))
    });
}

fn bench_ish_chunk_processing(c: &mut Criterion) {
    let iv = 12345;
    let ctx = ISHContext::new(10.0, 20.0, 30.0, 12345, None, [0u8; 32]);

    // 64KB chunk
    let chunk_size = 64 * 1024;
    let data = vec![0xAAu8; chunk_size];
    let start_index = 0;

    c.bench_function("ish_encrypt_chunk_64kb", |b| {
        b.iter(|| {
            ish_encrypt_chunk(
                black_box(iv),
                black_box(start_index),
                black_box(&data),
                black_box(&ctx),
            )
        })
    });

    // Prepare for decryption benchmark
    let encrypted_bytes = ish_encrypt_chunk(iv, start_index, &data, &ctx);

    c.bench_function("ish_decrypt_chunk_64kb", |b| {
        b.iter(|| {
            ish_decrypt_chunk(
                black_box(iv),
                black_box(start_index),
                black_box(&encrypted_bytes),
                black_box(&ctx),
            )
        })
    });
}

fn bench_ish_z1_chunk_processing(c: &mut Criterion) {
    let iv = 12345;
    let ctx = ISHContext::new(10.0, 20.0, 30.0, 12345, None, [0u8; 32]);

    // 64KB chunk
    let chunk_size = 64 * 1024;
    let data = vec![0xAAu8; chunk_size];
    let start_index = 0;

    c.bench_function("ish_encrypt_chunk_z1_64kb", |b| {
        b.iter(|| {
            ish_encrypt_chunk_z1(
                black_box(iv),
                black_box(start_index),
                black_box(&data),
                black_box(&ctx),
            )
        })
    });

    // Prepare for decryption benchmark
    let encrypted_bytes = ish_encrypt_chunk_z1(iv, start_index, &data, &ctx);

    c.bench_function("ish_decrypt_chunk_z1_64kb", |b| {
        b.iter(|| {
            ish_decrypt_chunk_z1(
                black_box(iv),
                black_box(start_index),
                black_box(&encrypted_bytes),
                black_box(&ctx),
            )
        })
    });
}

criterion_group!(
    benches,
    bench_field_generation,
    bench_field_evaluation,
    bench_ish_chunk_processing,
    bench_ish_z1_chunk_processing
);
criterion_main!(benches);
