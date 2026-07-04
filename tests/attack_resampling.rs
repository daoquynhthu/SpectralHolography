use spectral_holography::{generate_field, Vector3D};

#[test]
fn test_salt_avalanche() {
    // Verify that a small change in salt (derived from password)
    // results in a completely different field (Avalanche Effect).
    let iv = 12345;
    let salt1 = 0x11111111;
    let salt2 = 0x11111112; // 1 bit flip

    // These generate Field B (Secret)
    let field1 = generate_field(iv ^ salt1, 1000);
    let field2 = generate_field(iv ^ salt2, 1000);

    // Sample at the same location
    let p = Vector3D::new(10.0, 10.0, 10.0);
    let v1 = field1.eval_at_point(&p);
    let v2 = field2.eval_at_point(&p);

    println!("v1: {}, v2: {}", v1, v2);

    // Should be completely different (uncorrelated)
    // Range is roughly +/- sqrt(N) * A = +/- 30.
    // Difference should be significant.
    assert!(
        (v1 - v2).abs() > 0.1,
        "Salt avalanche failed! Fields are too similar."
    );
}

#[test]
fn test_iv_diversity() {
    // Verify that different IVs produce different fields
    let iv1 = 12345;
    let iv2 = 12346;

    let field1 = generate_field(iv1, 1000);
    let field2 = generate_field(iv2, 1000);

    let p = Vector3D::new(10.0, 10.0, 10.0);
    let v1 = field1.eval_at_point(&p);
    let v2 = field2.eval_at_point(&p);

    assert!((v1 - v2).abs() > 0.1, "IV diversity failed!");
}
