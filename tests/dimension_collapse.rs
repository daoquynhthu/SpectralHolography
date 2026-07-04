use spectral_holography::{generate_field, Vector3D};

#[test]
fn test_spatial_complexity() {
    let seed = 12345;
    let n_waves = 1000;
    let field = generate_field(seed, n_waves);
    let center = Vector3D::new(0.0, 0.0, 0.0);
    
    // Sample along x-axis with small step
    let v0 = field.eval_at_point(&center);
    let v1 = field.eval_at_point(&Vector3D::new(0.01, 0.0, 0.0));
    let v2 = field.eval_at_point(&Vector3D::new(0.02, 0.0, 0.0));
    
    // Check non-linearity
    // If linear, v1 - v0 == v2 - v1
    let d1 = v1 - v0;
    let d2 = v2 - v1;
    
    // We expect d1 != d2 (curvature) due to high frequency components
    // 1000 waves should create significant local curvature
    assert!((d1 - d2).abs() > 1e-9, "Field is locally linear! (Low complexity)");
    
    // Also check it's not constant
    assert!(d1.abs() > 1e-9, "Field is locally constant!");
}

#[test]
fn test_gradient_variation() {
    // Verify that gradients change direction (not a single plane wave)
    let seed = 67890;
    let n_waves = 1000;
    let field = generate_field(seed, n_waves);
    
    // Gradient at (0,0,0)
    let p0 = Vector3D::new(0.0, 0.0, 0.0);
    let v0 = field.eval_at_point(&p0);
    let dx = 1e-4;
    let gx0 = (field.eval_at_point(&Vector3D::new(dx, 0.0, 0.0)) - v0) / dx;
    let gy0 = (field.eval_at_point(&Vector3D::new(0.0, dx, 0.0)) - v0) / dx;
    let gz0 = (field.eval_at_point(&Vector3D::new(0.0, 0.0, dx)) - v0) / dx;
    
    // Gradient at (10,10,10)
    let p1 = Vector3D::new(10.0, 10.0, 10.0);
    let v1 = field.eval_at_point(&p1);
    let gx1 = (field.eval_at_point(&Vector3D::new(10.0 + dx, 10.0, 10.0)) - v1) / dx;
    let gy1 = (field.eval_at_point(&Vector3D::new(10.0, 10.0 + dx, 10.0)) - v1) / dx;
    let gz1 = (field.eval_at_point(&Vector3D::new(10.0, 10.0, 10.0 + dx)) - v1) / dx;
    
    // Gradients should be different
    let diff = (gx0 - gx1).abs() + (gy0 - gy1).abs() + (gz0 - gz1).abs();
    assert!(diff > 1e-4, "Gradient is constant! Field is a plane.");
}
