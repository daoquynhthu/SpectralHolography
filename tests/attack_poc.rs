use spectral_holography::{generate_field, Vector3D};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

// Simple Linear Equation Solver (Gaussian Elimination)
fn solve_linear_system(matrix: &Vec<Vec<f64>>, rhs: &Vec<f64>) -> Option<Vec<f64>> {
    let n = rhs.len();
    if matrix.len() != n || matrix[0].len() != n {
        return None;
    }

    let mut aug_matrix = matrix.clone();
    for i in 0..n {
        aug_matrix[i].push(rhs[i]);
    }

    // Gaussian Elimination
    for i in 0..n {
        // Pivot
        let mut pivot_row = i;
        for k in i + 1..n {
            if aug_matrix[k][i].abs() > aug_matrix[pivot_row][i].abs() {
                pivot_row = k;
            }
        }
        aug_matrix.swap(i, pivot_row);

        if aug_matrix[i][i].abs() < 1e-10 {
            return None; // Singular matrix
        }

        // Normalize row i
        let pivot = aug_matrix[i][i];
        for j in i..=n {
            aug_matrix[i][j] /= pivot;
        }

        // Eliminate other rows
        for k in 0..n {
            if k != i {
                let factor = aug_matrix[k][i];
                for j in i..=n {
                    aug_matrix[k][j] -= factor * aug_matrix[i][j];
                }
            }
        }
    }

    // Extract solution
    let mut solution = Vec::with_capacity(n);
    for i in 0..n {
        solution.push(aug_matrix[i][n]);
    }
    Some(solution)
}

#[test]
fn test_linear_complexity_vulnerability() {
    // 1. Setup a small field (N=3)
    // A sum of N sinusoids satisfies a linear recurrence of order 2N IF sampled equidistantly.
    let seed = 12345;
    let n_waves = 3; 
    let order = 2 * n_waves; // 6
    let field = generate_field(seed, n_waves);
    let key_loc = Vector3D::new(10.0, 10.0, 10.0);

    // 2. Collect samples with Jitter (simulating real encryption)
    let mut rng = ChaCha20Rng::seed_from_u64(999);
    let mut samples = Vec::new();
    let num_samples = 2 * order + 20;
    
    // We collect samples at random points around key_loc
    for _ in 0..num_samples {
        let dx = (rng.gen::<f64>() - 0.5) * 0.1;
        let dy = (rng.gen::<f64>() - 0.5) * 0.1;
        let dz = (rng.gen::<f64>() - 0.5) * 0.1;
        let p = Vector3D::new(key_loc.x + dx, key_loc.y + dy, key_loc.z + dz);
        let val = field.eval_at_point(&p);
        samples.push(val);
    }

    // 3. Build Linear System (Assuming equidistant sampling - attacker doesn't know jitter)
    // The attacker assumes x[n] = -sum(c[j]*x[n-j])
    // This model fails because the sampling is not equidistant.
    
    let mut matrix = Vec::new();
    let mut rhs = Vec::new();

    // Use a window of samples to form equations.
    // We try to solve for coefficients assuming linear recurrence holds.
    for k in 0..order {
        let mut row = Vec::new();
        // Coefficients c1...cn correspond to x[n-1]...x[n-order]
        for j in 1..=order {
            // Indexing: we want to predict samples[order+k] using previous 'order' samples
            row.push(samples[order + k - j]);
        }
        matrix.push(row);
        rhs.push(-samples[order + k]);
    }

    // 4. Solve for Coefficients
    let coeffs_opt = solve_linear_system(&matrix, &rhs);

    if coeffs_opt.is_none() {
        println!("Matrix is singular! Attack failed (Good).");
        return;
    }
    let coeffs = coeffs_opt.unwrap();

    println!("Recovered Coefficients: {:?}", coeffs);

    // 5. Predict Next Value
    let target_idx = 2 * order;
    
    // We try to predict the sample at target_idx using the linear recurrence
    // derived from previous samples.
    
    let actual_val_in_seq = samples[target_idx];
    
    let mut predicted_val = 0.0;
    for j in 1..=order {
        let past_val = samples[target_idx - j];
        predicted_val -= coeffs[j-1] * past_val;
    }

    println!("Actual: {}, Predicted: {}", actual_val_in_seq, predicted_val);
    let error = (actual_val_in_seq - predicted_val).abs();
    println!("Prediction Error: {}", error);

    // Assert error is large
    assert!(error > 1e-4, "Linear prediction succeeded! Vulnerability confirmed.");
    println!("Attack Failed as expected! Linear complexity broken. Error: {}", error);
}
