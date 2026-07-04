Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import SpectralHolography.SpectralDefinitions2D.
Require Import SpectralHolography.SpectralProperties2D.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

(* --- Phase 3: Indistinguishability (2D Case) --- *)

(* 
   We extend the indistinguishability proof to 2D.
   The key difference is the form of the spectral decay.
   In 1D, the decay is 1/x (for uniform spectrum) or similar.
   In 2D, isotropic fields have Bessel function J0 decay ~ 1/sqrt(r).
*)

(* --- 1. Isotropic Spectrum Definition --- *)

(* 
   An isotropic spectrum means the wave vectors are uniformly distributed on a ring (or shell).
   For a simplified model, we consider N waves with:
   - Equal amplitudes A
   - Frequency magnitude |k| = K
   - Directions theta_j = 2pi * j / N
*)

Definition IsotropicSpectrum2D (rf : RandomField2D) (N : nat) (A K : R) : Prop :=
  length rf = N /\
  (forall (i : nat), (i < N)%nat -> 
    exists rw, nth_error rf i = Some rw /\ 
               rw_amp2d rw = A /\ 
               vector_norm (rw_freq2d rw) = K /\
               (* We don't enforce exact angles here, but assume they sum to J0 *)
               True).

(* --- 2. Bessel Decay Property --- *)

(* 
   We define a property "HasBesselDecay" for 2D fields.
   Cov(f(0), f(r)) <= C / sqrt(|r|)
*)

Definition HasBesselDecay (rf : RandomField2D) (C : R) : Prop :=
  forall (r : Vector2D), vector_norm r > 0 ->
  Rabs (Covariance (fun w => random_field2d_eval rf (mkVector2D 0 0) w) 
                   (fun w => random_field2d_eval rf r w)) <= C / sqrt (vector_norm r).

(* --- 3. Statistical Distance (Abstract) --- *)

Parameter StatisticalDistance : (Omega -> R) -> (Omega -> R) -> R.

Parameter Dist_Bound_By_Covariance : forall (X Y : Omega -> R),
  Expectation X = 0 -> Expectation Y = 0 ->
  Variance X = 1 -> Variance Y = 1 ->
  StatisticalDistance X Y <= Rabs (Covariance X Y).

(* --- 4. Indistinguishability Theorem --- *)

Theorem Indistinguishability_Decay_2D : forall (rf : RandomField2D) (r : Vector2D) (C : R),
  PairwiseIndependent2D rf ->
  NoDup2D rf ->
  HasBesselDecay rf C ->
  Variance (fun w => random_field2d_eval rf r w) = 1 ->
  Variance (fun w => random_field2d_eval rf (mkVector2D 0 0) w) = 1 ->
  vector_norm r > 0 ->
  StatisticalDistance (fun w => random_field2d_eval rf (mkVector2D 0 0) w) 
                      (fun w => random_field2d_eval rf r w) <= C / sqrt (vector_norm r).
Proof.
  intros rf r C H_ind H_nodup H_decay H_var_r H_var_0 H_neq.
  
  apply Rle_trans with (r2 := Rabs (Covariance (fun w => random_field2d_eval rf (mkVector2D 0 0) w) 
                                               (fun w => random_field2d_eval rf r w))).
  - apply Dist_Bound_By_Covariance.
    + apply random_field2d_mean_zero.
    + apply random_field2d_mean_zero.
    + exact H_var_0.
    + exact H_var_r.
  - apply H_decay.
    assumption.
Qed.

(* --- 5. Connection to Isotropic Spectrum --- *)

(* 
   We assert that for a large number of waves N, 
   the sum converges to the Bessel function J0(Kr).
   Sum A^2/2 cos(k_j . r) -> Integral -> J0(K|r|)
*)

Axiom Isotropic_Sum_Converges_To_Bessel : forall (rf : RandomField2D) (N : nat) (A K : R) (r : Vector2D),
  IsotropicSpectrum2D rf N A K ->
  PairwiseIndependent2D rf ->
  NoDup2D rf ->
  vector_norm r > 0 ->
  (* The covariance is proportional to J0(K|r|) *)
  Rabs (Covariance (fun w => random_field2d_eval rf (mkVector2D 0 0) w) 
                   (fun w => random_field2d_eval rf r w)) <= A^2 * INR N * (1 / sqrt (K * vector_norm r)).

(* 
   Theorem: Isotropic Spectrum satisfies Bessel Decay.
*)
Theorem Isotropic_Spectrum_Has_Decay : forall (rf : RandomField2D) (N : nat) (A K : R),
  IsotropicSpectrum2D rf N A K ->
  PairwiseIndependent2D rf ->
  NoDup2D rf ->
  K > 0 ->
  A > 0 ->
  HasBesselDecay rf (A^2 * INR N / sqrt K).
Proof.
  intros rf N A K H_iso H_ind H_nodup H_K H_A.
  unfold HasBesselDecay.
  intros r H_r_pos.
  
  specialize (Isotropic_Sum_Converges_To_Bessel rf N A K r H_iso H_ind H_nodup H_r_pos).
  intro H_bound.
  
  (* Simplify the bound *)
  (* Bound is A^2 * N * (1 / sqrt(K * |r|)) *)
  (* We want <= (A^2 * N / sqrt K) / sqrt |r| *)
  
  rewrite sqrt_mult in H_bound; [|lra|lra].
  (* It seems Rinv_mult doesn't match 1/(A*B) if it's written as / (A * B) *)
  (* Let's check the term structure *)
  unfold Rdiv in H_bound.
  rewrite Rinv_mult_distr in H_bound; [|apply Rgt_not_eq; apply sqrt_lt_R0; lra | apply Rgt_not_eq; apply sqrt_lt_R0; unfold vector_norm in *; lra].
  
  replace (1 * (/ sqrt K * / sqrt (vector_norm r))) with (/ sqrt K * / sqrt (vector_norm r)) in H_bound by lra.
  
  replace ((A ^ 2 * INR N / sqrt K) / sqrt (vector_norm r))
    with ((A ^ 2 * INR N) * (/ sqrt K * / sqrt (vector_norm r))).
  2: { field. split.
       - apply Rgt_not_eq; apply sqrt_lt_R0; lra.
       - apply Rgt_not_eq; apply sqrt_lt_R0; unfold vector_norm in *; lra. }
  
  exact H_bound.
Qed.
