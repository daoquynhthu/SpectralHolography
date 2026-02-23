Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lra.
Require Import SpectralHolography.SpectralDefinitions.

Open Scope R_scope.

(* --- Probability Space Definitions --- *)

Parameter Omega : Type.
Parameter Expectation : (Omega -> R) -> R.

Axiom E_linear : forall (X Y : Omega -> R) (a b : R),
  Expectation (fun w => a * X w + b * Y w) = a * Expectation X + b * Expectation Y.

Axiom E_const : forall (c : R), Expectation (fun _ => c) = c.

Definition Variance (X : Omega -> R) : R :=
  Expectation (fun w => (X w - Expectation X) ^ 2).

Definition Covariance (X Y : Omega -> R) : R :=
  Expectation (fun w => (X w - Expectation X) * (Y w - Expectation Y)).

 Lemma Covariance_mean_zero : forall (X Y : Omega -> R),
  Expectation X = 0 -> Expectation Y = 0 ->
  Covariance X Y = Expectation (fun w => X w * Y w).
Proof.
  intros. unfold Covariance. rewrite H, H0.
  f_equal. apply functional_extensionality. intros. lra.
Qed.

Lemma E_scal : forall (X : Omega -> R) (c : R),
  Expectation (fun w => c * X w) = c * Expectation X.
Proof.
  intros.
  replace (fun w => c * X w) with (fun w => c * X w + 0 * (fun _ => 0) w).
  2: { apply functional_extensionality. intros. rewrite Rmult_0_l, Rplus_0_r. reflexivity. }
  rewrite E_linear.
  rewrite Rmult_0_l, Rplus_0_r.
  reflexivity.
Qed.

Lemma E_add : forall (X Y : Omega -> R),
  Expectation (fun w => X w + Y w) = Expectation X + Expectation Y.
Proof.
  intros.
  rewrite <- (Rmult_1_l (Expectation X)).
  rewrite <- (Rmult_1_l (Expectation Y)).
  rewrite <- E_linear.
  f_equal. apply functional_extensionality. intros. lra.
Qed.

(* --- Random Wave Properties --- *)

(* Assume Phase is Uniform on [0, 2pi] *)
(* E[sin(theta + phi)] = 0 *)
(* E[cos(theta + phi)] = 0 *)
(* E[sin^2(theta + phi)] = 1/2 *)
(* E[cos^2(theta + phi)] = 1/2 *)
(* E[sin(theta + phi)cos(theta + phi)] = 0 *)

Axiom E_sin_uniform_phase : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => sin (theta + phi w)) = 0.

Axiom E_cos_uniform_phase : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => cos (theta + phi w)) = 0.
  
Axiom E_cos_2phase : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => cos (2 * phi w + theta)) = 0.

(* Helper Lemmas for Squares *)
Lemma E_sin_sq_uniform : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => (sin (theta + phi w))^2) = 1/2.
Proof.
  intros.
  (* sin^2(x) = (1 - cos(2x))/2 *)
  assert (H: forall w, (sin (theta + phi w))^2 = 1/2 * (1 - cos (2 * (theta + phi w)))).
  { 
    intros. 
    rewrite cos_2a.
    pose proof (sin2 (theta + phi w)) as H_trig.
    unfold Rsqr in H_trig.
    simpl.
    lra.
  }
  rewrite (functional_extensionality _ _ H).
  rewrite E_scal.
  rewrite <- (Rminus_0_r (Expectation (fun w => 1 - cos (2 * (theta + phi w))))).
  replace (fun w => 1 - cos (2 * (theta + phi w))) 
    with (fun w => 1 * (fun _ => 1) w + (-1) * (fun w => cos (2 * theta + 2 * phi w)) w).
  2: { 
    apply functional_extensionality. intros w. 
    replace (2 * (theta + phi w)) with (2 * theta + 2 * phi w) by lra.
    lra. 
  }
  rewrite E_linear.
  rewrite E_const.
  
  assert (H_cos: Expectation (fun w => cos (2 * theta + 2 * phi w)) = 0).
  {
    replace (fun w => cos (2 * theta + 2 * phi w)) with (fun w => cos (2 * phi w + 2 * theta)).
    2: { apply functional_extensionality. intros. f_equal. lra. }
    apply E_cos_2phase.
  }
  rewrite H_cos.
  lra.
Qed.

Lemma E_cos_sq_uniform : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => (cos (theta + phi w))^2) = 1/2.
Proof.
  intros.
  assert (H: forall w, (cos (theta + phi w))^2 = 1/2 * (1 + cos (2 * (theta + phi w)))).
  { 
    intros. 
    rewrite cos_2a.
    pose proof (cos2 (theta + phi w)) as H_trig.
    unfold Rsqr in H_trig.
    simpl.
    lra.
  }
  rewrite (functional_extensionality _ _ H).
  rewrite E_scal.
  
  assert (H_cos: Expectation (fun w => cos (2 * (theta + phi w))) = 0).
  {
    replace (fun w => cos (2 * (theta + phi w))) with (fun w => cos (2 * phi w + 2 * theta)).
    2: { apply functional_extensionality. intros. f_equal. lra. }
    apply E_cos_2phase.
  }
  
  replace (fun w => 1 + cos (2 * (theta + phi w))) 
    with (fun w => 1 * (fun _ => 1) w + 1 * (fun w => cos (2 * (theta + phi w))) w).
  2: { apply functional_extensionality. intros. lra. }
  rewrite E_linear.
  rewrite E_const.
  rewrite H_cos.
  lra.
Qed.

Lemma E_sin_cos_uniform : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => sin (theta + phi w) * cos (theta + phi w)) = 0.
Proof.
  intros.
  (* sin(x)cos(x) = 1/2 sin(2x) *)
  assert (H: forall w, sin (theta + phi w) * cos (theta + phi w) = 1/2 * sin (2 * (theta + phi w))).
  { intros. rewrite sin_2a. lra. }
  rewrite (functional_extensionality _ _ H).
  rewrite E_scal.
  
  assert (H_sin: Expectation (fun w => sin (2 * (theta + phi w))) = 0).
  {
    replace (fun w => sin (2 * (theta + phi w))) with (fun w => sin (2 * theta + 2 * phi w)).
    2: { apply functional_extensionality. intros. f_equal. lra. }
    (* Assume E[sin(2theta + 2phi)] = 0 similar to cos case. *)
    (* Actually, sin(A+B) = sinA cosB + cosA sinB. *)
    (* But simpler, let's assume E[sin(2phi + C)] = 0 is also an axiom or follows from uniform phase *)
    (* We can reuse E_sin_uniform_phase if we consider 2phi as uniform modulo 2pi *)
    (* For now, let's use a specific axiom or just assume it holds for 2phi as well *)
    apply (E_sin_uniform_phase (2 * theta) (fun w => 2 * phi w)). 
  }
  rewrite H_sin.
  lra.
Qed.

(* --- Random Wave and Field Definitions --- *)

Record RandomWave : Type := mkRandomWave {
  rw_amp : R;
  rw_freq : R;
  rw_phase : Omega -> R
}.

Definition random_wave_eval (rw : RandomWave) (x : R) (w : Omega) : R :=
  (rw_amp rw) * cos ((rw_freq rw) * x + (rw_phase rw w)).

Definition random_wave_deriv (rw : RandomWave) (x : R) (w : Omega) : R :=
  - (rw_amp rw) * (rw_freq rw) * sin ((rw_freq rw) * x + (rw_phase rw w)).

Definition random_wave_deriv2 (rw : RandomWave) (x : R) (w : Omega) : R :=
  - (rw_amp rw) * (rw_freq rw) * (rw_freq rw) * cos ((rw_freq rw) * x + (rw_phase rw w)).

Definition RandomField := list RandomWave.

Fixpoint random_field_eval (rf : RandomField) (x : R) (w : Omega) : R :=
  match rf with
  | nil => 0
  | rw :: rest => (random_wave_eval rw x w) + (random_field_eval rest x w)
  end.

Fixpoint random_field_deriv (rf : RandomField) (x : R) (w : Omega) : R :=
  match rf with
  | nil => 0
  | rw :: rest => (random_wave_deriv rw x w) + (random_field_deriv rest x w)
  end.

Fixpoint random_field_deriv2 (rf : RandomField) (x : R) (w : Omega) : R :=
  match rf with
  | nil => 0
  | rw :: rest => (random_wave_deriv2 rw x w) + (random_field_deriv2 rest x w)
  end.

(* Mean Zero Properties *)

Lemma random_wave_mean_zero : forall (rw : RandomWave) (x : R),
  Expectation (random_wave_eval rw x) = 0.
Proof.
  intros.
  unfold random_wave_eval.
  assert (H: forall w, rw_amp rw * cos (rw_freq rw * x + rw_phase rw w) = 
             rw_amp rw * cos (rw_freq rw * x + rw_phase rw w)).
  { auto. }
  rewrite E_scal.
  rewrite E_cos_uniform_phase.
  lra.
Qed.

Lemma random_wave_deriv_mean_zero : forall (rw : RandomWave) (x : R),
  Expectation (random_wave_deriv rw x) = 0.
Proof.
  intros.
  unfold random_wave_deriv.
  replace (fun w => - (rw_amp rw) * (rw_freq rw) * sin ((rw_freq rw) * x + (rw_phase rw w)))
    with (fun w => (- (rw_amp rw) * (rw_freq rw)) * sin ((rw_freq rw) * x + (rw_phase rw w))).
  2: { apply functional_extensionality. intros. lra. }
  rewrite E_scal.
  rewrite E_sin_uniform_phase.
  lra.
Qed.

Lemma random_wave_deriv2_mean_zero : forall (rw : RandomWave) (x : R),
  Expectation (random_wave_deriv2 rw x) = 0.
Proof.
  intros.
  unfold random_wave_deriv2.
  replace (fun w => - (rw_amp rw) * (rw_freq rw) ^ 2 * cos ((rw_freq rw) * x + (rw_phase rw w)))
    with (fun w => (- (rw_amp rw) * (rw_freq rw) ^ 2) * cos ((rw_freq rw) * x + (rw_phase rw w))).
  2: { apply functional_extensionality. intros. lra. }
  rewrite E_scal.
  rewrite E_cos_uniform_phase.
  lra.
Qed.

(* Variance and Stationarity *)

Lemma random_wave_variance : forall (rw : RandomWave) (x : R),
  Variance (random_wave_eval rw x) = 1/2 * (rw_amp rw)^2.
Proof.
  intros.
  unfold Variance.
  rewrite random_wave_mean_zero.
  assert (H_sq: forall w, (random_wave_eval rw x w - 0)^2 = (rw_amp rw)^2 * (cos ((rw_freq rw) * x + (rw_phase rw w)))^2).
  {
    intros. unfold random_wave_eval.
    rewrite Rminus_0_r.
    ring.
  }
  rewrite (functional_extensionality _ _ H_sq).
  rewrite E_scal.
  rewrite E_cos_sq_uniform.
  lra.
Qed.

Lemma random_wave_deriv_variance : forall (rw : RandomWave) (x : R),
  Variance (random_wave_deriv rw x) = 1/2 * (rw_amp rw)^2 * (rw_freq rw)^2.
Proof.
  intros.
  unfold Variance.
  rewrite random_wave_deriv_mean_zero.
  assert (H_sq: forall w, (random_wave_deriv rw x w - 0)^2 = (rw_amp rw)^2 * (rw_freq rw)^2 * (sin ((rw_freq rw) * x + (rw_phase rw w)))^2).
  {
    intros. unfold random_wave_deriv.
    rewrite Rminus_0_r.
    ring.
  }
  rewrite (functional_extensionality _ _ H_sq).
  rewrite E_scal.
  rewrite E_sin_sq_uniform.
  lra.
Qed.

Lemma random_wave_deriv_orthogonal : forall (rw : RandomWave) (x : R),
  Covariance (random_wave_eval rw x) (random_wave_deriv rw x) = 0.
Proof.
  intros.
  unfold Covariance.
  rewrite random_wave_mean_zero.
  rewrite random_wave_deriv_mean_zero.
  assert (H_prod: forall w, (random_wave_eval rw x w - 0) * (random_wave_deriv rw x w - 0) = 
          - (rw_amp rw)^2 * (rw_freq rw) * (sin ((rw_freq rw) * x + (rw_phase rw w)) * cos ((rw_freq rw) * x + (rw_phase rw w)))).
  {
    intros. unfold random_wave_eval, random_wave_deriv.
    repeat rewrite Rminus_0_r.
    ring.
  }
  rewrite (functional_extensionality _ _ H_prod).
  rewrite E_scal.
  rewrite E_sin_cos_uniform.
  lra.
Qed.

(* Stationarity implies E[f(x)f(y)] depends on x-y. *)
(* E[A cos(kx+phi) * A cos(ky+phi)] = A^2 E[cos(kx+phi)cos(ky+phi)] *)
(* = A^2/2 cos(k(x-y)) *)
Lemma random_wave_stationary : forall (rw : RandomWave) (x y : R),
  Covariance (random_wave_eval rw x) (random_wave_eval rw y) = 
  1/2 * (rw_amp rw)^2 * cos ((rw_freq rw) * (x - y)).
Proof.
  intros.
  unfold Covariance.
  rewrite random_wave_mean_zero.
  rewrite random_wave_mean_zero.
  assert (H_prod: forall w, (random_wave_eval rw x w - 0) * (random_wave_eval rw y w - 0) = 
          (rw_amp rw)^2 * (cos ((rw_freq rw) * x + (rw_phase rw w)) * cos ((rw_freq rw) * y + (rw_phase rw w)))).
  {
    intros. unfold random_wave_eval. repeat rewrite Rminus_0_r. ring.
  }
  rewrite (functional_extensionality _ _ H_prod).
  rewrite E_scal.
  
  (* E[cos(A+phi)cos(B+phi)] = 1/2 cos(A-B) *)
  (* Let A = kx, B = ky *)
  (* cos(kx+phi)cos(ky+phi) = 1/2(cos(k(x-y)) + cos(k(x+y)+2phi)) *)
  
  assert (H_trig: forall w, cos ((rw_freq rw) * x + (rw_phase rw w)) * cos ((rw_freq rw) * y + (rw_phase rw w)) = 
          1/2 * (cos ((rw_freq rw) * (x - y)) + cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w)))).
  {
    intros w.
    (* Prove cos a cos b = 1/2 (cos(a-b) + cos(a+b)) *)
    assert (cos_mult_local: forall a b, cos a * cos b = 1/2 * (cos (a - b) + cos (a + b))).
    { intros. rewrite cos_minus, cos_plus. lra. }
    
    rewrite cos_mult_local.
    f_equal. f_equal.
    - f_equal. lra.
    - f_equal. lra.
  }
  rewrite (functional_extensionality _ _ H_trig).
  rewrite E_scal.
  replace (fun w => cos (rw_freq rw * (x - y)) + cos (rw_freq rw * (x + y) + 2 * rw_phase rw w))
    with (fun w => 1 * (fun _ => cos (rw_freq rw * (x - y))) w + 1 * (fun w => cos (rw_freq rw * (x + y) + 2 * rw_phase rw w)) w).
  2: { apply functional_extensionality. intros w0. lra. }
  rewrite E_linear.
  rewrite E_const.
  
  assert (H_cos2: Expectation (fun w => cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w))) = 0).
  {
     replace (fun w => cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w))) 
       with (fun w => cos (2 * (rw_phase rw w) + (rw_freq rw) * (x + y))).
     - apply (E_cos_2phase ((rw_freq rw) * (x + y)) (rw_phase rw)).
     - apply functional_extensionality. intros w. f_equal. lra.
  }
  rewrite H_cos2.
  unfold pow; simpl; field.
Qed.

(* Pairwise Independence Axiom *)
(* We assume waves in the field are independent *)
Definition PairwiseIndependent (rf : RandomField) : Prop :=
  forall (rw1 rw2 : RandomWave),
    In rw1 rf -> In rw2 rf -> rw1 <> rw2 ->
    forall (X Y : Omega -> R),
      (exists x, X = random_wave_eval rw1 x \/ X = random_wave_deriv rw1 x \/ X = random_wave_deriv2 rw1 x) ->
      (exists y, Y = random_wave_eval rw2 y \/ Y = random_wave_deriv rw2 y \/ Y = random_wave_deriv2 rw2 y) ->
      Expectation (fun w => X w * Y w) = Expectation X * Expectation Y.

Lemma independent_wave_field_uncorrelated : forall (a : RandomWave) (rf : RandomField) (x y : R),
  (forall rw, In rw rf -> rw <> a) ->
  (forall rw1 rw2, In rw1 (a :: rf) -> In rw2 (a :: rf) -> rw1 <> rw2 -> 
    Expectation (fun w => random_wave_eval rw1 x w * random_wave_eval rw2 y w) = 
    Expectation (fun w => random_wave_eval rw1 x w) * Expectation (fun w => random_wave_eval rw2 y w)) ->
  Expectation (fun w => random_wave_eval a x w * random_field_eval rf y w) = 0.
Proof.
  intros a rf x y H_distinct H_ind.
  induction rf.
  - simpl. 
    replace (fun w => random_wave_eval a x w * 0) with (fun w : Omega => 0).
    2: { apply functional_extensionality. intros. lra. }
    apply E_const.
  - simpl.
    replace (fun w => random_wave_eval a x w * (random_wave_eval a0 y w + random_field_eval rf y w))
      with (fun w => random_wave_eval a x w * random_wave_eval a0 y w + random_wave_eval a x w * random_field_eval rf y w).
    2: { apply functional_extensionality. intros. lra. }
    rewrite E_add.
    
    (* First term: E[a * a0] *)
    assert (H_first: Expectation (fun w => random_wave_eval a x w * random_wave_eval a0 y w) = 0).
    {
      rewrite H_ind.
      + rewrite random_wave_mean_zero. lra.
      + simpl. left. reflexivity.
      + simpl. right. left. reflexivity.
      + apply not_eq_sym. apply H_distinct. simpl. left. reflexivity.
    }
    rewrite H_first.
    
    (* Second term: E[a * rest] *)
    assert (H_second: Expectation (fun w => random_wave_eval a x w * random_field_eval rf y w) = 0).
    {
      apply IHrf.
      + intros rw H_in. apply H_distinct. simpl. right. assumption.
      + intros rw1 rw2 H_in1 H_in2 H_neq.
        apply H_ind.
        * simpl. destruct H_in1; [left|right; right]; assumption.
        * simpl. destruct H_in2; [left|right; right]; assumption.
        * assumption.
    }
    rewrite H_second.
    lra.
Qed.

Lemma random_field_mean_zero : forall (rf : RandomField) (x : R),
  Expectation (random_field_eval rf x) = 0.
Proof.
  induction rf; simpl; intros.
  - apply E_const.
  - rewrite E_add. rewrite IHrf. rewrite random_wave_mean_zero. lra.
Qed.

Lemma random_field_covariance_sum : forall (rf : RandomField) (x y : R),
  PairwiseIndependent rf ->
  NoDup rf ->
  Covariance (random_field_eval rf x) (random_field_eval rf y) = 
  fold_right Rplus 0 (map (fun rw => Covariance (random_wave_eval rw x) (random_wave_eval rw y)) rf).
Proof.
  intros rf x y H_ind H_nodup.
  
  induction rf.
  - simpl. unfold Covariance. repeat rewrite E_const. lra.
  - simpl.
    rewrite Covariance_mean_zero.
    2: { simpl. rewrite E_add. rewrite random_wave_mean_zero. rewrite random_field_mean_zero. lra. }
    2: { simpl. rewrite E_add. rewrite random_wave_mean_zero. rewrite random_field_mean_zero. lra. }
    
    (* Expand product *)
    assert (H_expand: Expectation (fun w => (random_wave_eval a x w + random_field_eval rf x w) * (random_wave_eval a y w + random_field_eval rf y w)) =
                      Expectation (fun w => random_wave_eval a x w * random_wave_eval a y w + 
                                            random_wave_eval a x w * random_field_eval rf y w +
                                            random_field_eval rf x w * random_wave_eval a y w +
                                            random_field_eval rf x w * random_field_eval rf y w)).
    {
      f_equal. apply functional_extensionality. intros w. ring.
    }
    rewrite H_expand.
    repeat rewrite E_add.
    
    (* Term 1: E[a(x)a(y)] = Cov(a, a) *)
    rewrite <- Covariance_mean_zero; [|apply random_wave_mean_zero|apply random_wave_mean_zero].
    
    (* Term 2: E[a(x)rest(y)] = 0 *)
    assert (H_cross1: Expectation (fun w => random_wave_eval a x w * random_field_eval rf y w) = 0).
    {
      apply independent_wave_field_uncorrelated.
      - intros rw H_in. inversion H_nodup as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
      - intros rw1 rw2 H_in1 H_in2 H_neq.
        unfold PairwiseIndependent in H_ind.
        apply (H_ind rw1 rw2); auto.
        + exists x. left. reflexivity.
        + exists y. left. reflexivity.
    }
    rewrite H_cross1.
    rewrite Rplus_0_r.

    (* Term 3: E[rest(x)a(y)] = 0 *)
    assert (H_cross2: Expectation (fun w => random_field_eval rf x w * random_wave_eval a y w) = 0).
    {
       assert (H_comm: Expectation (fun w => random_field_eval rf x w * random_wave_eval a y w) = 
                       Expectation (fun w => random_wave_eval a y w * random_field_eval rf x w)).
       { f_equal. apply functional_extensionality. intros w. ring. }
       rewrite H_comm.
       apply independent_wave_field_uncorrelated.
       - intros rw H_in. inversion H_nodup as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
       - intros rw1 rw2 H_in1 H_in2 H_neq.
         unfold PairwiseIndependent in H_ind.
         apply (H_ind rw1 rw2); auto.
         + exists y. left. reflexivity.
         + exists x. left. reflexivity.
    }
    rewrite H_cross2.
    rewrite Rplus_0_r.

    (* Term 4: E[rest(x)rest(y)] = Cov(rest, rest) *)
    rewrite <- Covariance_mean_zero; [|apply random_field_mean_zero|apply random_field_mean_zero].
    
    assert (H_ind_sub: PairwiseIndependent rf).
    {
      unfold PairwiseIndependent in *. intros rw1 rw2 H_in1 H_in2 H_neq X Y H_X H_Y.
      apply (H_ind rw1 rw2); simpl; try tauto; try assumption.
    }
    assert (H_nodup_sub: NoDup rf).
    { inversion H_nodup. assumption. }
    
    rewrite (IHrf H_ind_sub H_nodup_sub).
    reflexivity.
Qed.

(* Stationarity of Random Field (Isotropy Theorem 1.2) *)
Theorem random_field_stationary : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  exists (g : R -> R), forall (x y : R), Covariance (random_field_eval rf x) (random_field_eval rf y) = g (x - y).
Proof.
  intros rf H_ind H_nodup.
  induction rf.
  - exists (fun _ => 0). intros. simpl. unfold Covariance. repeat rewrite E_const. lra.
  - 
    (* IH gives g_rest *)
    assert (H_ind_sub: PairwiseIndependent rf).
    { unfold PairwiseIndependent in *. intros. apply H_ind with (rw1:=rw1) (rw2:=rw2); auto.
      simpl. right. assumption. simpl. right. assumption. }
    assert (H_nodup_sub: NoDup rf).
    { inversion H_nodup. assumption. }
    
    destruct (IHrf H_ind_sub H_nodup_sub) as [g_rest H_grest].
    
    (* Construct g_a *)
    exists (fun t => 1/2 * (rw_amp a)^2 * cos ((rw_freq a) * t) + g_rest t).
    intros x y.
    
    rewrite random_field_covariance_sum; auto.
    simpl.
    
    (* Term 1: Cov(a, a) *)
    rewrite random_wave_stationary.
    
    (* Term 2: Sum Cov(rest, rest) *)
    f_equal.
    rewrite <- H_grest.
    rewrite random_field_covariance_sum.
    * reflexivity.
    * unfold PairwiseIndependent in *. intros. apply H_ind with (rw1:=rw1) (rw2:=rw2); auto.
      simpl. right. assumption. simpl. right. assumption.
    * inversion H_nodup. assumption.
Qed.

Lemma random_field_isotropy : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  exists (h : R -> R), forall (x y : R), Covariance (random_field_eval rf x) (random_field_eval rf y) = h (Rabs (x - y)).
Proof.
  intros rf H_ind H_nodup.
  destruct (random_field_stationary rf H_ind H_nodup) as [g Hg].
  exists g.
  intros x y.
  rewrite Hg.
  
  (* Prove g(x-y) = g(|x-y|) *)
  assert (H_even: forall t, g t = g (-t)).
  {
    intros t.
    (* Let x=t, y=0. x-y=t. y-x=-t. *)
    assert (H_cov_sym: Covariance (random_field_eval rf t) (random_field_eval rf 0) = 
                       Covariance (random_field_eval rf 0) (random_field_eval rf t)).
    { unfold Covariance. f_equal. apply functional_extensionality. intros w. ring. }
    
    rewrite (Hg t 0) in H_cov_sym.
     rewrite (Hg 0 t) in H_cov_sym.
     replace (t - 0) with t in H_cov_sym by lra.
     replace (0 - t) with (-t) in H_cov_sym by lra.
     exact H_cov_sym.
  }
  
  destruct (Rcase_abs (x - y)) as [H_neg | H_pos].
  - rewrite (Rabs_left _ H_neg).
    rewrite H_even.
    reflexivity.
  - rewrite (Rabs_right _ H_pos).
    reflexivity.
Qed.






(* --- Derivative Field Properties --- *)



Lemma random_wave_deriv_deriv2_orthogonal : forall (rw : RandomWave) (x : R),
  Covariance (random_wave_deriv rw x) (random_wave_deriv2 rw x) = 0.
Proof.
  intros.
  unfold Covariance.
  rewrite random_wave_deriv_mean_zero.
  rewrite random_wave_deriv2_mean_zero.
  assert (H_prod: forall w, (random_wave_deriv rw x w - 0) * (random_wave_deriv2 rw x w - 0) = 
          (rw_amp rw)^2 * (rw_freq rw)^3 * (sin ((rw_freq rw) * x + (rw_phase rw w)) * cos ((rw_freq rw) * x + (rw_phase rw w)))).
  {
    intros. unfold random_wave_deriv, random_wave_deriv2.
    repeat rewrite Rminus_0_r.
    ring.
  }
  rewrite (functional_extensionality _ _ H_prod).
  rewrite E_scal.
  rewrite E_sin_cos_uniform.
  lra.
Qed.

Lemma random_field_deriv_mean_zero : forall (rf : RandomField) (x : R),
  Expectation (random_field_deriv rf x) = 0.
Proof.
  induction rf; simpl; intros.
  - apply E_const.
  - rewrite E_add. rewrite IHrf. rewrite random_wave_deriv_mean_zero. lra.
Qed.

Lemma random_field_deriv2_mean_zero : forall (rf : RandomField) (x : R),
  Expectation (random_field_deriv2 rf x) = 0.
Proof.
  induction rf; simpl; intros.
  - apply E_const.
  - rewrite E_add. rewrite IHrf. rewrite random_wave_deriv2_mean_zero. lra.
Qed.

Lemma independent_wave_sum_uncorrelated : forall (a : RandomWave) (rf : RandomField) 
  (f : RandomWave -> Omega -> R) (g : RandomWave -> Omega -> R),
  Expectation (f a) = 0 ->
  (forall rw, In rw rf -> Expectation (g rw) = 0) ->
  (forall rw, In rw rf -> 
     Expectation (fun w => f a w * g rw w) = Expectation (f a) * Expectation (g rw)) ->
  Expectation (fun w => f a w * (fold_right Rplus 0 (map (fun rw => g rw w) rf))) = 0.
 Proof.
   intros a rf f g E_fa_zero E_grf_zero H_ind.
   induction rf as [| a0 rf0 IHrf0].
   - simpl. replace (fun w => f a w * 0) with (fun w : Omega => 0).
     2: { apply functional_extensionality. intros. lra. }
     apply E_const.
   - simpl.
     replace (fun w => f a w * (g a0 w + fold_right Rplus 0 (map (fun rw => g rw w) rf0)))
       with (fun w => f a w * g a0 w + f a w * fold_right Rplus 0 (map (fun rw => g rw w) rf0)).
    2: { apply functional_extensionality. intros. lra. }
    rewrite E_add.
    
    (* Term 1: E[f a * g a0] *)
    rewrite H_ind.
    2: { simpl. left. reflexivity. }
    rewrite E_fa_zero.
    rewrite Rmult_0_l.
    rewrite Rplus_0_l.
    
    (* Term 2: IH *)
    apply IHrf0.
    + intros rw H_in. apply E_grf_zero. simpl. right. assumption.
    + intros rw H_in. apply H_ind. simpl. right. assumption.
 Qed.
 
 Lemma random_field_deriv_eq_fold : forall rf x w,
    random_field_deriv rf x w = fold_right Rplus 0 (map (fun rw => random_wave_deriv rw x w) rf).
  Proof.
    intros. induction rf.
    - simpl. reflexivity.
    - simpl. rewrite IHrf. reflexivity.
  Qed.
 
  Lemma random_field_eval_eq_fold : forall rf x w,
    random_field_eval rf x w = fold_right Rplus 0 (map (fun rw => random_wave_eval rw x w) rf).
  Proof.
    intros. induction rf.
    - simpl. reflexivity.
    - simpl. rewrite IHrf. reflexivity.
  Qed.

  Lemma random_field_deriv2_eq_fold : forall rf x w,
    random_field_deriv2 rf x w = fold_right Rplus 0 (map (fun rw => random_wave_deriv2 rw x w) rf).
  Proof.
    intros. induction rf.
    - simpl. reflexivity.
    - simpl. rewrite IHrf. reflexivity.
  Qed.

 Lemma random_field_eval_deriv_orthogonal : forall (rf : RandomField) (x : R),
  PairwiseIndependent rf ->
  NoDup rf ->
  Covariance (random_field_eval rf x) (random_field_deriv rf x) = 0.
Proof.
  intros rf x H_ind H_nodup.
  induction rf.
  - simpl. unfold Covariance. repeat rewrite E_const. lra.
  - simpl.
    rewrite Covariance_mean_zero.
    2: { simpl. rewrite E_add. rewrite random_wave_mean_zero. rewrite random_field_mean_zero. lra. }
    2: { simpl. rewrite E_add. rewrite random_wave_deriv_mean_zero. rewrite random_field_deriv_mean_zero. lra. }
    
    (* Expand (a + rest)(a' + rest') *)
    assert (H_expand: Expectation (fun w => (random_wave_eval a x w + random_field_eval rf x w) * (random_wave_deriv a x w + random_field_deriv rf x w)) =
                      Expectation (fun w => random_wave_eval a x w * random_wave_deriv a x w + 
                                            random_wave_eval a x w * random_field_deriv rf x w +
                                            random_field_eval rf x w * random_wave_deriv a x w +
                                            random_field_eval rf x w * random_field_deriv rf x w)).
    {
      f_equal. apply functional_extensionality. intros w. ring.
    }
    rewrite H_expand.
    repeat rewrite E_add.
    
    (* Term 1: Cov(a, a') = 0 *)
    rewrite <- Covariance_mean_zero; [|apply random_wave_mean_zero|apply random_wave_deriv_mean_zero].
    rewrite random_wave_deriv_orthogonal.
    
    (* Term 2: E[a * rest'] = 0 *)
    assert (H_cross1: PairwiseIndependent (a :: rf) -> NoDup (a :: rf) -> Expectation (fun w => random_wave_eval a x w * random_field_deriv rf x w) = 0).
      {
         intros H_ind_sub H_nodup_sub.
         replace (fun w => random_wave_eval a x w * random_field_deriv rf x w)
           with (fun w => random_wave_eval a x w * fold_right Rplus 0 (map (fun rw => random_wave_deriv rw x w) rf)).
         2: { apply functional_extensionality. intros. rewrite random_field_deriv_eq_fold. reflexivity. }
         apply independent_wave_sum_uncorrelated with (f := fun rw => random_wave_eval rw x) (g := fun rw => random_wave_deriv rw x).
         - apply random_wave_mean_zero.
         - intros rw H_in. apply random_wave_deriv_mean_zero.
         - intros rw H_in.
           unfold PairwiseIndependent in H_ind_sub.
           apply (H_ind_sub a rw).
           + simpl. left. reflexivity.
           + simpl. right. assumption.
           + inversion H_nodup_sub as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
           + exists x. left. reflexivity.
           + exists x. right. left. reflexivity.
      }
    rewrite (H_cross1 H_ind H_nodup).
    rewrite Rplus_0_r. (* 0 + 0 = 0 *)

    (* Term 3: E[rest * a'] = 0 *)
    assert (H_cross2: PairwiseIndependent (a :: rf) -> NoDup (a :: rf) -> Expectation (fun w => random_field_eval rf x w * random_wave_deriv a x w) = 0).
      {
         intros H_ind_sub H_nodup_sub.
         assert (H_comm: Expectation (fun w => random_field_eval rf x w * random_wave_deriv a x w) = 
                         Expectation (fun w => random_wave_deriv a x w * random_field_eval rf x w)).
         { f_equal. apply functional_extensionality. intros w. ring. }
         rewrite H_comm.
         
         replace (fun w => random_wave_deriv a x w * random_field_eval rf x w)
           with (fun w => random_wave_deriv a x w * fold_right Rplus 0 (map (fun rw => random_wave_eval rw x w) rf)).
         2: { apply functional_extensionality. intros. rewrite random_field_eval_eq_fold. reflexivity. }

         apply independent_wave_sum_uncorrelated with (f := fun rw => random_wave_deriv rw x) (g := fun rw => random_wave_eval rw x).
         - apply random_wave_deriv_mean_zero.
         - intros rw H_in. apply random_wave_mean_zero.
         - intros rw H_in.
           unfold PairwiseIndependent in H_ind_sub.
           apply (H_ind_sub a rw).
           + simpl. left. reflexivity.
           + simpl. right. assumption.
           + inversion H_nodup_sub as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
           + exists x. right. left. reflexivity.
           + exists x. left. reflexivity.
      }
    rewrite (H_cross2 H_ind H_nodup).
    
    repeat rewrite Rplus_0_l.
    repeat rewrite Rplus_0_r.

    (* Term 4: Cov(rest, rest') *)
    rewrite <- Covariance_mean_zero; [|apply random_field_mean_zero|apply random_field_deriv_mean_zero].
    
    apply IHrf.
    + unfold PairwiseIndependent in *. intros rw1 rw2 H_in1 H_in2 H_neq X Y H_X H_Y.
      apply (H_ind rw1 rw2); try assumption.
      -- right. assumption.
      -- right. assumption.
    + inversion H_nodup. assumption.
Qed.

Lemma random_field_deriv_deriv2_orthogonal : forall (rf : RandomField) (x : R),
  PairwiseIndependent rf ->
  NoDup rf ->
  Covariance (random_field_deriv rf x) (random_field_deriv2 rf x) = 0.
Proof.
  intros rf x H_ind H_nodup.
  induction rf.
  - simpl. unfold Covariance. repeat rewrite E_const. lra.
  - simpl.
    rewrite Covariance_mean_zero.
    2: { simpl. rewrite E_add. rewrite random_wave_deriv_mean_zero. rewrite random_field_deriv_mean_zero. lra. }
    2: { simpl. rewrite E_add. rewrite random_wave_deriv2_mean_zero. rewrite random_field_deriv2_mean_zero. lra. }
    
    (* Expand (a' + rest')(a'' + rest'') *)
    assert (H_expand: Expectation (fun w => (random_wave_deriv a x w + random_field_deriv rf x w) * (random_wave_deriv2 a x w + random_field_deriv2 rf x w)) =
                      Expectation (fun w => random_wave_deriv a x w * random_wave_deriv2 a x w + 
                                            random_wave_deriv a x w * random_field_deriv2 rf x w +
                                            random_field_deriv rf x w * random_wave_deriv2 a x w +
                                            random_field_deriv rf x w * random_field_deriv2 rf x w)).
    {
      f_equal. apply functional_extensionality. intros w. ring.
    }
    rewrite H_expand.
    repeat rewrite E_add.
    
    (* Term 1: Cov(a', a'') = 0 *)
    rewrite <- Covariance_mean_zero; [|apply random_wave_deriv_mean_zero|apply random_wave_deriv2_mean_zero].
    rewrite random_wave_deriv_deriv2_orthogonal.
    
    (* Term 2: E[a' * rest''] = 0 *)
    assert (H_cross1: PairwiseIndependent (a :: rf) -> NoDup (a :: rf) -> Expectation (fun w => random_wave_deriv a x w * random_field_deriv2 rf x w) = 0).
    {
       intros H_ind_sub H_nodup_sub.
       replace (fun w => random_wave_deriv a x w * random_field_deriv2 rf x w)
         with (fun w => random_wave_deriv a x w * fold_right Rplus 0 (map (fun rw => random_wave_deriv2 rw x w) rf)).
       2: { apply functional_extensionality. intros. rewrite random_field_deriv2_eq_fold. reflexivity. }
       apply independent_wave_sum_uncorrelated with (f := fun rw => random_wave_deriv rw x) (g := fun rw => random_wave_deriv2 rw x).
       - apply random_wave_deriv_mean_zero.
       - intros rw H_in. apply random_wave_deriv2_mean_zero.
       - intros rw H_in.
         unfold PairwiseIndependent in H_ind_sub.
         apply (H_ind_sub a rw).
         + simpl. left. reflexivity.
         + simpl. right. assumption.
         + inversion H_nodup_sub as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
         + exists x. right. left. reflexivity.
         + exists x. right. right. reflexivity.
    }
    rewrite (H_cross1 H_ind H_nodup).
    rewrite Rplus_0_r.

    (* Term 3: E[rest' * a''] = 0 *)
    assert (H_cross2: PairwiseIndependent (a :: rf) -> NoDup (a :: rf) -> Expectation (fun w => random_field_deriv rf x w * random_wave_deriv2 a x w) = 0).
    {
       intros H_ind_sub H_nodup_sub.
       assert (H_comm: Expectation (fun w => random_field_deriv rf x w * random_wave_deriv2 a x w) = 
                       Expectation (fun w => random_wave_deriv2 a x w * random_field_deriv rf x w)).
       { f_equal. apply functional_extensionality. intros w. ring. }
       rewrite H_comm.
       
       replace (fun w => random_wave_deriv2 a x w * random_field_deriv rf x w)
         with (fun w => random_wave_deriv2 a x w * fold_right Rplus 0 (map (fun rw => random_wave_deriv rw x w) rf)).
       2: { apply functional_extensionality. intros. rewrite random_field_deriv_eq_fold. reflexivity. }

       apply independent_wave_sum_uncorrelated with (f := fun rw => random_wave_deriv2 rw x) (g := fun rw => random_wave_deriv rw x).
       - apply random_wave_deriv2_mean_zero.
       - intros rw H_in. apply random_wave_deriv_mean_zero.
       - intros rw H_in.
         unfold PairwiseIndependent in H_ind_sub.
         apply (H_ind_sub a rw).
         + simpl. left. reflexivity.
         + simpl. right. assumption.
         + inversion H_nodup_sub as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
         + exists x. right. right. reflexivity.
         + exists x. right. left. reflexivity.
    }
    rewrite (H_cross2 H_ind H_nodup).
    
    repeat rewrite Rplus_0_l.
    repeat rewrite Rplus_0_r.

    (* Term 4: Cov(rest', rest'') *)
    rewrite <- Covariance_mean_zero; [|apply random_field_deriv_mean_zero|apply random_field_deriv2_mean_zero].
    
    apply IHrf.
    + unfold PairwiseIndependent in *. intros rw1 rw2 H_in1 H_in2 H_neq X Y H_X H_Y.
      apply (H_ind rw1 rw2); try assumption.
      -- right. assumption.
      -- right. assumption.
    + inversion H_nodup. assumption.
Qed.





Lemma random_wave_deriv_stationary : forall (rw : RandomWave) (x y : R),
  Covariance (random_wave_deriv rw x) (random_wave_deriv rw y) = 
  1/2 * (rw_amp rw)^2 * (rw_freq rw)^2 * cos ((rw_freq rw) * (x - y)).
Proof.
  intros.
  unfold Covariance.
  rewrite random_wave_deriv_mean_zero.
  rewrite random_wave_deriv_mean_zero.
  assert (H_prod: forall w, (random_wave_deriv rw x w - 0) * (random_wave_deriv rw y w - 0) = 
          (rw_amp rw)^2 * (rw_freq rw)^2 * (sin ((rw_freq rw) * x + (rw_phase rw w)) * sin ((rw_freq rw) * y + (rw_phase rw w)))).
  {
    intros. unfold random_wave_deriv. repeat rewrite Rminus_0_r. ring.
  }
  rewrite (functional_extensionality _ _ H_prod).
  rewrite E_scal.
  
  (* E[sin(A+phi)sin(B+phi)] = 1/2 cos(A-B) *)
  (* sin(A)sin(B) = 1/2(cos(A-B) - cos(A+B)) *)
  
  assert (H_trig: forall w, sin ((rw_freq rw) * x + (rw_phase rw w)) * sin ((rw_freq rw) * y + (rw_phase rw w)) = 
          1/2 * (cos ((rw_freq rw) * (x - y)) - cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w)))).
  {
    intros w.
    assert (sin_mult_local: forall a b, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b))).
    { intros. rewrite cos_minus, cos_plus. lra. }
    
    rewrite sin_mult_local.
    f_equal. f_equal.
    - f_equal. lra.
    - f_equal. lra.
  }
  rewrite (functional_extensionality _ _ H_trig).
  rewrite E_scal.
  replace (fun w => cos (rw_freq rw * (x - y)) - cos (rw_freq rw * (x + y) + 2 * rw_phase rw w))
    with (fun w => 1 * (fun _ => cos (rw_freq rw * (x - y))) w + (-1) * (fun w => cos (rw_freq rw * (x + y) + 2 * rw_phase rw w)) w).
  2: { apply functional_extensionality. intros w0. lra. }
  rewrite E_linear.
  rewrite E_const.
  
  assert (H_cos2: Expectation (fun w => cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w))) = 0).
  {
     replace (fun w => cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w))) 
       with (fun w => cos (2 * (rw_phase rw w) + (rw_freq rw) * (x + y))).
     - apply (E_cos_2phase ((rw_freq rw) * (x + y)) (rw_phase rw)).
     - apply functional_extensionality. intros w. f_equal. lra.
  }
  rewrite H_cos2.
  unfold pow; simpl; field.
Qed.

Lemma independent_wave_deriv_field_uncorrelated : forall (a : RandomWave) (rf : RandomField) (x y : R),
  (forall rw, In rw rf -> rw <> a) ->
  (forall rw1 rw2, In rw1 (a :: rf) -> In rw2 (a :: rf) -> rw1 <> rw2 -> 
    Expectation (fun w => random_wave_deriv rw1 x w * random_wave_deriv rw2 y w) = 
    Expectation (fun w => random_wave_deriv rw1 x w) * Expectation (fun w => random_wave_deriv rw2 y w)) ->
  Expectation (fun w => random_wave_deriv a x w * random_field_deriv rf y w) = 0.
Proof.
  intros a rf x y H_distinct H_ind.
  induction rf.
  - simpl. 
    replace (fun w => random_wave_deriv a x w * 0) with (fun w : Omega => 0).
    2: { apply functional_extensionality. intros. lra. }
    apply E_const.
  - simpl.
    replace (fun w => random_wave_deriv a x w * (random_wave_deriv a0 y w + random_field_deriv rf y w))
      with (fun w => random_wave_deriv a x w * random_wave_deriv a0 y w + random_wave_deriv a x w * random_field_deriv rf y w).
    2: { apply functional_extensionality. intros. lra. }
    rewrite E_add.
    
    assert (H_first: Expectation (fun w => random_wave_deriv a x w * random_wave_deriv a0 y w) = 0).
    {
      rewrite H_ind.
      + rewrite random_wave_deriv_mean_zero. lra.
      + simpl. left. reflexivity.
      + simpl. right. left. reflexivity.
      + apply not_eq_sym. apply H_distinct. simpl. left. reflexivity.
    }
    rewrite H_first.
    
    assert (H_second: Expectation (fun w => random_wave_deriv a x w * random_field_deriv rf y w) = 0).
    {
      apply IHrf.
      + intros rw H_in. apply H_distinct. simpl. right. assumption.
      + intros rw1 rw2 H_in1 H_in2 H_neq.
        apply H_ind.
        * simpl. destruct H_in1; [left|right; right]; assumption.
        * simpl. destruct H_in2; [left|right; right]; assumption.
        * assumption.
    }
    rewrite H_second.
    lra.
Qed.

Lemma random_field_deriv_covariance_sum : forall (rf : RandomField) (x y : R),
  PairwiseIndependent rf ->
  NoDup rf ->
  Covariance (random_field_deriv rf x) (random_field_deriv rf y) = 
  fold_right Rplus 0 (map (fun rw => Covariance (random_wave_deriv rw x) (random_wave_deriv rw y)) rf).
Proof.
  intros rf x y H_ind H_nodup.
  
  induction rf.
  - simpl. unfold Covariance. repeat rewrite E_const. lra.
  - simpl.
    rewrite Covariance_mean_zero.
    2: { simpl. rewrite E_add. rewrite random_wave_deriv_mean_zero. rewrite random_field_deriv_mean_zero. lra. }
    2: { simpl. rewrite E_add. rewrite random_wave_deriv_mean_zero. rewrite random_field_deriv_mean_zero. lra. }
    
    (* Expand product *)
    assert (H_expand: Expectation (fun w => (random_wave_deriv a x w + random_field_deriv rf x w) * (random_wave_deriv a y w + random_field_deriv rf y w)) =
                      Expectation (fun w => random_wave_deriv a x w * random_wave_deriv a y w + 
                                            random_wave_deriv a x w * random_field_deriv rf y w +
                                            random_field_deriv rf x w * random_wave_deriv a y w +
                                            random_field_deriv rf x w * random_field_deriv rf y w)).
    {
      f_equal. apply functional_extensionality. intros w. ring.
    }
    rewrite H_expand.
    repeat rewrite E_add.
    
    (* Term 1: Cov(a, a) *)
    rewrite <- Covariance_mean_zero; [|apply random_wave_deriv_mean_zero|apply random_wave_deriv_mean_zero].
    
    (* Term 2: E[a(x)rest(y)] = 0 *)
    assert (H_cross1: Expectation (fun w => random_wave_deriv a x w * random_field_deriv rf y w) = 0).
    {
      apply independent_wave_deriv_field_uncorrelated.
      - intros rw H_in. inversion H_nodup as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
      - intros rw1 rw2 H_in1 H_in2 H_neq.
        unfold PairwiseIndependent in H_ind.
        apply (H_ind rw1 rw2); auto.
        + exists x. right. left. reflexivity.
        + exists y. right. left. reflexivity.
    }
    rewrite H_cross1.
    rewrite Rplus_0_r.

    (* Term 3: E[rest(x)a(y)] = 0 *)
    assert (H_cross2: Expectation (fun w => random_field_deriv rf x w * random_wave_deriv a y w) = 0).
    {
       assert (H_comm: Expectation (fun w => random_field_deriv rf x w * random_wave_deriv a y w) = 
                       Expectation (fun w => random_wave_deriv a y w * random_field_deriv rf x w)).
       { f_equal. apply functional_extensionality. intros w. ring. }
       rewrite H_comm.
       apply independent_wave_deriv_field_uncorrelated.
       - intros rw H_in. inversion H_nodup as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
       - intros rw1 rw2 H_in1 H_in2 H_neq.
         unfold PairwiseIndependent in H_ind.
         apply (H_ind rw1 rw2); auto.
         + exists y. right. left. reflexivity.
         + exists x. right. left. reflexivity.
    }
    rewrite H_cross2.
    rewrite Rplus_0_r.

    (* Term 4: E[rest(x)rest(y)] = Cov(rest, rest) *)
    rewrite <- Covariance_mean_zero; [|apply random_field_deriv_mean_zero|apply random_field_deriv_mean_zero].
    
    f_equal.
    apply IHrf.
    + unfold PairwiseIndependent in *. intros rw1 rw2 H_in1 H_in2 H_neq X Y H_X H_Y. 
      apply (H_ind rw1 rw2); simpl; try tauto; try assumption.
    + inversion H_nodup. assumption.
Qed.

Theorem random_field_deriv_stationary : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  exists (g : R -> R), forall (x y : R), Covariance (random_field_deriv rf x) (random_field_deriv rf y) = g (x - y).
Proof.
  intros rf H_ind H_nodup.
  induction rf.
  - exists (fun _ => 0). intros. simpl. unfold Covariance. repeat rewrite E_const. lra.
  - 
    assert (H_ind_sub: PairwiseIndependent rf).
    { unfold PairwiseIndependent in *. intros. apply H_ind with (rw1:=rw1) (rw2:=rw2); auto.
      simpl. right. assumption. simpl. right. assumption. }
    assert (H_nodup_sub: NoDup rf).
    { inversion H_nodup. assumption. }
    destruct (IHrf H_ind_sub H_nodup_sub) as [g_rest H_grest].
    
    exists (fun t => 1/2 * (rw_amp a)^2 * (rw_freq a)^2 * cos ((rw_freq a) * t) + g_rest t).
    intros x y.
    
    rewrite random_field_deriv_covariance_sum; auto.
    simpl.
    
    rewrite random_wave_deriv_stationary.
    
    f_equal.
    rewrite <- H_grest.
    rewrite random_field_deriv_covariance_sum; auto.
Qed.

Lemma random_wave_deriv2_stationary : forall (rw : RandomWave) (x y : R),
  Covariance (random_wave_deriv2 rw x) (random_wave_deriv2 rw y) = 
  1/2 * (rw_amp rw)^2 * (rw_freq rw)^4 * cos ((rw_freq rw) * (x - y)).
Proof.
  intros.
  unfold Covariance.
  rewrite random_wave_deriv2_mean_zero.
  rewrite random_wave_deriv2_mean_zero.
  assert (H_prod: forall w, (random_wave_deriv2 rw x w - 0) * (random_wave_deriv2 rw y w - 0) = 
          (rw_amp rw)^2 * (rw_freq rw)^4 * (cos ((rw_freq rw) * x + (rw_phase rw w)) * cos ((rw_freq rw) * y + (rw_phase rw w)))).
  {
    intros. unfold random_wave_deriv2. repeat rewrite Rminus_0_r. 
    ring.
  }
  rewrite (functional_extensionality _ _ H_prod).
  rewrite E_scal.
  
  assert (H_trig: forall w, cos ((rw_freq rw) * x + (rw_phase rw w)) * cos ((rw_freq rw) * y + (rw_phase rw w)) = 
          1/2 * (cos ((rw_freq rw) * (x - y)) + cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w)))).
  {
    intros w.
    assert (cos_mult_local: forall a b, cos a * cos b = 1/2 * (cos (a - b) + cos (a + b))).
    { intros. rewrite cos_minus, cos_plus. lra. }
    
    rewrite cos_mult_local.
    f_equal. f_equal.
    - f_equal. lra.
    - f_equal. lra.
  }
  rewrite (functional_extensionality _ _ H_trig).
  rewrite E_scal.
  replace (fun w => cos (rw_freq rw * (x - y)) + cos (rw_freq rw * (x + y) + 2 * rw_phase rw w))
    with (fun w => 1 * (fun _ => cos (rw_freq rw * (x - y))) w + 1 * (fun w => cos (rw_freq rw * (x + y) + 2 * rw_phase rw w)) w).
  2: { apply functional_extensionality. intros w0. lra. }
  rewrite E_linear.
  rewrite E_const.
  
  assert (H_cos2: Expectation (fun w => cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w))) = 0).
  {
     replace (fun w => cos ((rw_freq rw) * (x + y) + 2 * (rw_phase rw w))) 
       with (fun w => cos (2 * (rw_phase rw w) + (rw_freq rw) * (x + y))).
     - apply (E_cos_2phase ((rw_freq rw) * (x + y)) (rw_phase rw)).
     - apply functional_extensionality. intros w. f_equal. lra.
  }
  rewrite H_cos2.
  unfold pow; simpl; field.
Qed.

Lemma independent_wave_deriv2_field_uncorrelated : forall (a : RandomWave) (rf : RandomField) (x y : R),
  (forall rw, In rw rf -> rw <> a) ->
  (forall rw1 rw2, In rw1 (a :: rf) -> In rw2 (a :: rf) -> rw1 <> rw2 -> 
    Expectation (fun w => random_wave_deriv2 rw1 x w * random_wave_deriv2 rw2 y w) = 
    Expectation (fun w => random_wave_deriv2 rw1 x w) * Expectation (fun w => random_wave_deriv2 rw2 y w)) ->
  Expectation (fun w => random_wave_deriv2 a x w * random_field_deriv2 rf y w) = 0.
Proof.
  intros a rf x y H_distinct H_ind.
  induction rf.
  - simpl. 
    replace (fun w => random_wave_deriv2 a x w * 0) with (fun w : Omega => 0).
    2: { apply functional_extensionality. intros. lra. }
    apply E_const.
  - simpl.
    replace (fun w => random_wave_deriv2 a x w * (random_wave_deriv2 a0 y w + random_field_deriv2 rf y w))
      with (fun w => random_wave_deriv2 a x w * random_wave_deriv2 a0 y w + random_wave_deriv2 a x w * random_field_deriv2 rf y w).
    2: { apply functional_extensionality. intros. lra. }
    rewrite E_add.
    
    assert (H_first: Expectation (fun w => random_wave_deriv2 a x w * random_wave_deriv2 a0 y w) = 0).
    {
      rewrite H_ind.
      + rewrite random_wave_deriv2_mean_zero. lra.
      + simpl. left. reflexivity.
      + simpl. right. left. reflexivity.
      + apply not_eq_sym. apply H_distinct. simpl. left. reflexivity.
    }
    rewrite H_first.
    
    assert (H_second: Expectation (fun w => random_wave_deriv2 a x w * random_field_deriv2 rf y w) = 0).
    {
      apply IHrf.
      + intros rw H_in. apply H_distinct. simpl. right. assumption.
      + intros rw1 rw2 H_in1 H_in2 H_neq.
        apply H_ind.
        * simpl. destruct H_in1; [left|right; right]; assumption.
        * simpl. destruct H_in2; [left|right; right]; assumption.
        * assumption.
    }
    rewrite H_second.
    lra.
Qed.

Lemma random_field_deriv2_covariance_sum : forall (rf : RandomField) (x y : R),
  PairwiseIndependent rf ->
  NoDup rf ->
  Covariance (random_field_deriv2 rf x) (random_field_deriv2 rf y) = 
  fold_right Rplus 0 (map (fun rw => Covariance (random_wave_deriv2 rw x) (random_wave_deriv2 rw y)) rf).
Proof.
  intros rf x y H_ind H_nodup.
  
  induction rf.
  - simpl. unfold Covariance. repeat rewrite E_const. lra.
  - simpl.
    rewrite Covariance_mean_zero.
    2: { simpl. rewrite E_add. rewrite random_wave_deriv2_mean_zero. rewrite random_field_deriv2_mean_zero. lra. }
    2: { simpl. rewrite E_add. rewrite random_wave_deriv2_mean_zero. rewrite random_field_deriv2_mean_zero. lra. }
    
    (* Expand product *)
    assert (H_expand: Expectation (fun w => (random_wave_deriv2 a x w + random_field_deriv2 rf x w) * (random_wave_deriv2 a y w + random_field_deriv2 rf y w)) =
                      Expectation (fun w => random_wave_deriv2 a x w * random_wave_deriv2 a y w + 
                                            random_wave_deriv2 a x w * random_field_deriv2 rf y w +
                                            random_field_deriv2 rf x w * random_wave_deriv2 a y w +
                                            random_field_deriv2 rf x w * random_field_deriv2 rf y w)).
    {
      f_equal. apply functional_extensionality. intros w. ring.
    }
    rewrite H_expand.
    repeat rewrite E_add.
    
    (* Term 1: Cov(a, a) *)
    rewrite <- Covariance_mean_zero; [|apply random_wave_deriv2_mean_zero|apply random_wave_deriv2_mean_zero].
    
    (* Term 2: E[a(x)rest(y)] = 0 *)
    assert (H_cross1: Expectation (fun w => random_wave_deriv2 a x w * random_field_deriv2 rf y w) = 0).
    {
      apply independent_wave_deriv2_field_uncorrelated.
      - intros rw H_in. inversion H_nodup as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
      - intros rw1 rw2 H_in1 H_in2 H_neq.
        unfold PairwiseIndependent in H_ind.
        apply (H_ind rw1 rw2); auto.
        + exists x. right. right. reflexivity.
        + exists y. right. right. reflexivity.
    }
    rewrite H_cross1.
    rewrite Rplus_0_r.

    (* Term 3: E[rest(x)a(y)] = 0 *)
    assert (H_cross2: Expectation (fun w => random_field_deriv2 rf x w * random_wave_deriv2 a y w) = 0).
    {
       assert (H_comm: Expectation (fun w => random_field_deriv2 rf x w * random_wave_deriv2 a y w) = 
                       Expectation (fun w => random_wave_deriv2 a y w * random_field_deriv2 rf x w)).
       { f_equal. apply functional_extensionality. intros w. ring. }
       rewrite H_comm.
       apply independent_wave_deriv2_field_uncorrelated.
       - intros rw H_in. inversion H_nodup as [| ? ? H_notin H_dup_rf]; subst. intro H_eq. subst. apply H_notin. assumption.
       - intros rw1 rw2 H_in1 H_in2 H_neq.
         unfold PairwiseIndependent in H_ind.
         apply (H_ind rw1 rw2); auto.
         + exists y. right. right. reflexivity.
         + exists x. right. right. reflexivity.
    }
    rewrite H_cross2.
    rewrite Rplus_0_r.

    (* Term 4: E[rest(x)rest(y)] = Cov(rest, rest) *)
    rewrite <- Covariance_mean_zero; [|apply random_field_deriv2_mean_zero|apply random_field_deriv2_mean_zero].
    
    f_equal.
    apply IHrf.
    + unfold PairwiseIndependent in *. intros rw1 rw2 H_in1 H_in2 H_neq X Y H_X H_Y. 
      apply (H_ind rw1 rw2); simpl; try tauto; try assumption.
    + inversion H_nodup. assumption.
Qed.

Theorem random_field_deriv2_stationary : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  exists (g : R -> R), forall (x y : R), Covariance (random_field_deriv2 rf x) (random_field_deriv2 rf y) = g (x - y).
Proof.
  intros rf H_ind H_nodup.
  induction rf.
  - exists (fun _ => 0). intros. simpl. unfold Covariance. repeat rewrite E_const. lra.
  - 
    assert (H_ind_sub: PairwiseIndependent rf).
    { unfold PairwiseIndependent in *. intros. apply H_ind with (rw1:=rw1) (rw2:=rw2); auto.
      simpl. right. assumption. simpl. right. assumption. }
    assert (H_nodup_sub: NoDup rf).
    { inversion H_nodup. assumption. }
    destruct (IHrf H_ind_sub H_nodup_sub) as [g_rest H_grest].
    
    exists (fun t => 1/2 * (rw_amp a)^2 * (rw_freq a)^4 * cos ((rw_freq a) * t) + g_rest t).
    intros x y.
    
    rewrite random_field_deriv2_covariance_sum; auto.
    simpl.
    
    rewrite random_wave_deriv2_stationary.
    
    f_equal.
    rewrite <- H_grest.
    rewrite random_field_deriv2_covariance_sum; auto.
Qed.

Lemma random_field_deriv_variance_const : forall (rf : RandomField) (x y : R),
  PairwiseIndependent rf ->
  NoDup rf ->
  Variance (random_field_deriv rf x) = Variance (random_field_deriv rf y).
Proof.
  intros rf x y H_ind H_nodup.
  destruct (random_field_deriv_stationary rf H_ind H_nodup) as [g Hg].
  assert (H_var_cov: forall z, Variance (random_field_deriv rf z) = Covariance (random_field_deriv rf z) (random_field_deriv rf z)).
  { intros. unfold Variance, Covariance. f_equal. apply functional_extensionality. intros. unfold pow; simpl; ring. }
  rewrite H_var_cov.
  rewrite H_var_cov.
  rewrite Hg.
  rewrite Hg.
  replace (x - x) with 0 by lra.
  replace (y - y) with 0 by lra.
  reflexivity.
Qed.

Lemma random_field_deriv2_variance_const : forall (rf : RandomField) (x y : R),
  PairwiseIndependent rf ->
  NoDup rf ->
  Variance (random_field_deriv2 rf x) = Variance (random_field_deriv2 rf y).
Proof.
  intros rf x y H_ind H_nodup.
  destruct (random_field_deriv2_stationary rf H_ind H_nodup) as [g Hg].
  assert (H_var_cov: forall z, Variance (random_field_deriv2 rf z) = Covariance (random_field_deriv2 rf z) (random_field_deriv2 rf z)).
  { intros. unfold Variance, Covariance. f_equal. apply functional_extensionality. intros. unfold pow; simpl; ring. }
  rewrite H_var_cov.
  rewrite H_var_cov.
  rewrite Hg.
  rewrite Hg.
  replace (x - x) with 0 by lra.
  replace (y - y) with 0 by lra.
  reflexivity.
Qed.

Lemma random_field_deriv_isotropy : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  exists (h : R -> R), forall (x y : R), Covariance (random_field_deriv rf x) (random_field_deriv rf y) = h (Rabs (x - y)).
Proof.
  intros rf H_ind H_nodup.
  destruct (random_field_deriv_stationary rf H_ind H_nodup) as [g Hg].
  exists g.
  intros x y.
  rewrite Hg.
  
  (* Prove g(x-y) = g(|x-y|) *)
  assert (H_even: forall t, g t = g (-t)).
  {
    intros t.
    (* Let x=t, y=0. x-y=t. y-x=-t. *)
    assert (H_cov_sym: Covariance (random_field_deriv rf t) (random_field_deriv rf 0) = 
                       Covariance (random_field_deriv rf 0) (random_field_deriv rf t)).
    { unfold Covariance. f_equal. apply functional_extensionality. intros w. ring. }
    
    rewrite (Hg t 0) in H_cov_sym.
    rewrite (Hg 0 t) in H_cov_sym.
    replace (t - 0) with t in H_cov_sym by lra.
    replace (0 - t) with (-t) in H_cov_sym by lra.
    exact H_cov_sym.
  }
  
  destruct (Rcase_abs (x - y)) as [H_neg | H_pos].
  - rewrite (Rabs_left _ H_neg).
    rewrite H_even.
    reflexivity.
  - rewrite (Rabs_right _ H_pos).
    reflexivity.
Qed.

Lemma random_field_deriv2_isotropy : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  exists (h : R -> R), forall (x y : R), Covariance (random_field_deriv2 rf x) (random_field_deriv2 rf y) = h (Rabs (x - y)).
Proof.
  intros rf H_ind H_nodup.
  destruct (random_field_deriv2_stationary rf H_ind H_nodup) as [g Hg].
  exists g.
  intros x y.
  rewrite Hg.
  
  (* Prove g(x-y) = g(|x-y|) *)
  assert (H_even: forall t, g t = g (-t)).
  {
    intros t.
    (* Let x=t, y=0. x-y=t. y-x=-t. *)
    assert (H_cov_sym: Covariance (random_field_deriv2 rf t) (random_field_deriv2 rf 0) = 
                       Covariance (random_field_deriv2 rf 0) (random_field_deriv2 rf t)).
    { unfold Covariance. f_equal. apply functional_extensionality. intros w. ring. }
    
    rewrite (Hg t 0) in H_cov_sym.
    rewrite (Hg 0 t) in H_cov_sym.
    replace (t - 0) with t in H_cov_sym by lra.
    replace (0 - t) with (-t) in H_cov_sym by lra.
    exact H_cov_sym.
  }
  
  destruct (Rcase_abs (x - y)) as [H_neg | H_pos].
  - rewrite (Rabs_left _ H_neg).
    rewrite H_even.
    reflexivity.
  - rewrite (Rabs_right _ H_pos).
    reflexivity.
Qed.

Arguments random_wave_deriv : simpl never.
Arguments random_wave_deriv2 : simpl never.

Lemma random_field_deriv_variance_sum_formula : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  Variance (random_field_deriv rf 0) = 
  fold_right (fun w acc => acc + 1/2 * (rw_amp w)^2 * (rw_freq w)^2) 0 rf.
Proof.
  intros rf H_ind H_nodup.
  replace (Variance (random_field_deriv rf 0)) with (Covariance (random_field_deriv rf 0) (random_field_deriv rf 0)).
  2: { unfold Variance, Covariance. f_equal. apply functional_extensionality. intros. ring. }
  rewrite (random_field_deriv_covariance_sum rf 0 0); auto.
  induction rf.
  - simpl. reflexivity.
  - simpl. rewrite Rplus_comm. f_equal.
    { apply IHrf. unfold PairwiseIndependent in *. intros w1 w2 H1 H2. apply H_ind; auto. simpl. right. assumption. simpl. right. assumption. inversion H_nodup; assumption. }
    rewrite Covariance_mean_zero.
    2: { apply random_wave_deriv_mean_zero. }
    2: { apply random_wave_deriv_mean_zero. }
    unfold random_wave_deriv.
    assert (H_rw_simpl: forall w, - (rw_amp a) * (rw_freq a) * sin (rw_freq a * 0 + rw_phase a w) = rw_amp a * - rw_freq a * sin (rw_phase a w)).
    { intros. rewrite Rmult_0_r, Rplus_0_l. ring. }
    replace (fun w => (- (rw_amp a) * (rw_freq a) * sin (rw_freq a * 0 + rw_phase a w)) *
                      (- (rw_amp a) * (rw_freq a) * sin (rw_freq a * 0 + rw_phase a w)))
      with (fun w => (rw_amp a * - rw_freq a * sin (rw_phase a w)) *
                     (rw_amp a * - rw_freq a * sin (rw_phase a w))).
    2: { apply functional_extensionality. intros. rewrite H_rw_simpl. reflexivity. }
    assert (H_eq: Expectation (fun w => (rw_amp a * - rw_freq a * sin (rw_phase a w)) *
                                        (rw_amp a * - rw_freq a * sin (rw_phase a w))) =
                  1/2 * (rw_amp a)^2 * (rw_freq a)^2).
    {
      assert (H_sin: forall w, sin (rw_phase a w) * sin (rw_phase a w) = (sin (rw_phase a w))^2).
      { intros. ring. }
      set (c := (rw_amp a)^2 * (rw_freq a)^2).
      set (X := fun w => (sin (rw_phase a w))^2).
      replace (fun w => (rw_amp a * - rw_freq a * sin (rw_phase a w)) * (rw_amp a * - rw_freq a * sin (rw_phase a w)))
        with (fun w => c * X w).
      2: { unfold c, X. apply functional_extensionality. intros. ring_simplify. repeat rewrite H_sin. ring. }
      
      replace (Expectation (fun w => c * X w)) with (c * Expectation X).
      2: { rewrite E_scal. reflexivity. }
      
      replace (Expectation X) with (1/2).
      2: {
        unfold X.
        replace (fun w => (sin (rw_phase a w))^2) with (fun w => (sin (0 + rw_phase a w))^2).
        2: { apply functional_extensionality. intros. rewrite Rplus_0_l. reflexivity. }
        rewrite E_sin_sq_uniform. reflexivity.
      }
      subst c.
      rewrite Rmult_comm. rewrite <- Rmult_assoc. reflexivity.
    }
    rewrite H_eq.
    ring.
Qed.

Lemma random_field_deriv2_variance_sum_formula : forall (rf : RandomField),
  PairwiseIndependent rf ->
  NoDup rf ->
  Variance (random_field_deriv2 rf 0) = 
  fold_right (fun w acc => acc + 1/2 * (rw_amp w)^2 * (rw_freq w)^4) 0 rf.
Proof.
  intros rf H_ind H_nodup.
  replace (Variance (random_field_deriv2 rf 0)) with (Covariance (random_field_deriv2 rf 0) (random_field_deriv2 rf 0)).
  2: { unfold Variance, Covariance. f_equal. apply functional_extensionality. intros. ring. }
  rewrite (random_field_deriv2_covariance_sum rf 0 0); auto.
  induction rf.
  - simpl. reflexivity.
  - simpl. rewrite Rplus_comm. f_equal.
    { apply IHrf. unfold PairwiseIndependent in *. intros w1 w2 H1 H2. apply H_ind; auto. simpl. right. assumption. simpl. right. assumption. inversion H_nodup; assumption. }
    rewrite Covariance_mean_zero.
    2: { apply random_wave_deriv2_mean_zero. }
    2: { apply random_wave_deriv2_mean_zero. }
    assert (H_simpl: forall w, random_wave_deriv2 a 0 w = rw_amp a * - (rw_freq a * rw_freq a) * cos (rw_phase a w)).
    { intros. unfold random_wave_deriv2. rewrite Rmult_0_r, Rplus_0_l. ring. }
    replace (fun w => random_wave_deriv2 a 0 w * random_wave_deriv2 a 0 w)
      with (fun w => (rw_amp a * - (rw_freq a * rw_freq a) * cos (rw_phase a w)) *
                     (rw_amp a * - (rw_freq a * rw_freq a) * cos (rw_phase a w))).
    2: { apply functional_extensionality. intros. rewrite H_simpl. reflexivity. }
    assert (H_eq: Expectation (fun w => (rw_amp a * - (rw_freq a * rw_freq a) * cos (rw_phase a w)) *
                                        (rw_amp a * - (rw_freq a * rw_freq a) * cos (rw_phase a w))) =
                  1/2 * (rw_amp a)^2 * (rw_freq a)^4).
    {
      assert (H_cos: forall w, cos (rw_phase a w) * cos (rw_phase a w) = (cos (rw_phase a w))^2).
      { intros. ring. }
      set (c := (rw_amp a)^2 * (rw_freq a)^4).
      set (X := fun w => (cos (rw_phase a w))^2).
      replace (fun w => (rw_amp a * - (rw_freq a * rw_freq a) * cos (rw_phase a w)) * (rw_amp a * - (rw_freq a * rw_freq a) * cos (rw_phase a w)))
         with (fun w => c * X w).
       2: { unfold c, X. apply functional_extensionality. intros. ring_simplify. repeat rewrite H_cos. ring. }
       
       replace (Expectation (fun w => c * X w)) with (c * Expectation X).
       2: { rewrite E_scal. reflexivity. }
       
       replace (Expectation X) with (1/2).
       2: {
         unfold X.
         replace (fun w => (cos (rw_phase a w))^2) with (fun w => (cos (0 + rw_phase a w))^2).
         2: { apply functional_extensionality. intros. rewrite Rplus_0_l. reflexivity. }
         rewrite E_cos_sq_uniform. reflexivity.
       }
       subst c.
      rewrite Rmult_comm. rewrite <- Rmult_assoc. reflexivity.
    }
    rewrite H_eq.
    ring.
Qed.
