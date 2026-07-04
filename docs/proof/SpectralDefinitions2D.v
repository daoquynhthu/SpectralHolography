Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

(* --- 2D Vector Definitions --- *)

Record Vector2D : Type := mkVector2D {
  vec_x : R;
  vec_y : R
}.

Definition dot_product (v1 v2 : Vector2D) : R :=
  (vec_x v1) * (vec_x v2) + (vec_y v1) * (vec_y v2).

Definition vector_add (v1 v2 : Vector2D) : Vector2D :=
  mkVector2D (vec_x v1 + vec_x v2) (vec_y v1 + vec_y v2).

Definition vector_sub (v1 v2 : Vector2D) : Vector2D :=
  mkVector2D (vec_x v1 - vec_x v2) (vec_y v1 - vec_y v2).

Definition vector_scale (c : R) (v : Vector2D) : Vector2D :=
  mkVector2D (c * vec_x v) (c * vec_y v).

Definition vector_norm_sq (v : Vector2D) : R :=
  (vec_x v)^2 + (vec_y v)^2.

Definition vector_norm (v : Vector2D) : R :=
  sqrt (vector_norm_sq v).

(* --- 2D Random Wave Definition --- *)

(* A 2D wave is defined by amplitude A, frequency vector k, and phase phi. *)
(* f(x) = A * cos(k . x + phi) *)
Record Wave2D : Type := mkWave2D {
  amp2d : R;
  freq2d : Vector2D;
  phase2d : R
}.

Definition wave2d_eval (w : Wave2D) (x : Vector2D) : R :=
  (amp2d w) * cos (dot_product (freq2d w) x + (phase2d w)).

(* --- 2D Random Field Definition --- *)

(* A 2D random field is a sum of 2D waves *)
Definition Landscape2D := list Wave2D.

Fixpoint landscape2d_eval (l : Landscape2D) (x : Vector2D) : R :=
  match l with
  | nil => 0
  | w :: rest => (wave2d_eval w x) + (landscape2d_eval rest x)
  end.

(* --- Probability Space Definitions (copied from 1D) --- *)

(* We define a probability space Omega for the random phases *)
Definition Omega := nat -> R. (* A sequence of random numbers *)

(* A Random Wave is a function from Omega to Wave2D *)
(* Usually, only the phase is random (uniform in [0, 2pi]) *)
(* The amplitude and frequency vector are fixed parameters of the spectral density *)
Record RandomWave2D : Type := mkRandomWave2D {
  rw_amp2d : R;
  rw_freq2d : Vector2D;
  rw_phase2d : Omega -> R
}.

Definition random_wave2d_eval (rw : RandomWave2D) (x : Vector2D) (w : Omega) : R :=
  (rw_amp2d rw) * cos (dot_product (rw_freq2d rw) x + (rw_phase2d rw w)).

Definition RandomField2D := list RandomWave2D.

Fixpoint random_field2d_eval (rf : RandomField2D) (x : Vector2D) (w : Omega) : R :=
  match rf with
  | nil => 0
  | rw :: rest => (random_wave2d_eval rw x w) + (random_field2d_eval rest x w)
  end.

(* --- Expectation and Variance --- *)

(* We assume a simplified expectation operator for the phases *)
(* E[X] = integral over phases *)
Parameter Expectation : (Omega -> R) -> R.

(* Basic properties of Expectation *)
Axiom E_linear : forall (X Y : Omega -> R) (a b : R),
  Expectation (fun w => a * X w + b * Y w) = a * Expectation X + b * Expectation Y.

Axiom E_const : forall (c : R), Expectation (fun w => c) = c.

(* Key property: Uniform phase assumption *)
(* If phi is uniform in [0, 2pi], then E[cos(theta + phi)] = 0 *)
Axiom E_cos_uniform : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => cos (theta + phi w)) = 0.

Axiom E_sin_uniform : forall (theta : R) (phi : Omega -> R),
  Expectation (fun w => sin (theta + phi w)) = 0.

(* Key property 2: Independence of phases *)
(* E[cos(theta1 + phi1) * cos(theta2 + phi2)] = 0 if phi1, phi2 independent *)
(* We need a more precise definition of independence for the list of waves *)

Definition Variance (X : Omega -> R) : R :=
  Expectation (fun w => (X w - Expectation X)^2).

Definition Covariance (X Y : Omega -> R) : R :=
  Expectation (fun w => (X w - Expectation X) * (Y w - Expectation Y)).

(* --- Bessel Function Definition --- *)

(* J0(x) is the Bessel function of the first kind of order 0 *)
(* It appears in the covariance of 2D isotropic fields *)
Parameter BesselJ0 : R -> R.

(* Asymptotic behavior of J0 *)
(* J0(x) ~ sqrt(2 / (pi * x)) * cos(x - pi/4) *)
Axiom BesselJ0_decay : forall (x : R),
  x > 0 -> Rabs (BesselJ0 x) <= 1 / sqrt x. (* Simplified bound for proof purposes *)
