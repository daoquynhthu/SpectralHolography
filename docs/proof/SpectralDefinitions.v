
(* SpectralDefinitions.v *)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

(* --- Definition of a Single Wave Component --- *)
(* A wave is defined by amplitude (A), frequency (k), and phase (phi). *)
Record Wave : Type := mkWave {
  amp : R;
  freq : R;
  phase : R
}.

(* The function value of a single wave at point x: A * cos(k * x + phi) *)
Definition wave_eval (w : Wave) (x : R) : R :=
  (amp w) * cos ((freq w) * x + (phase w)).

(* --- Definition of a Spectral Landscape (Sum of Waves) --- *)
(* A landscape is a list of waves. *)
Definition Landscape := list Wave.

(* Evaluation of the landscape at point x is the sum of wave evaluations. *)
Fixpoint landscape_eval (l : Landscape) (x : R) : R :=
  match l with
  | nil => 0
  | w :: rest => (wave_eval w x) + (landscape_eval rest x)
  end.

(* --- Basic Analytic Properties --- *)

(* Lemma: The derivative of a single wave exists and is computable. *)
(* wave'(x) = -A * k * sin(k * x + phi) *)

Definition wave_deriv (w : Wave) (x : R) : R :=
  - (amp w) * (freq w) * sin ((freq w) * x + (phase w)).

Lemma wave_is_derivable : forall (w : Wave) (x : R),
  derivable_pt (wave_eval w) x.
Proof.
  intros w x.
  unfold wave_eval.
  apply derivable_pt_mult.
  - apply derivable_pt_const.
  - apply derivable_pt_comp with (f1 := fun x => (freq w) * x + (phase w)) (f2 := cos).
    + apply derivable_pt_plus.
      * apply derivable_pt_mult.
        -- apply derivable_pt_const.
        -- apply derivable_pt_id.
      * apply derivable_pt_const.
    + apply derivable_pt_cos.
Qed.

(* Lemma: The derivative of a single wave is equal to the expected formula. *)
Lemma derive_wave_correct : forall (w : Wave) (x : R),
  derive_pt (wave_eval w) x (wave_is_derivable w x) = wave_deriv w x.
Proof.
  intros.
  apply derive_pt_eq.
  unfold wave_eval, wave_deriv.

  (* f1 = inner linear function *)
  set (f1 := fun x => (freq w) * x + (phase w)).
  assert (H_f1: derivable_pt_lim f1 x (freq w)).
  {
    unfold f1.
    assert (H_lim: derivable_pt_lim (fun x => freq w * x + phase w) x (freq w * 1 + 0)).
    {
      apply derivable_pt_lim_plus with (f1 := fun x => freq w * x) (f2 := fun _ => phase w).
      - assert (H_prod: derivable_pt_lim (fun x => freq w * x) x (0 * x + freq w * 1)).
        {
          apply derivable_pt_lim_mult with (f1 := fun _ => freq w) (f2 := fun x => x).
          - apply derivable_pt_lim_const.
          - apply derivable_pt_lim_id.
        }
        replace (freq w * 1) with (0 * x + freq w * 1) by lra.
        exact H_prod.
      - apply derivable_pt_lim_const.
    }
    assert (Eq: freq w * 1 + 0 = freq w) by lra.
    rewrite Eq in H_lim.
    exact H_lim.
  }

  (* g = outer function *)
  set (g := fun y => amp w * cos y).
  assert (H_g: derivable_pt_lim g (f1 x) (- amp w * sin (f1 x))).
  {
    unfold g.
    assert (H_lim_g: derivable_pt_lim (fun y => amp w * cos y) (f1 x) (0 * cos (f1 x) + amp w * (- sin (f1 x)))).
    {
      apply derivable_pt_lim_mult with (f1 := fun _ => amp w) (f2 := cos).
      - apply derivable_pt_lim_const.
      - apply derivable_pt_lim_cos.
    }
    assert (Eq: 0 * cos (f1 x) + amp w * (- sin (f1 x)) = - amp w * sin (f1 x)) by lra.
    rewrite Eq in H_lim_g.
    exact H_lim_g.
  }

  (* Combine with comp *)
  replace (- (amp w) * (freq w) * sin ((freq w) * x + (phase w)))
    with ((- amp w * sin (f1 x)) * (freq w)).
  2: { unfold f1. lra. }

  change (fun x => amp w * cos ((freq w) * x + (phase w))) with (fun x => g (f1 x)).

  apply derivable_pt_lim_comp with (f1 := f1) (f2 := g).
   - exact H_f1.
   - exact H_g.
Qed.

(* Lemma: A landscape (finite sum of waves) is differentiable everywhere. *)
Lemma landscape_is_derivable : forall (l : Landscape) (x : R),
  derivable_pt (landscape_eval l) x.
Proof.
  intros l x.
  induction l as [| w rest IH].
  - (* Base case: nil *)
    simpl.
    apply derivable_pt_const.
  - (* Inductive step: w :: rest *)
    simpl.
    apply derivable_pt_plus.
    + apply wave_is_derivable.
    + apply IH.
Qed.

(* Definition of the derivative of a landscape *)
Fixpoint landscape_deriv_func (l : Landscape) (x : R) : R :=
  match l with
  | nil => 0
  | w :: rest => (wave_deriv w x) + (landscape_deriv_func rest x)
  end.

(* Lemma: The derivative of the landscape is the sum of wave derivatives. *)
Lemma derive_landscape_correct : forall (l : Landscape) (x : R),
  derive_pt (landscape_eval l) x (landscape_is_derivable l x) = landscape_deriv_func l x.
Proof.
  intros.
  apply derive_pt_eq.
  induction l.
  - simpl. apply derivable_pt_lim_const.
  - simpl.
    apply derivable_pt_lim_plus.
    + rewrite <- (derive_wave_correct a x).
      exact (proj2_sig (wave_is_derivable a x)).
    + exact IHl.
Qed.

(* --- Second Derivative Properties --- *)

(* wave''(x) = -A * k^2 * cos(k * x + phi) *)
Definition wave_deriv2 (w : Wave) (x : R) : R :=
  - (amp w) * (freq w) * (freq w) * cos ((freq w) * x + (phase w)).

Lemma wave_deriv_is_derivable : forall (w : Wave) (x : R),
  derivable_pt (wave_deriv w) x.
Proof.
  intros w x.
  unfold wave_deriv.
  apply derivable_pt_mult.
  - apply derivable_pt_mult.
    + apply derivable_pt_opp.
      apply derivable_pt_const.
    + apply derivable_pt_const.
  - apply derivable_pt_comp with (f1 := fun x => (freq w) * x + (phase w)) (f2 := sin).
    + apply derivable_pt_plus.
      * apply derivable_pt_mult.
        -- apply derivable_pt_const.
        -- apply derivable_pt_id.
      * apply derivable_pt_const.
    + apply derivable_pt_sin.
Qed.

Lemma derive_wave_deriv_correct : forall (w : Wave) (x : R),
  derive_pt (wave_deriv w) x (wave_deriv_is_derivable w x) = wave_deriv2 w x.
Proof.
  intros.
  apply derive_pt_eq.
  unfold wave_deriv, wave_deriv2.

  set (f1 := fun x => (freq w) * x + (phase w)).
  assert (H_f1: derivable_pt_lim f1 x (freq w)).
  {
    unfold f1.
    assert (H_lim: derivable_pt_lim (fun x => freq w * x + phase w) x (freq w * 1 + 0)).
    {
      apply derivable_pt_lim_plus with (f1 := fun x => freq w * x) (f2 := fun _ => phase w).
      - assert (H_prod: derivable_pt_lim (fun x => freq w * x) x (0 * x + freq w * 1)).
        {
          apply derivable_pt_lim_mult with (f1 := fun _ => freq w) (f2 := fun x => x).
          - apply derivable_pt_lim_const.
          - apply derivable_pt_lim_id.
        }
        replace (freq w * 1) with (0 * x + freq w * 1) by lra.
        exact H_prod.
      - apply derivable_pt_lim_const.
    }
    assert (Eq: freq w * 1 + 0 = freq w) by lra.
    rewrite Eq in H_lim.
    exact H_lim.
  }

  set (g := fun y => - amp w * freq w * sin y).
  assert (H_g: derivable_pt_lim g (f1 x) (- amp w * freq w * cos (f1 x))).
  {
    unfold g.
    assert (H_lim_g: derivable_pt_lim (fun y => (- amp w * freq w) * sin y) (f1 x) 
             (0 * sin (f1 x) + (- amp w * freq w) * (cos (f1 x)))).
    {
       apply derivable_pt_lim_mult with (f1 := fun _ => - amp w * freq w) (f2 := sin).
       - apply derivable_pt_lim_const.
       - apply derivable_pt_lim_sin.
    }
    assert (Eq: 0 * sin (f1 x) + (- amp w * freq w) * cos (f1 x) = - amp w * freq w * cos (f1 x)) by lra.
    rewrite Eq in H_lim_g.
    exact H_lim_g.
  }

  replace (- (amp w) * (freq w) * (freq w) * cos ((freq w) * x + (phase w)))
    with ((- amp w * freq w * cos (f1 x)) * (freq w)).
  2: { unfold f1. lra. }

  change (fun x => - amp w * freq w * sin ((freq w) * x + (phase w))) 
    with (fun x => g (f1 x)).

  apply derivable_pt_lim_comp with (f1 := f1) (f2 := g).
  - exact H_f1.
  - exact H_g.
Qed.

Fixpoint landscape_deriv2_func (l : Landscape) (x : R) : R :=
  match l with
  | nil => 0
  | w :: rest => (wave_deriv2 w x) + (landscape_deriv2_func rest x)
  end.

Lemma landscape_deriv_is_derivable : forall (l : Landscape) (x : R),
  derivable_pt (landscape_deriv_func l) x.
Proof.
  intros l x.
  induction l as [| w rest IH].
  - simpl. apply derivable_pt_const.
  - simpl. apply derivable_pt_plus.
    + apply wave_deriv_is_derivable.
    + apply IH.
Qed.

Lemma derive_landscape_deriv_correct : forall (l : Landscape) (x : R),
  derive_pt (landscape_deriv_func l) x (landscape_deriv_is_derivable l x) = landscape_deriv2_func l x.
Proof.
  intros.
  apply derive_pt_eq.
  induction l.
  - simpl. apply derivable_pt_lim_const.
  - simpl.
    apply derivable_pt_lim_plus.
    + rewrite <- (derive_wave_deriv_correct a x).
      exact (proj2_sig (wave_deriv_is_derivable a x)).
    + exact IHl.
Qed.
