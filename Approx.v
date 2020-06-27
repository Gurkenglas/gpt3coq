Require Import ZArith.
Open Scope Z_scope.

Notation "x '/<' y" := (x / y)
  (at level 40, left associativity).

Definition div_nearest_down (x y : Z) : Z := (1 + (2 * x - 1) /< y) /< 2.

Notation "x '/~<' y" := (div_nearest_down x y)
  (at level 40, left associativity).

Definition div_nearest_up (x y : Z) : Z := (1 + 2 * x /< y) /< 2.

Notation "x '/~>' y" := (div_nearest_up x y)
  (at level 40, left associativity).

Definition clamp (l u x : Z) : Z :=
  if x <? l then l else
  if x >? u then u else x.

Definition approx (l u m x : Z) : Z :=
  if x <? l then l else
  if x >? u then u else
  l + m * ((1 + (2 * (x - l) - 1) /< m) /< 2).

Definition approx_valid (l u m x : Z) : Prop :=
  l <= u /\ m > 0 /\ (u - l) mod m = 0.

Definition approx' (l u m x : Z) : Z :=
  l + m * ((clamp l u x - l) /~< m).

Import Z.

Theorem approx_lower_bound : forall l u m x : Z,
  approx_valid l u m x -> approx l u m x >= l.
Proof.
  unfold approx, approx_valid. intros l u m x [Hlelu [Hgtm0 Heq]].
  destruct (ltb_spec x l) as [Hltxl | Hlelx].
  - omega.
  - destruct (gtb_spec x u) as [Hltux | Hlexu].
    + omega.
    + apply le_ge. rewrite <- (add_0_r l) at 1. apply Zplus_le_compat_l.
      rewrite <- (mul_0_r m). apply mul_le_mono_nonneg_l.
      * omega.
      * apply div_pos.
          ++ destruct (eqb_spec l x) as [Heqlx | Feqlx].
            ** apply eq_le_incl. rewrite Heqlx. rewrite sub_diag.
              rewrite mul_0_r. rewrite sub_0_l.
              destruct (leb_spec m 1).
              --- replace m with 1 by omega. reflexivity.
              --- rewrite Z_div_nz_opp_full.
                +++ rewrite div_1_l by omega. reflexivity.
                +++ rewrite mod_1_l by omega. omega.
            ** assert (l < x) as Hltlx by omega.
              assert (exists y : Z, succ y = x - l).
              exists (pred (x - l)). apply succ_pred.
              induction H as [y H]. rewrite <- H. rewrite mul_succ_r.
              replace (2 * y + 2 - 1) with (2 * y + 1) by omega.
              rewrite <- (add_0_r 0). apply add_le_mono.
              --- omega.
              --- rewrite <- (div_0_l m) by omega. apply div_le_mono.
                +++ omega.
                +++ omega.
          ++ omega. Qed.

Theorem approx_upper_bound : forall l u m x : Z,
  approx_valid l u m x -> approx l u m x <= u.
Proof.
  unfold approx, approx_valid. intros l u m x [Hlelu [Hgtm0 Heq]].
  destruct (ltb_spec x l) as [Hltxl | Hlelx].
  - omega.
  - destruct (gtb_spec x u) as [Hltux | Hlexu].
    + omega.
    + (* by symmetry. *) Admitted.

Theorem approx_divisible_lower : forall l u m x : Z,
  approx_valid l u m x -> (approx l u m x - l) mod m = 0.
Proof.
  unfold approx, approx_valid. intros l u m x [Hlelu [Hgtm0 Heq]].
  destruct (ltb_spec x l) as [Hltxl | Hlelx].
  - rewrite sub_diag. rewrite mod_0_l by omega. reflexivity.
  - destruct (gtb_spec x u) as [Hltux | Hlexu].
    + apply Heq.
    + rewrite add_simpl_l. rewrite (mul_comm m). apply Z_mod_mult. Qed.

Theorem approx_divisible_upper : forall l u m x : Z,
  approx_valid l u m x -> (u - approx l u m x) mod m = 0.
Proof.
  unfold approx, approx_valid. intros l u m x [Hlelu [Hgtm0 Heq]].
  destruct (ltb_spec x l) as [Hltxl | Hlelx].
  - apply Heq.
  - destruct (gtb_spec x u) as [Hltux | Hlexu].
    + rewrite sub_diag. apply mod_0_l. omega.
    + rewrite sub_add_distr. rewrite Zminus_mod. rewrite Heq.
      rewrite sub_0_l. apply Z_mod_zero_opp.
      * omega.
      * rewrite Zmod_mod. rewrite (mul_comm m). apply Z_mod_mult. Defined.
