From Coq Require Import
  Arith
  Nat
  Strings.Ascii.
From Whiskey Require Import Util.Invert.

(* From <https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html> *)
Inductive reflect P : bool -> Prop :=
  | ReflectT :  P -> reflect P true
  | ReflectF : ~P -> reflect P false.

Theorem reflect_iff P b : reflect P b <-> (P <-> b = true).
Proof.
  split; intros.
  - (* reflect P b -> (P <-> b = true) *) split; intros.
    + (* P -> b = true *) invert H; [reflexivity | apply H1 in H0; destruct H0].
    + (* b = true -> P *) invert H; [assumption | discriminate H2].
  - (* (P <-> b = true) -> reflect P b *) destruct H. destruct b.
    + (* reflect P true  *) constructor. apply H0. reflexivity.
    + (* reflect P false *) constructor. intros C. apply H in C. discriminate C.
Qed.

Theorem reflect_nat_eq a b : reflect (a = b) (a =? b).
Proof.
  destruct (a =? b) eqn:E; constructor;
  [rewrite Nat.eqb_eq in E | rewrite Nat.eqb_neq in E];
  assumption.
Qed.

Theorem reflect_bool_eq a b : reflect (a = b) (Bool.eqb a b).
Proof. destruct a; destruct b; constructor; try reflexivity; intros C; discriminate C. Qed.

Theorem reflect_ascii_eq a b : reflect (a = b) (Ascii.eqb a b).
Proof.
  destruct (reflect_nat_eq (nat_of_ascii a) (nat_of_ascii b)).
  - eapply f_equal in H. repeat rewrite ascii_nat_embedding in H.
    assert (A: Ascii.eqb a b = true). { apply Ascii.eqb_eq. assumption. } rewrite A.
    constructor. assumption.
  - assert (A: Ascii.eqb a b = false). { apply Ascii.eqb_neq. intros C; subst. apply H. reflexivity. } rewrite A.
    constructor. apply Ascii.eqb_neq. assumption.
Qed.
