From Coq.Strings Require Import
  Ascii
  String.
From Whiskey Require Import
  Invert.

Fixpoint slow_rev s :=
  match s with
  | EmptyString => EmptyString
  | String hd tl => append (slow_rev tl) (String hd "")
  end.

Example slow_rev_abc : slow_rev "abc" = "cba"%string. Proof. reflexivity. Qed.

Fixpoint rev_str_acc s acc :=
  match s with
  | EmptyString => acc
  | String hd tl => rev_str_acc tl (String hd acc)
  end.

Definition rev_str s := rev_str_acc s "".
Arguments rev_str s/. (* <https://stackoverflow.com/a/50957824> *)

Example rev_str_abc : rev_str "abc" = "cba"%string. Proof. reflexivity. Qed.

Lemma str_app_assoc : forall a b c, append a (append b c) = append (append a b) c.
Proof.
  induction a. { reflexivity. }
  intros. simpl in *.
  rewrite IHa. reflexivity.
Qed.

Lemma rev_append_app : forall s acc,
  rev_str_acc s acc = append (slow_rev s) acc.
Proof. induction s. { reflexivity. } intros. simpl. rewrite IHs. rewrite <- str_app_assoc. reflexivity. Qed.

Theorem rev_str_is_slow_rev : forall s, slow_rev s = rev_str s.
Proof.
  induction s. { reflexivity. }
  unfold rev_str. simpl.
  symmetry. apply rev_append_app.
Qed.

Lemma slow_rev_pop : forall hd tl, slow_rev (String hd tl) = (slow_rev tl ++ String hd "")%string.
Proof. intros. generalize dependent hd. induction tl; reflexivity. Qed.

Lemma slow_rev_pop_back : forall hd tl,
  slow_rev (tl ++ String hd "")%string = String hd (slow_rev tl).
Proof.
  intros. generalize dependent hd.
  induction tl. { reflexivity. } intros.
  simpl in *. rewrite IHtl. reflexivity.
Qed.

Lemma str_app_nil_r : forall s, (s ++ "")%string = s.
Proof. induction s. { reflexivity. } simpl. rewrite IHs. reflexivity. Qed.

Theorem rev_str_involutive : forall s, rev_str (rev_str s) = s.
Proof.
  induction s. { reflexivity. }
  unfold rev_str in *. simpl.
  repeat rewrite rev_append_app.
  rewrite slow_rev_pop_back.
  repeat rewrite rev_str_is_slow_rev.
  unfold rev_str. rewrite IHs.
  rewrite str_app_nil_r.
  reflexivity.
Qed.

Fixpoint str_split_last_rec hd tl :=
  match tl with
  | EmptyString => (EmptyString, hd)
  | String hd' tl' => let (hd'', tl'') := str_split_last_rec hd' tl' in
      (String hd hd'', tl'')
  end.

Definition str_split_last s :=
  match s with
  | EmptyString => None
  | String hd tl => Some (str_split_last_rec hd tl)
  end.
Arguments str_split_last s/.

Example str_split_last_abcdefg : str_split_last "abcdefg" = Some ("abcdef"%string, "g"%char).
Proof. reflexivity. Qed.

Example str_split_last_none : str_split_last "" = None.
Proof. reflexivity. Qed.

Example str_split_last_singleton : str_split_last "c" = Some (""%string, "c"%char).
Proof. reflexivity. Qed.

Theorem rev_str_eq_iff a b : a = b <-> rev_str a = rev_str b.
Proof.
  generalize dependent b. induction a; intros.
  - split; intros.
    + subst. reflexivity.
    + destruct b. { reflexivity. }
      eapply f_equal in H. repeat rewrite rev_str_involutive in H. inversion H.
  - split.
    + intros. subst. reflexivity.
    + generalize dependent IHa.
      generalize dependent a0.
      generalize dependent a.
      induction b; intros; eapply f_equal in H; repeat rewrite rev_str_involutive in H; invert H.
      reflexivity.
Qed.

Theorem rev_str_swap a b: rev_str a = b <-> a = rev_str b.
Proof. split; intros; rewrite rev_str_eq_iff in H; rewrite rev_str_involutive in H; assumption. Qed.
