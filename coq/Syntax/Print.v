(* All the ways a value could be printed (even hideously unreadable ones). *)

From Coq Require Import
  Arith
  Decimal
  DecimalNat
  Strings.Ascii
  Strings.String.
From Whiskey Require Import
  Data.Literal
  Data.Value
  Util.Invert
  Util.Reflect
  Util.RevStr.

Definition tab_n := 9.
Definition space_n := nat_of_ascii " ".
Definition newline_n := 10.
Definition tab := ascii_of_nat tab_n.
Definition space := " "%char.
Definition newline := ascii_of_nat newline_n.

Inductive Whitespace : ascii -> Prop :=
  | WSTab : Whitespace tab
  | WSSpace : Whitespace space
  | WSNewLine : Whitespace newline.
Arguments Whitespace c%char.

Definition is_space_n c := orb (orb (c =? tab_n) (c =? space_n)) (c =? newline_n).
Arguments is_space_n c/.
Definition is_space c := is_space_n (nat_of_ascii c).
Arguments is_space c%char/.

Theorem reflect_space : forall c, reflect (Whitespace c) (is_space c).
Proof.
  intros. apply reflect_iff. split; intros.
  - invert H; reflexivity.
  - unfold is_space in H. unfold is_space_n in H.
    repeat (apply Bool.orb_prop in H; destruct H);
    rewrite Nat.eqb_eq in H;
    apply (f_equal ascii_of_nat) in H; rewrite ascii_nat_embedding in H;
    subst; constructor.
Qed.
Arguments reflect_space c%char.

Fixpoint base_ten_dec d :=
  match d with
  | Nil => EmptyString
  | D0 tl => String "0" (base_ten_dec tl)
  | D1 tl => String "1" (base_ten_dec tl)
  | D2 tl => String "2" (base_ten_dec tl)
  | D3 tl => String "3" (base_ten_dec tl)
  | D4 tl => String "4" (base_ten_dec tl)
  | D5 tl => String "5" (base_ten_dec tl)
  | D6 tl => String "6" (base_ten_dec tl)
  | D7 tl => String "7" (base_ten_dec tl)
  | D8 tl => String "8" (base_ten_dec tl)
  | D9 tl => String "9" (base_ten_dec tl)
  end.
Arguments base_ten_dec d%uint.

Definition base_ten n := base_ten_dec (Nat.to_uint n).
Arguments base_ten n/.

Example base_ten_512 : base_ten 512 = "512"%string.
Proof. reflexivity. Qed.

Example base_ten_0 : base_ten 0 = "0"%string.
Proof. reflexivity. Qed.

Lemma little_succ_never_nil d : Little.succ d <> Nil.
Proof. induction d; intros C; discriminate C. Qed.

(* NOTE: `Nil` is an edge case, but `Nat.to_uint _` can never be `Nil` *)
Example nat_never_nil n : Nat.to_uint n <> Nil.
Proof.
  induction n; intros C. { discriminate C. }
  rewrite Unsigned.to_uint_alt in *.
  apply DecimalFacts.rev_nil_inv in C.
  simpl in C. apply little_succ_never_nil in C. assumption.
Qed.

Definition parse_digit d :=
  (*
  (match d with
  | "0" => Some D0
  | "1" => Some D1
  | "2" => Some D2
  | "3" => Some D3
  | "4" => Some D4
  | "5" => Some D5
  | "6" => Some D6
  | "7" => Some D7
  | "8" => Some D8
  | "9" => Some D9
  | _ => None
  end)%char.
  *)
  (
  if d =? "0" then Some D0 else
  if d =? "1" then Some D1 else
  if d =? "2" then Some D2 else
  if d =? "3" then Some D3 else
  if d =? "4" then Some D4 else
  if d =? "5" then Some D5 else
  if d =? "6" then Some D6 else
  if d =? "7" then Some D7 else
  if d =? "8" then Some D8 else
  if d =? "9" then Some D9 else
  None
  )%char.
Arguments parse_digit d%char.

(* NOTE: This returns 0 on the empty string! *)
Fixpoint from_base_ten_dec s :=
  match s with
  | EmptyString => Some Nil
  | String c tl =>
      match parse_digit c with
      | None => None
      | Some f =>
          match from_base_ten_dec tl with
          | None => None
          | Some rec => Some (f rec)
          end
      end
  end.
Arguments from_base_ten_dec s%string.

Definition from_base_ten s :=
  match s with
  | EmptyString => None (* Preventing the odd behavior `NOTE`d above *)
  | _ => 
      match from_base_ten_dec s with
      | None => None
      | Some d => Some (Nat.of_uint d)
      end
  end.
Arguments from_base_ten s%string/.

Example from_base_ten_512 : from_base_ten "512" = Some 512.
Proof. reflexivity. Qed.

Example from_base_ten_empty : from_base_ten "" = None.
Proof. reflexivity. Qed.

Example from_base_ten_leading_zeros : from_base_ten "00042" = Some 42.
Proof. reflexivity. Qed.

Lemma parse_digit_options c f :
  parse_digit c = Some f ->
  c = "0"%char \/
  c = "1"%char \/
  c = "2"%char \/
  c = "3"%char \/
  c = "4"%char \/
  c = "5"%char \/
  c = "6"%char \/
  c = "7"%char \/
  c = "8"%char \/
  c = "9"%char.
Proof.
  intros. unfold parse_digit in H.
  destruct (reflect_ascii_eq c "0"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "1"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "2"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "3"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "4"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "5"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "6"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "7"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "8"); subst; [repeat (try (left; reflexivity); right) |].
  destruct (reflect_ascii_eq c "9").
  - invert H. repeat right. reflexivity.
  - discriminate H.
Qed.

Lemma from_base_ten_dec_pop c s f tl :
  parse_digit c = Some f ->
  from_base_ten_dec s = Some tl ->
  from_base_ten_dec (String c s) = Some (f tl).
Proof.
  intros. simpl in *. rewrite H; clear c H.
  generalize dependent tl. generalize dependent f.
  induction s; intros. { invert H0. reflexivity. }
  rewrite H0. reflexivity.
Qed.

Lemma base_ten_dec_empty_only_on_nil n : n = Nil <-> base_ten_dec n = ""%string.
Proof.
  split; intros. { subst. reflexivity. }
  generalize dependent H.
  induction n; intros; [reflexivity | | | | | | | | | |];
  inversion H.
Qed.

Lemma base_ten_never_empty n : base_ten n <> ""%string.
Proof.
  unfold base_ten. intros C.
  apply base_ten_dec_empty_only_on_nil in C.
  apply nat_never_nil in C. assumption.
Qed.

Theorem base_ten_dec_correct n : from_base_ten_dec (base_ten_dec n) = Some n.
Proof.
  induction n; [reflexivity | | | | | | | | | |];
  simpl; rewrite IHn; reflexivity.
Qed.

Theorem base_ten_correct n : from_base_ten (base_ten n) = Some n.
Proof.
  unfold from_base_ten. unfold base_ten.
  rewrite base_ten_dec_correct. rewrite Unsigned.of_to.
  destruct (base_ten_dec (Nat.to_uint n)) eqn:Ebt.
  { apply base_ten_never_empty in Ebt. destruct Ebt. }
  reflexivity.
Qed.

Inductive PrintLiteral : literal -> string -> Prop :=
  | PrintLitNat n s: from_base_ten s = Some n -> PrintLiteral (LitNat n) s
  | PrintLitTrue : PrintLiteral (LitBool true) "true"
  | PrintLitFalse : PrintLiteral (LitBool false) "false".

Example print_literal_leading_zeros : PrintLiteral (LitNat 42) "00042".
Proof. constructor. reflexivity. Qed.

Inductive Print : value -> string -> Prop :=
  | PrintEmpty : Print ValEmpty ""
  | PrintLit lit s : PrintLiteral lit s -> Print (ValLit lit) s
  | PrintVar ident : Print (ValVar ident) ident
  | PrintUnit s ps :
      ps = String "(" (rev_str (String ")" (rev_str s))) ->
      Print ValEmpty s ->
      Print (ValTuple nil) ps
  | PrintSpacePre w v s: Whitespace w -> Print v s -> Print v (String w s)
  | PrintSpacePost w v s s': str_split_last s = Some (s', w) -> Whitespace w -> Print v s' -> Print v s.

Ltac leading_space := apply PrintSpacePre; [constructor |].

Example leading_whitespace_zero : Print (ValLit (LitNat 0)) " 0".
Proof. leading_space. repeat econstructor. Qed.

Example leading_zeros : Print (ValLit (LitNat 0)) "00000".
Proof. repeat econstructor. Qed.

Example print_512 : Print (ValLit (LitNat 512)) "512".
Proof. repeat econstructor. Qed.

Ltac trailing_space := eapply PrintSpacePost; [reflexivity | constructor |].

Example trailing_whitespace_zero : Print (ValLit (LitNat 0)) "0 ".
Proof. trailing_space. repeat econstructor. Qed.

Ltac trim_whitespace := repeat leading_space; repeat trailing_space.

Example trim_whitespace_absurd : Print (ValLit (LitNat 0)) "            0            ".
Proof. trim_whitespace. apply PrintLit. constructor. repeat econstructor. Qed.

Ltac print_unit := eapply PrintUnit; [f_equal; apply rev_str_swap; simpl; f_equal; apply rev_str_swap; reflexivity |].

Example unit_with_whitespace_inside : Print (ValTuple nil) "( )".
Proof. print_unit. repeat constructor. Qed.

Inductive WellFormatted : string -> Prop :=
  (* TODO *)
  | WFTodo s : WellFormatted s.

Lemma all_literals_printable :
  forall lit, exists s, PrintLiteral lit s /\ WellFormatted s.
Proof.
  induction lit.
  - (* Natural numbers *) exists (base_ten n). split. { constructor. apply base_ten_correct. } constructor.
  - (* Booleans *) destruct b; eexists; split; constructor.
Qed.

(* Every possible value has a well-formatted source-code representation. *)
Theorem all_values_printable :
  forall (v: value), exists s, Print v s /\ WellFormatted s.
Proof.
  induction v.
  - (* Empty, i.e. whitespace inside a unit tuple *) exists ""%string. split; constructor.
  - (* Literals *)
    destruct (all_literals_printable lit) as [s [H HWF]].
    exists s. split; [constructor |]; assumption.
  - (* Variables *) exists ident. split; constructor.
  - (* Tuples: unit and singleton are special cases, then induction *)
    destruct elements; [| destruct elements; [| induction elements]].
    + exists "()"%string. split. { print_unit. constructor. } constructor.
    + (* FIXME: Why is there not an IH about the printability of `v` here? *)
Qed.
