From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.

Inductive literal :=
  | LitNat : nat -> literal
  | LitBool : bool -> literal.
  (*
  TODO: representation nightmare
  | LitChar : ascii -> literal
  | LitString : string -> literal.
  *)
