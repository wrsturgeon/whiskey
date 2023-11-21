From Coq Require Import
  Strings.String.
From Whiskey Require Import
  Data.Literal.

Inductive value :=
  | ValEmpty (* nothing, i.e. what's inside `{ }` and `( )` *)
  | ValLit (lit : literal)
  | ValVar (ident : string)
  | ValTuple (elements : list value)
  | ValRecord (lookup : string -> value)
  | ValLambda (argument : pattern)

with pattern :=
  | PatWild
  | PatBind (bound : pattern) (identifier : string)
  | PatLit (lit : literal)
  | PatVar (ident : string)
  | PatTuple (elements : list value)
  | PatRecord (lookup : string -> value).
(* TODO: lambda patterns? *)
