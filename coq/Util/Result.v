(* Result types: either a valid result or an error. *)
Inductive Result ok err :=
  | Ok : ok -> Result ok err
  | Err : err -> Result ok err.
