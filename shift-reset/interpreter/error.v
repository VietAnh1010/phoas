From Stdlib Require Import String.
From shift_reset.core Require Import syntax tag val.

Definition Failure (s : string) : exn :=
  Exn (Tag "Failure") (VString s).

Definition Type_error (s : string) : exn :=
  Exn (Tag "Type_error") (VString s).

Definition Name_error (s : string) : exn :=
  Exn (Tag "Name_error") (VString s).

Definition Memory_error (s : string) : exn :=
  Exn (Tag "Memory_error") (VString s).

Definition Assert_failure (s : string) : exn :=
  Exn (Tag "Assert_failure") (VString s).

Definition Match_failure (s : string) : exn :=
  Exn (Tag "Match_failure") (VString s).

Definition Invalid_argument (s : string) : exn :=
  Exn (Tag "Invalid_argument") (VString s).

Definition Unhandled_exception (x : exn) : exn :=
  Exn (Tag "Unhandled_exception") (VExn' x).

Definition Unhandled_effect (f : eff) : exn :=
  Exn (Tag "Unhandled_effect") (VEff' f).

Definition Division_by_zero : exn :=
  Exn (Tag "Division_by_zero") VTt.

Definition Undelimited_shift : exn :=
  Exn (Tag "Undelimited_shift") VTt.

Definition Undelimited_control : exn :=
  Exn (Tag "Undelimited_control") VTt.

Definition Out_of_fuel : exn :=
  Exn (Tag "Out_of_fuel") VTt.
