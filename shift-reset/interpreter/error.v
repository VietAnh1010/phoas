From Stdlib Require Import String.
From shift_reset.core Require Import syntax ident val.

Definition Failure (s : string) : exn :=
  Exn (Ident "Failure") (VString s).

Definition Type_error (s : string) : exn :=
  Exn (Ident "Type_error") (VString s).

Definition Name_error (s : string) : exn :=
  Exn (Ident "Name_error") (VString s).

Definition Memory_error (s : string) : exn :=
  Exn (Ident "Memory_error") (VString s).

Definition Assert_failure (s : string) : exn :=
  Exn (Ident "Assert_failure") (VString s).

Definition Match_failure (s : string) : exn :=
  Exn (Ident "Match_failure") (VString s).

Definition Invalid_argument (s : string) : exn :=
  Exn (Ident "Invalid_argument") (VString s).

Definition Unhandled_exception (x : exn) : exn :=
  Exn (Ident "Unhandled_exception") (VExn' x).

Definition Unhandled_effect (f : eff) : exn :=
  Exn (Ident "Unhandled_effect") (VEff' f).

Definition Division_by_zero : exn :=
  Exn (Ident "Division_by_zero") VTt.

Definition Negative_exponent : exn :=
  Exn (Ident "Negative_exponent") VTt.

Definition Negative_arithmetic_shift : exn :=
  Exn (Ident "Negative_arithmetic_shift") VTt.

Definition Undelimited_shift : exn :=
  Exn (Ident "Undelimited_shift") VTt.

Definition Undelimited_control : exn :=
  Exn (Ident "Undelimited_control") VTt.

Definition Undelimited_shift0 : exn :=
  Exn (Ident "Undelimited_shift0") VTt.

Definition Undelimited_control0 : exn :=
  Exn (Ident "Undelimited_control0") VTt.

Definition Out_of_fuel : exn :=
  Exn (Ident "Out_of_fuel") VTt.
