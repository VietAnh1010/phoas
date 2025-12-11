From Stdlib Require Import String.
From shift_reset.core Require Import syntax tag.

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

Definition Unhandled_exception (s : string) : exn :=
  Exn (Tag "Unhandled_exception") (VString s).

Definition Unhandled_effect (s : string) : exn :=
  Exn (Tag "Unhandled_effect") (VString s).

Definition Division_by_zero : exn :=
  Exn (Tag "Division_by_zero") VTt.

Definition Undelimited_shift : exn :=
  Exn (Tag "Undelimited_shift") VTt.

Definition Undelimited_control : exn :=
  Exn (Tag "Undelimited_control") VTt.

Definition Out_of_fuel : exn :=
  Exn (Tag "Out_of_fuel") VTt.
