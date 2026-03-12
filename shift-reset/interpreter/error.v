From Stdlib Require Import String.
From shift_reset.core Require Import syntax ident.

Definition Failure (s : string) : val :=
  VVariant (Ident "Failure") (VString s).

Definition Type_error (s : string) : val :=
  VVariant (Ident "Type_error") (VString s).

Definition Name_error (s : string) : val :=
  VVariant (Ident "Name_error") (VString s).

Definition Memory_error (s : string) : val :=
  VVariant (Ident "Memory_error") (VString s).

Definition Assert_failure (s : string) : val :=
  VVariant (Ident "Assert_failure") (VString s).

Definition Match_failure (s : string) : val :=
  VVariant (Ident "Match_failure") (VString s).

Definition Invalid_argument (s : string) : val :=
  VVariant (Ident "Invalid_argument") (VString s).

Definition Unhandled_effect : val -> val :=
  VVariant (Ident "Unhandled_effect").

Definition Division_by_zero : val :=
  VVariant (Ident "Division_by_zero") VTt.

Definition Negative_exponent : val :=
  VVariant (Ident "Negative_exponent") VTt.

Definition Negative_arithmetic_shift : val :=
  VVariant (Ident "Negative_arithmetic_shift") VTt.

Definition Undelimited_shift : val :=
  VVariant (Ident "Undelimited_shift") VTt.

Definition Undelimited_control : val :=
  VVariant (Ident "Undelimited_control") VTt.

Definition Undelimited_shift0 : val :=
  VVariant (Ident "Undelimited_shift0") VTt.

Definition Undelimited_control0 : val :=
  VVariant (Ident "Undelimited_control0") VTt.

Definition Out_of_fuel : val :=
  VVariant (Ident "Out_of_fuel") VTt.
