From Stdlib Require Import String.
From shift_reset.core Require Import syntax ident.

Definition Failure (s : string) : val :=
  VVariant (Ident "Failure") (VString s).

Definition Type_error (s : string) (v : val) : val :=
  VVariant (Ident "Type_error") (VPair (VString s) v).

Definition Name_error (s : string) : val :=
  VVariant (Ident "Name_error") (VString s).

Definition Memory_error : val -> val :=
  VVariant (Ident "Memory_error").

Definition Match_failure : val -> val :=
  VVariant (Ident "Match_failure").

Definition Invalid_argument (s : string) (v : val) : val :=
  VVariant (Ident "Invalid_argument") (VPair (VString s) v).

Definition Unhandled_effect : val -> val :=
  VVariant (Ident "Unhandled_effect").

Definition Undelimited_shift : val :=
  VEnum (Ident "Undelimited_shift").

Definition Undelimited_control : val :=
  VEnum (Ident "Undelimited_control").

Definition Out_of_fuel : val :=
  VEnum (Ident "Out_of_fuel").
