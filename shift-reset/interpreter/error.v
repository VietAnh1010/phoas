From Stdlib Require Import String.
From shift_reset.core Require Import syntax ident.

Definition Failure (s : string) : val :=
  VVariant (VariantSome (Ident "Failure") (VString s)).

Definition Type_error (s : string) (v : val) : val :=
  VVariant (VariantSome (Ident "Type_error") (VRecord (IVAsCons (Ident "expected") (VString s) (IVAsCons (Ident "got") v IVAsNil)))).

Definition Name_error (s : string) : val :=
  VVariant (VariantSome (Ident "Name_error") (VString s)).

Definition Memory_error (s : string) : val :=
  VVariant (VariantSome (Ident "Memory_error") (VString s)).

Definition Match_failure (s : string) : val :=
  VVariant (VariantSome (Ident "Match_failure") (VString s)).

Definition Invalid_argument (s : string) : val :=
  VVariant (VariantSome (Ident "Invalid_argument") (VString s)).

Definition Unhandled_effect (v : val) : val :=
  VVariant (VariantSome (Ident "Unhandled_effect") v).

Definition Division_by_zero : val :=
  VVariant (VariantNone (Ident "Division_by_zero")).

Definition Negative_exponent : val :=
  VVariant (VariantNone (Ident "Negative_exponent")).

Definition Negative_arithmetic_shift : val :=
  VVariant (VariantNone (Ident "Negative_arithmetic_shift")).

Definition Undelimited_shift : val :=
  VVariant (VariantNone (Ident "Undelimited_shift")).

Definition Undelimited_control : val :=
  VVariant (VariantNone (Ident "Undelimited_control")).

Definition Out_of_fuel : val :=
  VVariant (VariantNone (Ident "Out_of_fuel")).
