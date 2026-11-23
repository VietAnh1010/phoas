From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax loc val.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.

Definition unwrap_val {A} (f : val -> option A) (s : string) (v : val) : iv_monad A :=
  match f v with
  | None => throw (Type_error s v)
  | Some x => pure x
  end.

Definition unwrap_unit : val -> iv_monad unit :=
  unwrap_val val_to_unit "unit".

Definition unwrap_int : val -> iv_monad Z :=
  unwrap_val val_to_int "int".

Definition unwrap_float : val -> iv_monad Qc :=
  unwrap_val val_to_float "float".

Definition unwrap_bool : val -> iv_monad bool :=
  unwrap_val val_to_bool "bool".

Definition unwrap_char : val -> iv_monad ascii :=
  unwrap_val val_to_char "char".

Definition unwrap_string : val -> iv_monad string :=
  unwrap_val val_to_string "string".

Definition unwrap_ref : val -> iv_monad loc :=
  unwrap_val val_to_ref "ref".

Definition unwrap_prod : val -> iv_monad (val * val) :=
  unwrap_val val_to_prod "prod".

Definition unwrap_sum : val -> iv_monad (val + val) :=
  unwrap_val val_to_sum "sum".

Definition unwrap_variant : val -> iv_monad variant :=
  unwrap_val val_to_variant "variant".

Definition unwrap_enum : val -> iv_monad enum :=
  unwrap_val val_to_enum "enum".

Definition unwrap_list : val -> iv_monad (list val) :=
  unwrap_val val_to_list "list".

Definition unwrap_tuple : val -> iv_monad tuple :=
  unwrap_val val_to_tuple "tuple".

Definition unwrap_record : val -> iv_monad record :=
  unwrap_val val_to_record "record".

Definition unwrap_array : val -> iv_monad array :=
  unwrap_val val_to_array "array".

Definition unwrap_applicable : val -> iv_monad applicable :=
  unwrap_val val_to_applicable "applicable".
