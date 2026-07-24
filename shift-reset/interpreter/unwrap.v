From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax loc val.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.

Definition unwrap_val {A} (f : val -> option A) (s : string) (v : val) : iv_monad A :=
  match f v with
  | Some x => pure x
  | None => throw (Type_error s v)
  end.

Definition unwrap_vunit : val -> iv_monad unit :=
  unwrap_val val_to_unit "unit".

Definition unwrap_vint : val -> iv_monad Z :=
  unwrap_val val_to_int "int".

Definition unwrap_vfloat : val -> iv_monad Qc :=
  unwrap_val val_to_float "float".

Definition unwrap_vbool : val -> iv_monad bool :=
  unwrap_val val_to_bool "bool".

Definition unwrap_vchar : val -> iv_monad ascii :=
  unwrap_val val_to_char "char".

Definition unwrap_vstring : val -> iv_monad string :=
  unwrap_val val_to_string "string".

Definition unwrap_vref : val -> iv_monad loc :=
  unwrap_val val_to_ref "ref".

Definition unwrap_vprod : val -> iv_monad (val * val) :=
  unwrap_val val_to_prod "prod".

Definition unwrap_vsum : val -> iv_monad (val + val) :=
  unwrap_val val_to_sum "sum".

Definition unwrap_vvariant : val -> iv_monad variant :=
  unwrap_val val_to_variant "variant".

Definition unwrap_vtuple : val -> iv_monad tuple :=
  unwrap_val val_to_tuple "tuple".

Definition unwrap_vrecord : val -> iv_monad record :=
  unwrap_val val_to_record "record".

Definition unwrap_varray : val -> iv_monad array :=
  unwrap_val val_to_array "array".

Definition unwrap_vclosure : val -> iv_monad closure :=
  unwrap_val val_to_closure "closure".
