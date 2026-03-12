From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax loc val.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.

Definition unwrap_val {A} (f : val -> option A) (s : string) (v : val) : iv_monad A :=
  match f v with
  | Some x => pure x
  | None => throw (Type_error s)
  end.

Definition unwrap_vunit : val -> iv_monad unit :=
  unwrap_val val_to_unit "unwrap_vunit".

Definition unwrap_vint : val -> iv_monad Z :=
  unwrap_val val_to_int "unwrap_vint".

Definition unwrap_vfloat : val -> iv_monad Qc :=
  unwrap_val val_to_float "unwrap_vfloat".

Definition unwrap_vbool : val -> iv_monad bool :=
  unwrap_val val_to_bool "unwrap_vbool".

Definition unwrap_vchar : val -> iv_monad ascii :=
  unwrap_val val_to_char "unwrap_vchar".

Definition unwrap_vstring : val -> iv_monad string :=
  unwrap_val val_to_string "unwrap_vstring".

Definition unwrap_vref : val -> iv_monad loc :=
  unwrap_val val_to_ref "unwrap_vref".

Definition unwrap_vprod : val -> iv_monad (val * val) :=
  unwrap_val val_to_prod "unwrap_vprod".

Definition unwrap_vsum : val -> iv_monad (val + val) :=
  unwrap_val val_to_sum "unwrap_vsum".

Definition unwrap_vvariant : val -> iv_monad variant :=
  unwrap_val val_to_variant "unwrap_vvariant".

Definition unwrap_vtuple : val -> iv_monad tuple :=
  unwrap_val val_to_tuple "unwrap_vtuple".

Definition unwrap_vrecord : val -> iv_monad record :=
  unwrap_val val_to_record "unwrap_vrecord".

Definition unwrap_varray : val -> iv_monad array :=
  unwrap_val val_to_array "unwrap_varray".

Definition unwrap_vclosure : val -> iv_monad closure :=
  unwrap_val val_to_closure "unwrap_vclosure".
