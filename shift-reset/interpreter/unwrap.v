From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax loc val.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error.

Definition unwrap_val {A} (f : val -> option A) (s : string) (v : val) : except exn A :=
  match f v with
  | Some x => pure x
  | None => throw (Type_error s)
  end.

Definition unwrap_vunit : val -> except exn unit :=
  unwrap_val val_to_unit "unwrap_vunit".

Definition unwrap_vint : val -> except exn Z :=
  unwrap_val val_to_int "unwrap_vint".

Definition unwrap_vfloat : val -> except exn Qc :=
  unwrap_val val_to_float "unwrap_vfloat".

Definition unwrap_vbool : val -> except exn bool :=
  unwrap_val val_to_bool "unwrap_vbool".

Definition unwrap_vchar : val -> except exn ascii :=
  unwrap_val val_to_char "unwrap_vchar".

Definition unwrap_vstring : val -> except exn string :=
  unwrap_val val_to_string "unwrap_vstring".

Definition unwrap_vref : val -> except exn loc :=
  unwrap_val val_to_ref "unwrap_vref".

Definition unwrap_vprod : val -> except exn (val * val) :=
  unwrap_val val_to_prod "unwrap_vprod".

Definition unwrap_vsum : val -> except exn (val + val) :=
  unwrap_val val_to_sum "unwrap_vsum".

Definition unwrap_vexn : val -> except exn exn :=
  unwrap_val val_to_exn "unwrap_vexn".

Definition unwrap_veff : val -> except exn eff :=
  unwrap_val val_to_eff "unwrap_veff".

Definition unwrap_vvariant : val -> except exn variant :=
  unwrap_val val_to_variant "unwrap_vvariant".

Definition unwrap_vtuple : val -> except exn tuple :=
  unwrap_val val_to_tuple "unwrap_vtuple".

Definition unwrap_vrecord : val -> except exn record :=
  unwrap_val val_to_record "unwrap_vrecord".

Definition unwrap_varray : val -> except exn array :=
  unwrap_val val_to_array "unwrap_varray".

Definition unwrap_vclosure : val -> except exn closure :=
  unwrap_val val_to_closure "unwrap_vclosure".
