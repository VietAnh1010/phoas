From Stdlib Require Import Ascii Bool String Qcanon ZArith.
From shift_reset.lib Require Import compare float.
From shift_reset.core Require Import syntax ident loc val.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.
Import ExceptNotations.

Local Open Scope Z_scope.
Local Open Scope Qc_scope.
Local Open Scope except_scope.
Local Open Scope string_scope.
Local Open Scope lazy_bool_scope.

Definition dispatch_neg (v : val) : iv_monad val :=
  match v with
  | VInt z => pure (VInt (-z))
  | VFloat q => pure (VFloat (-q))
  | _ => throw (Type_error "int | float" v)
  end.

Definition dispatch_not (v : val) : iv_monad val :=
  match v with
  | VTrue => pure VFalse
  | VFalse => pure VTrue
  | _ => throw (Type_error "bool" v)
  end.

Definition dispatch_lnot (v : val) : iv_monad val :=
  match v with
  | VInt z => pure (VInt (Z.lnot z))
  | _ => throw (Type_error "int" v)
  end.

Definition dispatch_length (v : val) : iv_monad val :=
  match v with
  | VString s => pure (VInt (Z.of_nat (String.length s)))
  | VArray _ z => pure (VInt z)
  | _ => throw (Type_error "array | string" v)
  end.

Definition dispatch_un_op (op : un_op) : val -> iv_monad val :=
  match op with
  | UnOpNeg => dispatch_neg
  | UnOpNot => dispatch_not
  | UnOpLnot => dispatch_lnot
  | UnOpLength => dispatch_length
  end.

Definition dispatch_add (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 + z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 + q2))
  | _, _ => throw (Type_error "int * int | float * float" (VPair v1 v2))
  end.

Definition dispatch_sub (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 - z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 - q2))
  | _, _ => throw (Type_error "int * int | float * float" (VPair v1 v2))
  end.

Definition dispatch_mul (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 * z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 * q2))
  | _, _ => throw (Type_error "int * int | float * float" (VPair v1 v2))
  end.

Definition dispatch_div (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 =? 0)%Z then throw Division_by_zero else pure (VInt (z1 / z2))
  | VFloat q1, VFloat q2 => if (q2 =? 0)%Qc then throw Division_by_zero else pure (VFloat (q1 / q2))
  | _, _ => throw (Type_error "int * int | float * float" (VPair v1 v2))
  end.

Definition dispatch_mod (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 =? 0)%Z then throw Division_by_zero else pure (VInt (z1 mod z2))
  | _, _ => throw (Type_error "int * int" (VPair v1 v2))
  end.

Definition dispatch_pow (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 <? 0)%Z then throw Negative_exponent else pure (VInt (z1 ^ z2))
  | VFloat q, VInt z => if (z <? 0)%Z then throw Negative_exponent else pure (VFloat (q ^ Z.to_nat z))
  | _, _ => throw (Type_error "int * int | float * int" (VPair v1 v2))
  end.

Definition dispatch_land (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (Z.land z1 z2))
  | _, _ => throw (Type_error "int * int" (VPair v1 v2))
  end.

Definition dispatch_lor (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (Z.lor z1 z2))
  | _, _ => throw (Type_error "int * int" (VPair v1 v2))
  end.

Definition dispatch_lxor (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (Z.lxor z1 z2))
  | _, _ => throw (Type_error "int * int" (VPair v1 v2))
  end.

Definition dispatch_shiftl (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 <? 0)%Z then throw Negative_arithmetic_shift else pure (VInt (Z.shiftl z1 z2))
  | _, _ => throw (Type_error "int * int" (VPair v1 v2))
  end.

Definition dispatch_shiftr (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 <? 0)%Z then throw Negative_arithmetic_shift else pure (VInt (Z.shiftr z1 z2))
  | _, _ => throw (Type_error "int * int" (VPair v1 v2))
  end.

Fixpoint append_list (v1 v2 : val) : iv_monad val :=
  match v1 with
  | VNil => pure v2
  | VCons v11 v12 => VCons v11 <$> append_list v12 v2
  | _ => throw (Type_error "list" v1)
  end.

Definition dispatch_append (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VString s1, VString s2 => pure (VString (s1 ++ s2))
  | (VNil | VCons _ _), _ => append_list v1 v2
  | _, _ => throw (Type_error "string * string | list * list" (VPair v1 v2))
  end.

Fixpoint compare_val (v1 v2 : val) : iv_monad comparison :=
  match v1, v2 with
  | VTt, VTt => pure Eq
  | VInt z1, VInt z2 => pure (z1 ?= z2)%Z
  | VFloat q1, VFloat q2 => pure (q1 ?= q2)%Qc
  | VTrue, VTrue => pure Eq
  | VFalse, VFalse => pure Eq
  | VTrue, VFalse => pure Gt
  | VFalse, VTrue => pure Lt
  | VChar a1, VChar a2 => pure (a1 ?= a2)%char
  | VString s1, VString s2 => pure (s1 ?= s2)%string
  | VPair v11 v12, VPair v21 v22 =>
      let* c := compare_val v11 v21 in
      match c with
      | Eq => compare_val v12 v22
      | _ => pure c
      end
  | VTuple t1, VTuple t2 => compare_vals t1 t2
  | VInl v1', VInl v2' => compare_val v1' v2'
  | VInr v1', VInr v2' => compare_val v1' v2'
  | VInl _, VInr _ => pure Lt
  | VInr _, VInl _ => pure Gt
  | VNil, VNil => pure Eq
  | VCons v11 v12, VCons v21 v22 =>
      let* c := compare_val v11 v21 in
      match c with
      | Eq => compare_val v12 v22
      | _ => pure c
      end
  | VNil, VCons _ _ => pure Lt
  | VCons _ _, VNil => pure Gt
  | _, _ => throw (Type_error "'a ord => 'a * 'a" (VPair v1 v2))
  end
with compare_vals (t1 t2 : vals) : iv_monad comparison :=
  match t1, t2 with
  | VsNil, VsNil => pure Eq
  | VsCons v1 t1', VsCons v2 t2' =>
      let* c := compare_val v1 v2 in
      match c with
      | Eq => compare_vals t1' t2'
      | _ => pure c
      end
  | _, _ => throw (Type_error "'a ord => 'a * 'a" (VPair (VTuple t1) (VTuple t2)))
  end.

Fixpoint equal_val (v1 v2 : val) : iv_monad bool :=
  match v1, v2 with
  | VTt, VTt => pure true
  | VInt z1, VInt z2 => pure (z1 =? z2)%Z
  | VFloat q1, VFloat q2 => pure (q1 =? q2)%Qc
  | VTrue, VTrue => pure true
  | VFalse, VFalse => pure true
  | VTrue, VFalse => pure false
  | VFalse, VTrue => pure false
  | VChar a1, VChar a2 => pure (a1 =? a2)%char
  | VString s1, VString s2 => pure (s1 =? s2)%string
  | VPair v11 v12, VPair v21 v22 =>
      let* b := equal_val v11 v21 in
      if b then equal_val v12 v22 else pure false
  | VTuple t1, VTuple t2 => equal_vals t1 t2
  | VRecord r1, VRecord r2 => equal_ident_val_assocs r1 r2
  | VInl v1', VInl v2' => equal_val v1' v2'
  | VInr v1', VInr v2' => equal_val v1' v2'
  | VInl _, VInr _ => pure false
  | VInr _, VInl _ => pure false
  | VNil, VNil => pure true
  | VCons v11 v12, VCons v21 v22 =>
      let* b := equal_val v11 v21 in
      if b then equal_val v12 v22 else pure false
  | VNil, VCons _ _ => pure false
  | VCons _ _, VNil => pure false
  | VVariant v1', VVariant v2' => equal_variant v1' v2'
  | VRef l1, VRef l2 => pure (loc_eqb l1 l2)
  | VArray l1 z1, VArray l2 z2 => pure (loc_eqb l1 l2 &&& (z1 =? z2)%Z)
  | _, _ => throw (Type_error "'a eq => 'a * 'a" (VPair v1 v2))
  end
with equal_vals (t1 t2 : vals) : iv_monad bool :=
  match t1, t2 with
  | VsNil, VsNil => pure true
  | VsCons v1 t1', VsCons v2 t2' =>
      let* b := equal_val v1 v2 in
      if b then equal_vals t1' t2' else pure false
  | _, _ => pure false
  end
with equal_ident_val_assocs (r1 r2 : ident_val_assocs) : iv_monad bool :=
  match r1, r2 with
  | IVAsNil, IVAsNil => pure true
  | IVAsCons l1 v1 r1', IVAsCons l2 v2 r2' =>
      if ident_eqb l1 l2 then
        let* b := equal_val v1 v2 in
        if b then equal_ident_val_assocs r1' r2' else pure false
      else pure false
  | _, _ => pure false
  end
with equal_variant (v1 v2 : variant) : iv_monad bool :=
  match v1, v2 with
  | VariantNone l1, VariantNone l2 => pure (ident_eqb l1 l2)
  | VariantSome l1 v1', VariantSome l2 v2' => if ident_eqb l1 l2 then equal_val v1' v2' else pure false
  | _, _ => pure false
  end.

Definition dispatch_lt (v1 v2 : val) : iv_monad val :=
  let+ c := compare_val v1 v2 in VBool (compare_ltb c).

Definition dispatch_le (v1 v2 : val) : iv_monad val :=
  let+ c := compare_val v1 v2 in VBool (compare_leb c).

Definition dispatch_gt (v1 v2 : val) : iv_monad val :=
  let+ c := compare_val v1 v2 in VBool (compare_gtb c).

Definition dispatch_ge (v1 v2 : val) : iv_monad val :=
  let+ c := compare_val v1 v2 in VBool (compare_geb c).

Definition dispatch_eq (v1 v2 : val) : iv_monad val :=
  VBool <$> equal_val v1 v2.

Definition dispatch_neq (v1 v2 : val) : iv_monad val :=
  let+ b := equal_val v1 v2 in VBool (negb b).

Definition dispatch_bin_op (op : bin_op) : val -> val -> iv_monad val :=
  match op with
  | BinOpAdd => dispatch_add
  | BinOpSub => dispatch_sub
  | BinOpMul => dispatch_mul
  | BinOpDiv => dispatch_div
  | BinOpMod => dispatch_mod
  | BinOpPow => dispatch_pow
  | BinOpLand => dispatch_land
  | BinOpLor => dispatch_lor
  | BinOpLxor => dispatch_lxor
  | BinOpShiftl => dispatch_shiftl
  | BinOpShiftr => dispatch_shiftr
  | BinOpAppend => dispatch_append
  | BinOpLt => dispatch_lt
  | BinOpLe => dispatch_le
  | BinOpGt => dispatch_gt
  | BinOpGe => dispatch_ge
  | BinOpEq => dispatch_eq
  | BinOpNeq => dispatch_neq
  end.
