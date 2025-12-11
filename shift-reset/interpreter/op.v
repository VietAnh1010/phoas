From Stdlib Require Import Ascii Bool String Qcanon ZArith.
From shift_reset.lib Require Import compare float.
From shift_reset.core Require Import syntax loc tag val.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import ierror unwrap.
Import ExceptNotations.

Local Open Scope Z_scope.
Local Open Scope Qc_scope.
Local Open Scope except_scope.
Local Open Scope string_scope.
Local Open Scope lazy_bool_scope.

Definition dispatch_pos (v : val) : except exn val :=
  match v with
  | VInt _ => pure v
  | VFloat _ => pure v
  | _ => throw (Type_error "dispatch_pos")
  end.

Definition dispatch_neg (v : val) : except exn val :=
  match v with
  | VInt z => pure (VInt (-z))
  | VFloat q => pure (VFloat (-q))
  | _ => throw (Type_error "dispatch_neg")
  end.

Definition dispatch_not (v : val) : except exn val :=
  match v with
  | VTrue => pure VFalse
  | VFalse => pure VTrue
  | _ => throw (Type_error "dispatch_not")
  end.

Definition dispatch_op1 (op : op1) : val -> except exn val :=
  match op with
  | Op1Pos => dispatch_pos
  | Op1Neg => dispatch_neg
  | Op1Not => dispatch_not
  end.

Definition dispatch_add (v1 v2 : val) : except exn val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 + z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 + q2))
  | _, _ => throw (Type_error "dispatch_add")
  end.

Definition dispatch_sub (v1 v2 : val) : except exn val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 - z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 - q2))
  | _, _ => throw (Type_error "dispatch_sub")
  end.

Definition dispatch_mul (v1 v2 : val) : except exn val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 * z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 * q2))
  | _, _ => throw (Type_error "dispatch_mul")
  end.

Definition dispatch_div (v1 v2 : val) : except exn val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 =? 0)%Z then throw Division_by_zero else pure (VInt (z1 / z2))
  | VFloat q1, VFloat q2 => if (q2 =? 0)%Qc then throw Division_by_zero else pure (VFloat (q1 / q2))
  | _, _ => throw (Type_error "dispatch_div")
  end.

Definition dispatch_mod (v1 v2 : val) : except exn val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 =? 0)%Z then throw Division_by_zero else pure (VInt (z1 mod z2))
  | _, _ => throw (Type_error "dispatch_mod")
  end.

Definition dispatch_app (v1 v2 : val) : except exn val :=
  match v1, v2 with
  | VString s1, VString s2 => pure (VString (s1 ++ s2))
  | _, _ => throw (Type_error "dispatch_app")
  end.

Fixpoint compare_val (v1 v2 : val) : except exn comparison :=
  match v1, v2 with
  | VTt, VTt => pure Eq
  | VInt z1, VInt z2 => pure (z1 ?= z2)%Z
  | VFloat q1, VFloat q2 => pure (q1 ?= q2)%Qc
  | VTrue, VTrue => pure Eq
  | VTrue, VFalse => pure Gt
  | VFalse, VTrue => pure Lt
  | VFalse, VFalse => pure Eq
  | VChar a1, VChar a2 => pure (a1 ?= a2)%char
  | VString s1, VString s2 => pure (s1 ?= s2)%string
  | VPair v11 v12, VPair v21 v22 =>
      let* c := compare_val v11 v21 in
      match c with
      | Eq => compare_val v12 v22
      | _ => pure c
      end
  | VInl v1', VInl v2' => compare_val v1' v2'
  | VInr v1', VInr v2' => compare_val v1' v2'
  | VInl _, VInr _ => pure Lt
  | VInr _, VInl _ => pure Gt
  | _, _ => throw (Type_error "compare_val")
  end.

Fixpoint equal_val (v1 v2 : val) : except exn bool :=
  match v1, v2 with
  | VTt, VTt => pure true
  | VInt z1, VInt z2 => pure (z1 =? z2)%Z
  | VFloat q1, VFloat q2 => pure (q1 =? q2)%Qc
  | VTrue, VTrue => pure true
  | VTrue, VFalse => pure false
  | VFalse, VTrue => pure false
  | VFalse, VFalse => pure true
  | VChar a1, VChar a2 => pure (a1 =? a2)%char
  | VString s1, VString s2 => pure (s1 =? s2)%string
  | VPair v11 v12, VPair v21 v22 =>
      let* b := equal_val v11 v21 in
      if b then equal_val v12 v22 else pure false
  | VTuple t1, VTuple t2 => equal_tuple t1 t2
  | VRecord r1, VRecord r2 => equal_record r1 r2
  | VInl v1', VInl v2' => equal_val v1' v2'
  | VInr v1', VInr v2' => equal_val v1' v2'
  | VInl _, VInr _ => pure false
  | VInr _, VInl _ => pure false
  | VVariant tag1 v1', VVariant tag2 v2' => if tag_eqb tag1 tag2 then equal_val v1' v2' else pure false
  | VRef l1, VRef l2 => pure (loc_eqb l1 l2)
  | VExn tag1 v1', VExn tag2 v2' => if tag_eqb tag1 tag2 then equal_val v1' v2' else pure false
  | VEff tag1 v1', VEff tag2 v2' => if tag_eqb tag1 tag2 then equal_val v1' v2' else pure false
  | VArray l1 z1, VArray l2 z2 => pure (loc_eqb l1 l2 &&& (z1 =? z2)%Z)
  | _, _ => throw (Type_error "equal_val")
  end
with equal_tuple (t1 t2 : tuple) : except exn bool :=
  match t1, t2 with
  | TupleNil, TupleNil => pure true
  | TupleCons v1 t1', TupleCons v2 t2' =>
      let* b := equal_val v1 v2 in
      if b then equal_tuple t1' t2' else pure false
  | _, _ => pure false
  end
with equal_record (r1 r2 : record) : except exn bool :=
  match r1, r2 with
  | RecordNil, RecordNil => pure true
  | RecordCons tag1 v1 r1', RecordCons tag2 v2 r2' =>
      if tag_eqb tag1 tag2 then
        let* b := equal_val v1 v2 in
        if b then equal_record r1' r2' else pure false
      else pure false
  | _, _ => pure false
  end.

Definition dispatch_lt (v1 v2 : val) : except exn val :=
  let+ c := compare_val v1 v2 in VBool (compare_ltb c).

Definition dispatch_le (v1 v2 : val) : except exn val :=
  let+ c := compare_val v1 v2 in VBool (compare_leb c).

Definition dispatch_gt (v1 v2 : val) : except exn val :=
  let+ c := compare_val v1 v2 in VBool (compare_gtb c).

Definition dispatch_ge (v1 v2 : val) : except exn val :=
  let+ c := compare_val v1 v2 in VBool (compare_geb c).

Definition dispatch_eq (v1 v2 : val) : except exn val :=
  VBool <$> equal_val v1 v2.

Definition dispatch_neq (v1 v2 : val) : except exn val :=
  let+ b := equal_val v1 v2 in VBool (negb b).

Definition dispatch_op2 (op : op2) : val -> val -> except exn val :=
  match op with
  | Op2Add => dispatch_add
  | Op2Sub => dispatch_sub
  | Op2Mul => dispatch_mul
  | Op2Div => dispatch_div
  | Op2Mod => dispatch_mod
  | Op2App => dispatch_app
  | Op2Lt => dispatch_lt
  | Op2Le => dispatch_le
  | Op2Gt => dispatch_gt
  | Op2Ge => dispatch_ge
  | Op2Eq => dispatch_eq
  | Op2Neq => dispatch_neq
  end.
