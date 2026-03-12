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

Definition dispatch_pos (v : val) : iv_monad val :=
  match v with
  | VInt _ => pure v
  | VFloat _ => pure v
  | _ => throw (Type_error "dispatch_pos")
  end.

Definition dispatch_neg (v : val) : iv_monad val :=
  match v with
  | VInt z => pure (VInt (-z))
  | VFloat q => pure (VFloat (-q))
  | _ => throw (Type_error "dispatch_neg")
  end.

Definition dispatch_not (v : val) : iv_monad val :=
  match v with
  | VTrue => pure VFalse
  | VFalse => pure VTrue
  | _ => throw (Type_error "dispatch_not")
  end.

Definition dispatch_lnot (v : val) : iv_monad val :=
  match v with
  | VInt z => pure (VInt (Z.lnot z))
  | _ => throw (Type_error "dispatch_lnot")
  end.

Definition dispatch_op1 (op : op1) : val -> iv_monad val :=
  match op with
  | Op1Pos => dispatch_pos
  | Op1Neg => dispatch_neg
  | Op1Not => dispatch_not
  | Op1Lnot => dispatch_lnot
  end.

Definition dispatch_add (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 + z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 + q2))
  | _, _ => throw (Type_error "dispatch_add")
  end.

Definition dispatch_sub (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 - z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 - q2))
  | _, _ => throw (Type_error "dispatch_sub")
  end.

Definition dispatch_mul (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (z1 * z2))
  | VFloat q1, VFloat q2 => pure (VFloat (q1 * q2))
  | _, _ => throw (Type_error "dispatch_mul")
  end.

Definition dispatch_div (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 =? 0)%Z then throw Division_by_zero else pure (VInt (z1 / z2))
  | VFloat q1, VFloat q2 => if (q2 =? 0)%Qc then throw Division_by_zero else pure (VFloat (q1 / q2))
  | _, _ => throw (Type_error "dispatch_div")
  end.

Definition dispatch_mod (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 =? 0)%Z then throw Division_by_zero else pure (VInt (z1 mod z2))
  | _, _ => throw (Type_error "dispatch_mod")
  end.

Definition dispatch_pow (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 <? 0)%Z then throw Negative_exponent else pure (VInt (z1 ^ z2))
  | VFloat q, VInt z => if (z <? 0)%Z then throw Negative_exponent else pure (VFloat (q ^ Z.to_nat z))
  | _, _ => throw (Type_error "dispatch_pow")
  end.

Definition dispatch_land (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (Z.land z1 z2))
  | _, _ => throw (Type_error "dispatch_land")
  end.

Definition dispatch_lor (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (Z.lor z1 z2))
  | _, _ => throw (Type_error "dispatch_lor")
  end.

Definition dispatch_lxor (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => pure (VInt (Z.lxor z1 z2))
  | _, _ => throw (Type_error "dispatch_lxor")
  end.

Definition dispatch_shl (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 <? 0)%Z then throw Negative_arithmetic_shift else pure (VInt (Z.shiftl z1 z2))
  | _, _ => throw (Type_error "dispatch_shl")
  end.

Definition dispatch_shr (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VInt z1, VInt z2 => if (z2 <? 0)%Z then throw Negative_arithmetic_shift else pure (VInt (Z.shiftr z1 z2))
  | _, _ => throw (Type_error "dispatch_shr")
  end.

Definition dispatch_app (v1 v2 : val) : iv_monad val :=
  match v1, v2 with
  | VString s1, VString s2 => pure (VString (s1 ++ s2))
  | _, _ => throw (Type_error "dispatch_app")
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
  | VInl v1', VInl v2' => compare_val v1' v2'
  | VInr v1', VInr v2' => compare_val v1' v2'
  | VInl _, VInr _ => pure Lt
  | VInr _, VInl _ => pure Gt
  | _, _ => throw (Type_error "compare_val")
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
  | VTuple t1, VTuple t2 => equal_tuple t1 t2
  | VRecord r1, VRecord r2 => equal_record r1 r2
  | VInl v1', VInl v2' => equal_val v1' v2'
  | VInr v1', VInr v2' => equal_val v1' v2'
  | VInl _, VInr _ => pure false
  | VInr _, VInl _ => pure false
  | VVariant l1 v1', VVariant l2 v2' => if ident_eqb l1 l2 then equal_val v1' v2' else pure false
  | VRef l1, VRef l2 => pure (loc_eqb l1 l2)
  | VArray l1 z1, VArray l2 z2 => pure (loc_eqb l1 l2 &&& (z1 =? z2)%Z)
  | _, _ => throw (Type_error "equal_val")
  end
with equal_tuple (t1 t2 : tuple) : iv_monad bool :=
  match t1, t2 with
  | TupleNil, TupleNil => pure true
  | TupleCons v1 t1', TupleCons v2 t2' =>
      let* b := equal_val v1 v2 in
      if b then equal_tuple t1' t2' else pure false
  | _, _ => pure false
  end
with equal_record (r1 r2 : record) : iv_monad bool :=
  match r1, r2 with
  | RecordNil, RecordNil => pure true
  | RecordCons l1 v1 r1', RecordCons l2 v2 r2' =>
      if ident_eqb l1 l2 then
        let* b := equal_val v1 v2 in
        if b then equal_record r1' r2' else pure false
      else pure false
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

Definition dispatch_op2 (op : op2) : val -> val -> iv_monad val :=
  match op with
  | Op2Add => dispatch_add
  | Op2Sub => dispatch_sub
  | Op2Mul => dispatch_mul
  | Op2Div => dispatch_div
  | Op2Mod => dispatch_mod
  | Op2Pow => dispatch_pow
  | Op2Land => dispatch_land
  | Op2Lor => dispatch_lor
  | Op2Lxor => dispatch_lxor
  | Op2Shl => dispatch_shl
  | Op2Shr => dispatch_shr
  | Op2App => dispatch_app
  | Op2Lt => dispatch_lt
  | Op2Le => dispatch_le
  | Op2Gt => dispatch_gt
  | Op2Ge => dispatch_ge
  | Op2Eq => dispatch_eq
  | Op2Neq => dispatch_neq
  end.
