From Stdlib Require Import String Qcanon ZArith.
From shift_reset.lib Require Import comparison float int.
From shift_reset.core Require Import syntax loc tag val.
From shift_reset.interpreter Require Import ierror imonad unwrap.

Local Open Scope imonad_scope.

Definition dispatch_pos (v : val) : imonad val :=
  match v with
  | VInt _ => imonad_pure v
  | VFloat _ => imonad_pure v
  | _ => imonad_throw_error (Type_error "dispatch_pos")
  end.

Definition dispatch_neg (v : val) : imonad val :=
  match v with
  | VInt z => imonad_pure (VInt (Z.opp z))
  | VFloat q => imonad_pure (VFloat (Qcopp q))
  | _ => imonad_throw_error (Type_error "dispatch_neg")
  end.

Definition dispatch_not (v : val) : imonad val :=
  match v with
  | VTrue => imonad_pure VFalse
  | VFalse => imonad_pure VTrue
  | _ => imonad_throw_error (Type_error "dispatch_not")
  end.

Definition dispatch_op1 (op : op1) : val -> imonad val :=
  match op with
  | Op1Pos => dispatch_pos
  | Op1Neg => dispatch_neg
  | Op1Not => dispatch_not
  end.

Definition vint_add (z : Z) (arg : val) : imonad val :=
  VInt_by2 Z.add z <$> unwrap_vint arg.

Definition vint_sub (z : Z) (arg : val) : imonad val :=
  VInt_by2 Z.sub z <$> unwrap_vint arg.

Definition vint_mul (z : Z) (arg : val) : imonad val :=
  VInt_by2 Z.mul z <$> unwrap_vint arg.

Definition vint_div (z : Z) (arg : val) : imonad val :=
  VInt_by2 Z.div z <$> unwrap_vint arg.

Definition vint_mod (z : Z) (arg : val) : imonad val :=
  VInt_by2 Z.modulo z <$> unwrap_vint arg.

Definition vfloat_add (q : Qc) (arg : val) : imonad val :=
  VFloat_by2 Qcplus q <$> unwrap_vfloat arg.

Definition vfloat_sub (q : Qc) (arg : val) : imonad val :=
  VFloat_by2 Qcminus q <$> unwrap_vfloat arg.

Definition vfloat_mul (q : Qc) (arg : val) : imonad val :=
  VFloat_by2 Qcmult q <$> unwrap_vfloat arg.

Definition vfloat_div (q : Qc) (arg : val) : imonad val :=
  VFloat_by2 Qcdiv q <$> unwrap_vfloat arg.

Definition dispatch_add (v : val) : imonad (val -> imonad val) :=
  match v with
  | VInt z => imonad_pure (vint_add z)
  | VFloat q => imonad_pure (vfloat_add q)
  | _ => imonad_throw_error (Type_error "dispatch_add")
  end.

Definition dispatch_sub (v : val) : imonad (val -> imonad val) :=
  match v with
  | VInt z => imonad_pure (vint_sub z)
  | VFloat q => imonad_pure (vfloat_sub q)
  | _ => imonad_throw_error (Type_error "dispatch_sub")
  end.

Definition dispatch_mul (v : val) : imonad (val -> imonad val) :=
  match v with
  | VInt z => imonad_pure (vint_mul z)
  | VFloat q => imonad_pure (vfloat_mul q)
  | _ => imonad_throw_error (Type_error "dispatch_mul")
  end.

Definition dispatch_div (v : val) : imonad (val -> imonad val) :=
  match v with
  | VInt z => imonad_pure (vint_div z)
  | VFloat q => imonad_pure (vfloat_div q)
  | _ => imonad_throw_error (Type_error "dispatch_div")
  end.

Definition dispatch_mod (v : val) : imonad (val -> imonad val) :=
  match v with
  | VInt z => imonad_pure (vint_mod z)
  | _ => imonad_throw_error (Type_error "dispatch_mod")
  end.

Fixpoint compare_val (v1 v2 : val) : imonad comparison :=
  match v1, v2 with
  | VUnit, VUnit => imonad_pure Eq
  | VInt z1, VInt z2 => imonad_pure (Z.compare z1 z2)
  | VFloat q1, VFloat q2 => imonad_pure (Qccompare q1 q2)
  | VTrue, VTrue => imonad_pure Eq
  | VTrue, VFalse => imonad_pure Gt
  | VFalse, VTrue => imonad_pure Lt
  | VFalse, VFalse => imonad_pure Eq
  | VPair v11 v12, VPair v21 v22 =>
      c <- compare_val v11 v21;
      match c with
      | Eq => compare_val v12 v22
      | _ => imonad_pure c
      end
  | VInl v1', VInl v2' => compare_val v1' v2'
  | VInr v1', VInr v2' => compare_val v1' v2'
  | VInl _, VInr _ => imonad_pure Lt
  | VInr _, VInl _ => imonad_pure Gt
  | _, _ => imonad_throw_error (Type_error "compare_val")
  end.

Definition vprod_compare (v1 v2 arg : val) : imonad comparison :=
  p <- unwrap_vprod arg;
  let (v1', v2') := p in
  c <- compare_val v1 v1';
  match c with
  | Eq => compare_val v2 v2'
  | _ => imonad_pure c
  end.

Definition vsum_compare1 (v arg : val) : imonad comparison :=
  s <- unwrap_vsum arg;
  match s with
  | inl v' => compare_val v v'
  | inr _ => imonad_pure Lt
  end.

Definition vsum_compare2 (v arg : val) : imonad comparison :=
  s <- unwrap_vsum arg;
  match s with
  | inl _ => imonad_pure Gt
  | inr v' => compare_val v v'
  end.

Fixpoint equal_val (v1 v2 : val) : imonad bool :=
  match v1, v2 with
  | VUnit, VUnit => imonad_pure true
  | VInt z1, VInt z2 => imonad_pure (Z.eqb z1 z2)
  | VFloat q1, VFloat q2 => imonad_pure (Qc_eq_bool q1 q2)
  | VTrue, VTrue => imonad_pure true
  | VTrue, VFalse => imonad_pure false
  | VFalse, VTrue => imonad_pure false
  | VFalse, VFalse => imonad_pure true
  | VPair v11 v12, VPair v21 v22 =>
      b <- equal_val v11 v21;
      if b then equal_val v12 v22 else imonad_pure false
  | VInl v1', VInl v2' => equal_val v1' v2'
  | VInr v1', VInr v2' => equal_val v1' v2'
  | VInl _, VInr _ => imonad_pure false
  | VInr _, VInl _ => imonad_pure false
  | VRef l1, VRef l2 => imonad_pure (loc_eqb l1 l2)
  | VExn exn1, VExn exn2 => equal_exn exn1 exn2
  | VEff eff1, VEff eff2 => equal_eff eff1 eff2
  | _, _ => imonad_throw_error (Type_error "equal_val")
  end
with equal_exn (exn1 exn2 : exn) : imonad bool :=
  let (tag1, v1) := exn1 in
  let (tag2, v2) := exn2 in
  if tag_eqb tag1 tag2 then equal_val v1 v2 else imonad_pure false
with equal_eff (eff1 eff2 : eff) : imonad bool :=
  let (tag1, v1) := eff1 in
  let (tag2, v2) := eff2 in
  if tag_eqb tag1 tag2 then equal_val v1 v2 else imonad_pure false.

Definition vprod_equal (v1 v2 arg : val) : imonad bool :=
  p <- unwrap_vprod arg;
  let (v1', v2') := p in
  b <- equal_val v1 v1';
  if b then equal_val v2 v2' else imonad_pure false.

Definition vsum_equal1 (v arg : val) : imonad bool :=
  s <- unwrap_vsum arg;
  match s with
  | inl v' => equal_val v v'
  | inr _ => imonad_pure false
  end.

Definition vsum_equal2 (v arg : val) : imonad bool :=
  s <- unwrap_vsum arg;
  match s with
  | inl _ => imonad_pure false
  | inr v' => equal_val v v'
  end.

Definition vexn_equal (exn : exn) (arg : val) : imonad bool :=
  unwrap_vexn arg >>= equal_exn exn.

Definition veff_equal (eff : eff) (arg : val) : imonad bool :=
  unwrap_veff arg >>= equal_eff eff.

Definition vunit_ltb (arg : val) : imonad val :=
  VFalse <$ unwrap_vunit arg.

Definition vunit_leb (arg : val) : imonad val :=
  VTrue <$ unwrap_vunit arg.

Definition vunit_gtb (arg : val) : imonad val :=
  VFalse <$ unwrap_vunit arg.

Definition vunit_geb (arg : val) : imonad val :=
  VTrue <$ unwrap_vunit arg.

Definition vunit_eqb (arg : val) : imonad val :=
  VTrue <$ unwrap_vunit arg.

Definition vunit_neqb (arg : val) : imonad val :=
  VFalse <$ unwrap_vunit arg.

Definition vint_ltb (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.ltb z <$> unwrap_vint arg.

Definition vint_leb (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.leb z <$> unwrap_vint arg.

Definition vint_gtb (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.gtb z <$> unwrap_vint arg.

Definition vint_geb (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.geb z <$> unwrap_vint arg.

Definition vint_eqb (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.eqb z <$> unwrap_vint arg.

Definition vint_neqb (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z_neqb z <$> unwrap_vint arg.

Definition vfloat_ltb (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_ltb q <$> unwrap_vfloat arg.

Definition vfloat_leb (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_leb q <$> unwrap_vfloat arg.

Definition vfloat_gtb (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_gtb q <$> unwrap_vfloat arg.

Definition vfloat_geb (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_geb q <$> unwrap_vfloat arg.

Definition vfloat_eqb (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_eq_bool q <$> unwrap_vfloat arg.

Definition vfloat_neqb (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_neqb q <$> unwrap_vfloat arg.

Definition vbool_ltb1 (arg : val) : imonad val :=
  VFalse <$ unwrap_vbool arg.

Definition vbool_leb1 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vbool_gtb1 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_geb1 (arg : val) : imonad val :=
  VTrue <$ unwrap_vbool arg.

Definition vbool_eqb1 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vbool_neqb1 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_ltb2 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vbool_leb2 (arg : val) : imonad val :=
  VTrue <$ unwrap_vbool arg.

Definition vbool_gtb2 (arg : val) : imonad val :=
  VFalse <$ unwrap_vbool arg.

Definition vbool_geb2 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_eqb2 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_neqb2 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vprod_ltb (v1 v2 arg : val) : imonad val :=
  VBool_by compare_ltb <$> vprod_compare v1 v2 arg.

Definition vprod_leb (v1 v2 arg : val) : imonad val :=
  VBool_by compare_leb <$> vprod_compare v1 v2 arg.

Definition vprod_gtb (v1 v2 arg : val) : imonad val :=
  VBool_by compare_gtb <$> vprod_compare v1 v2 arg.

Definition vprod_geb (v1 v2 arg : val) : imonad val :=
  VBool_by compare_geb <$> vprod_compare v1 v2 arg.

Definition vprod_eqb (v1 v2 arg : val) : imonad val :=
  VBool <$> vprod_equal v1 v2 arg.

Definition vprod_neqb (v1 v2 arg : val) : imonad val :=
  VBool_by negb <$> vprod_equal v1 v2 arg.

Definition vsum_ltb1 (v arg : val) : imonad val :=
  VBool_by compare_ltb <$> vsum_compare1 v arg.

Definition vsum_leb1 (v arg : val) : imonad val :=
  VBool_by compare_leb <$> vsum_compare1 v arg.

Definition vsum_gtb1 (v arg : val) : imonad val :=
  VBool_by compare_gtb <$> vsum_compare1 v arg.

Definition vsum_geb1 (v arg : val) : imonad val :=
  VBool_by compare_geb <$> vsum_compare1 v arg.

Definition vsum_eqb1 (v arg : val) : imonad val :=
  VBool <$> vsum_equal1 v arg.

Definition vsum_neqb1 (v arg : val) : imonad val :=
  VBool_by negb <$> vsum_equal1 v arg.

Definition vsum_ltb2 (v arg : val) : imonad val :=
  VBool_by compare_ltb <$> vsum_compare2 v arg.

Definition vsum_leb2 (v arg : val) : imonad val :=
  VBool_by compare_leb <$> vsum_compare2 v arg.

Definition vsum_gtb2 (v arg : val) : imonad val :=
  VBool_by compare_gtb <$> vsum_compare2 v arg.

Definition vsum_geb2 (v arg : val) : imonad val :=
  VBool_by compare_geb <$> vsum_compare2 v arg.

Definition vsum_eqb2 (v arg : val) : imonad val :=
  VBool <$> vsum_equal2 v arg.

Definition vsum_neqb2 (v arg : val) : imonad val :=
  VBool_by negb <$> vsum_equal2 v arg.

Definition vref_eqb (l : loc) (arg : val) : imonad val :=
  VBool_by2 loc_eqb l <$> unwrap_vref arg.

Definition vref_neqb (l : loc) (arg : val) : imonad val :=
  VBool_by2 loc_neqb l <$> unwrap_vref arg.

Definition vexn_eqb (exn : exn) (arg : val) : imonad val :=
  VBool <$> vexn_equal exn arg.

Definition vexn_neqb (exn : exn) (arg : val) : imonad val :=
  VBool_by negb <$> vexn_equal exn arg.

Definition veff_eqb (eff : eff) (arg : val) : imonad val :=
  VBool <$> veff_equal eff arg.

Definition veff_neqb (eff : eff) (arg : val) : imonad val :=
  VBool_by negb <$> veff_equal eff arg.

Definition dispatch_ltb (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_ltb
  | VInt z => imonad_pure (vint_ltb z)
  | VFloat q => imonad_pure (vfloat_ltb q)
  | VTrue => imonad_pure vbool_ltb1
  | VFalse => imonad_pure vbool_ltb2
  | VPair v1 v2 => imonad_pure (vprod_ltb v1 v2)
  | VInl v' => imonad_pure (vsum_ltb1 v')
  | VInr v' => imonad_pure (vsum_ltb2 v')
  | _ => imonad_throw_error (Type_error "dispatch_ltb")
  end.

Definition dispatch_leb (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_leb
  | VInt z => imonad_pure (vint_leb z)
  | VFloat q => imonad_pure (vfloat_leb q)
  | VTrue => imonad_pure vbool_leb1
  | VFalse => imonad_pure vbool_leb2
  | VPair v1 v2 => imonad_pure (vprod_leb v1 v2)
  | VInl v' => imonad_pure (vsum_leb1 v')
  | VInr v' => imonad_pure (vsum_leb2 v')
  | _ => imonad_throw_error (Type_error "dispatch_leb")
  end.

Definition dispatch_gtb (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_gtb
  | VInt z => imonad_pure (vint_gtb z)
  | VFloat q => imonad_pure (vfloat_gtb q)
  | VTrue => imonad_pure vbool_gtb1
  | VFalse => imonad_pure vbool_gtb2
  | VPair v1 v2 => imonad_pure (vprod_gtb v1 v2)
  | VInl v' => imonad_pure (vsum_gtb1 v')
  | VInr v' => imonad_pure (vsum_gtb2 v')
  | _ => imonad_throw_error (Type_error "dispatch_gtb")
  end.

Definition dispatch_geb (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_geb
  | VInt z => imonad_pure (vint_geb z)
  | VFloat q => imonad_pure (vfloat_geb q)
  | VTrue => imonad_pure vbool_geb1
  | VFalse => imonad_pure vbool_geb2
  | VPair v1 v2 => imonad_pure (vprod_geb v1 v2)
  | VInl v' => imonad_pure (vsum_geb1 v')
  | VInr v' => imonad_pure (vsum_geb2 v')
  | _ => imonad_throw_error (Type_error "dispatch_geb")
  end.

Definition dispatch_eqb (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_eqb
  | VInt z => imonad_pure (vint_eqb z)
  | VFloat q => imonad_pure (vfloat_eqb q)
  | VTrue => imonad_pure vbool_eqb1
  | VFalse => imonad_pure vbool_eqb2
  | VPair v1 v2 => imonad_pure (vprod_eqb v1 v2)
  | VInl v' => imonad_pure (vsum_eqb1 v')
  | VInr v' => imonad_pure (vsum_eqb2 v')
  | VRef l => imonad_pure (vref_eqb l)
  | VExn exn => imonad_pure (vexn_eqb exn)
  | VEff eff => imonad_pure (veff_eqb eff)
  | _ => imonad_throw_error (Type_error "dispatch_eqb")
  end.

Definition dispatch_neqb (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_neqb
  | VInt z => imonad_pure (vint_neqb z)
  | VFloat q => imonad_pure (vfloat_neqb q)
  | VTrue => imonad_pure vbool_neqb1
  | VFalse => imonad_pure vbool_neqb2
  | VPair v1 v2 => imonad_pure (vprod_neqb v1 v2)
  | VInl v' => imonad_pure (vsum_neqb1 v')
  | VInr v' => imonad_pure (vsum_neqb2 v')
  | VRef l => imonad_pure (vref_neqb l)
  | VExn exn => imonad_pure (vexn_neqb exn)
  | VEff eff => imonad_pure (veff_neqb eff)
  | _ => imonad_throw_error (Type_error "dispatch_neqb")
  end.

Definition dispatch_op2 (op : op2) : val -> imonad (val -> imonad val) :=
  match op with
  | Op2Add => dispatch_add
  | Op2Sub => dispatch_sub
  | Op2Mul => dispatch_mul
  | Op2Div => dispatch_div
  | Op2Mod => dispatch_mod
  | Op2Ltb => dispatch_ltb
  | Op2Leb => dispatch_leb
  | Op2Gtb => dispatch_gtb
  | Op2Geb => dispatch_geb
  | Op2Eqb => dispatch_eqb
  | Op2Neqb => dispatch_neqb
  end.
