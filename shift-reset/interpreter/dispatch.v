From Stdlib Require Import String Qcanon ZArith.
From shift_reset.lib Require Import comparison float int.
From shift_reset.core Require Import syntax loc tag val.
From shift_reset.interpreter Require Import ierror imonad unwrap.

Local Open Scope imonad_scope.

Definition dispatch_neg (v : val) : imonad val :=
  match v with
  | VInt z => imonad_pure (VInt (Z.opp z))
  | VFloat q => imonad_pure (VFloat (Qcopp q))
  | _ => imonad_throw_error (Type_error "")
  end.

Definition dispatch_not (v : val) : imonad val :=
  match v with
  | VTrue => imonad_pure VFalse
  | VFalse => imonad_pure VTrue
  | _ => imonad_throw_error (Type_error "")
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

Definition vunit_lt (arg : val) : imonad val :=
  VFalse <$ unwrap_vunit arg.

Definition vunit_le (arg : val) : imonad val :=
  VTrue <$ unwrap_vunit arg.

Definition vunit_gt (arg : val) : imonad val :=
  VFalse <$ unwrap_vunit arg.

Definition vunit_ge (arg : val) : imonad val :=
  VTrue <$ unwrap_vunit arg.

Definition vunit_eq (arg : val) : imonad val :=
  VTrue <$ unwrap_vunit arg.

Definition vunit_neq (arg : val) : imonad val :=
  VFalse <$ unwrap_vunit arg.

Definition vint_lt (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.ltb z <$> unwrap_vint arg.

Definition vint_le (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.leb z <$> unwrap_vint arg.

Definition vint_gt (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.gtb z <$> unwrap_vint arg.

Definition vint_ge (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.geb z <$> unwrap_vint arg.

Definition vint_eq (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z.eqb z <$> unwrap_vint arg.

Definition vint_neq (z : Z) (arg : val) : imonad val :=
  VBool_by2 Z_neqb z <$> unwrap_vint arg.

Definition vfloat_lt (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_ltb q <$> unwrap_vfloat arg.

Definition vfloat_le (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_leb q <$> unwrap_vfloat arg.

Definition vfloat_gt (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_gtb q <$> unwrap_vfloat arg.

Definition vfloat_ge (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_geb q <$> unwrap_vfloat arg.

Definition vfloat_eq (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_eq_bool q <$> unwrap_vfloat arg.

Definition vfloat_neq (q : Qc) (arg : val) : imonad val :=
  VBool_by2 Qc_neqb q <$> unwrap_vfloat arg.

Definition vbool_lt1 (arg : val) : imonad val :=
  VFalse <$ unwrap_vbool arg.

Definition vbool_le1 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vbool_gt1 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_ge1 (arg : val) : imonad val :=
  VTrue <$ unwrap_vbool arg.

Definition vbool_eq1 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vbool_neq1 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_lt2 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vbool_le2 (arg : val) : imonad val :=
  VTrue <$ unwrap_vbool arg.

Definition vbool_gt2 (arg : val) : imonad val :=
  VFalse <$ unwrap_vbool arg.

Definition vbool_ge2 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_eq2 (arg : val) : imonad val :=
  VBool_by negb <$> unwrap_vbool arg.

Definition vbool_neq2 (arg : val) : imonad val :=
  VBool <$> unwrap_vbool arg.

Definition vprod_lt (v1 v2 arg : val) : imonad val :=
  VBool_by compare_ltb <$> vprod_compare v1 v2 arg.

Definition vprod_le (v1 v2 arg : val) : imonad val :=
  VBool_by compare_leb <$> vprod_compare v1 v2 arg.

Definition vprod_gt (v1 v2 arg : val) : imonad val :=
  VBool_by compare_gtb <$> vprod_compare v1 v2 arg.

Definition vprod_ge (v1 v2 arg : val) : imonad val :=
  VBool_by compare_geb <$> vprod_compare v1 v2 arg.

Definition vprod_eq (v1 v2 arg : val) : imonad val :=
  VBool <$> vprod_equal v1 v2 arg.

Definition vprod_neq (v1 v2 arg : val) : imonad val :=
  VBool_by negb <$> vprod_equal v1 v2 arg.

Definition vsum_lt1 (v arg : val) : imonad val :=
  VBool_by compare_ltb <$> vsum_compare1 v arg.

Definition vsum_le1 (v arg : val) : imonad val :=
  VBool_by compare_leb <$> vsum_compare1 v arg.

Definition vsum_gt1 (v arg : val) : imonad val :=
  VBool_by compare_gtb <$> vsum_compare1 v arg.

Definition vsum_ge1 (v arg : val) : imonad val :=
  VBool_by compare_geb <$> vsum_compare1 v arg.

Definition vsum_eq1 (v arg : val) : imonad val :=
  VBool <$> vsum_equal1 v arg.

Definition vsum_neq1 (v arg : val) : imonad val :=
  VBool_by negb <$> vsum_equal1 v arg.

Definition vsum_lt2 (v arg : val) : imonad val :=
  VBool_by compare_ltb <$> vsum_compare2 v arg.

Definition vsum_le2 (v arg : val) : imonad val :=
  VBool_by compare_leb <$> vsum_compare2 v arg.

Definition vsum_gt2 (v arg : val) : imonad val :=
  VBool_by compare_gtb <$> vsum_compare2 v arg.

Definition vsum_ge2 (v arg : val) : imonad val :=
  VBool_by compare_geb <$> vsum_compare2 v arg.

Definition vsum_eq2 (v arg : val) : imonad val :=
  VBool <$> vsum_equal2 v arg.

Definition vsum_neq2 (v arg : val) : imonad val :=
  VBool_by negb <$> vsum_equal2 v arg.

Definition vref_eq (l : loc) (arg : val) : imonad val :=
  VBool_by2 loc_eqb l <$> unwrap_vref arg.

Definition vref_neq (l : loc) (arg : val) : imonad val :=
  VBool_by2 loc_neqb l <$> unwrap_vref arg.

Definition vexn_eq (exn : exn) (arg : val) : imonad val :=
  VBool <$> vexn_equal exn arg.

Definition vexn_neq (exn : exn) (arg : val) : imonad val :=
  VBool_by negb <$> vexn_equal exn arg.

Definition veff_eq (eff : eff) (arg : val) : imonad val :=
  VBool <$> veff_equal eff arg.

Definition veff_neq (eff : eff) (arg : val) : imonad val :=
  VBool_by negb <$> veff_equal eff arg.

Definition dispatch_lt (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_lt
  | VInt z => imonad_pure (vint_lt z)
  | VFloat q => imonad_pure (vfloat_lt q)
  | VTrue => imonad_pure vbool_lt1
  | VFalse => imonad_pure vbool_lt2
  | VPair v1 v2 => imonad_pure (vprod_lt v1 v2)
  | VInl v' => imonad_pure (vsum_lt1 v')
  | VInr v' => imonad_pure (vsum_lt2 v')
  | _ => imonad_throw_error (Type_error "dispatch_lt")
  end.

Definition dispatch_le (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_le
  | VInt z => imonad_pure (vint_le z)
  | VFloat q => imonad_pure (vfloat_le q)
  | VTrue => imonad_pure vbool_le1
  | VFalse => imonad_pure vbool_le2
  | VPair v1 v2 => imonad_pure (vprod_le v1 v2)
  | VInl v' => imonad_pure (vsum_le1 v')
  | VInr v' => imonad_pure (vsum_le2 v')
  | _ => imonad_throw_error (Type_error "dispatch_le")
  end.

Definition dispatch_gt (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_gt
  | VInt z => imonad_pure (vint_gt z)
  | VFloat q => imonad_pure (vfloat_gt q)
  | VTrue => imonad_pure vbool_gt1
  | VFalse => imonad_pure vbool_gt2
  | VPair v1 v2 => imonad_pure (vprod_gt v1 v2)
  | VInl v' => imonad_pure (vsum_gt1 v')
  | VInr v' => imonad_pure (vsum_gt2 v')
  | _ => imonad_throw_error (Type_error "dispatch_gt")
  end.

Definition dispatch_ge (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_ge
  | VInt z => imonad_pure (vint_ge z)
  | VFloat q => imonad_pure (vfloat_ge q)
  | VTrue => imonad_pure vbool_ge1
  | VFalse => imonad_pure vbool_ge2
  | VPair v1 v2 => imonad_pure (vprod_ge v1 v2)
  | VInl v' => imonad_pure (vsum_ge1 v')
  | VInr v' => imonad_pure (vsum_ge2 v')
  | _ => imonad_throw_error (Type_error "dispatch_ge")
  end.

Definition dispatch_eq (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_eq
  | VInt z => imonad_pure (vint_eq z)
  | VFloat q => imonad_pure (vfloat_eq q)
  | VTrue => imonad_pure vbool_eq1
  | VFalse => imonad_pure vbool_eq2
  | VPair v1 v2 => imonad_pure (vprod_eq v1 v2)
  | VInl v' => imonad_pure (vsum_eq1 v')
  | VInr v' => imonad_pure (vsum_eq2 v')
  | VRef l => imonad_pure (vref_eq l)
  | VExn exn => imonad_pure (vexn_eq exn)
  | VEff eff => imonad_pure (veff_eq eff)
  | _ => imonad_throw_error (Type_error "dispatch_eq")
  end.

Definition dispatch_neq (v : val) : imonad (val -> imonad val) :=
  match v with
  | VUnit => imonad_pure vunit_neq
  | VInt z => imonad_pure (vint_neq z)
  | VFloat q => imonad_pure (vfloat_neq q)
  | VTrue => imonad_pure vbool_neq1
  | VFalse => imonad_pure vbool_neq2
  | VPair v1 v2 => imonad_pure (vprod_neq v1 v2)
  | VInl v' => imonad_pure (vsum_neq1 v')
  | VInr v' => imonad_pure (vsum_neq2 v')
  | VRef l => imonad_pure (vref_neq l)
  | VExn exn => imonad_pure (vexn_neq exn)
  | VEff eff => imonad_pure (veff_neq eff)
  | _ => imonad_throw_error (Type_error "")
  end.
