From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.lib Require Import char comparison float int string.
From shift_reset.core Require Import syntax loc tag val.
From shift_reset.interpreter Require Import ierror imonad unwrap.

Local Open Scope string_scope.
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

Definition vstring_app (s : string) (arg : val) : imonad val :=
  VString_by2 String.append s <$> unwrap_vstring arg.

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

Definition dispatch_app (v : val) : imonad (val -> imonad val) :=
  match v with
  | VString s => imonad_pure (vstring_app s)
  | _ => imonad_throw_error (Type_error "dispatch_app")
  end.

Fixpoint compare_val (v1 v2 : val) : imonad comparison :=
  match v1, v2 with
  | VTt, VTt => imonad_pure Eq
  | VInt z1, VInt z2 => imonad_pure (Z.compare z1 z2)
  | VFloat q1, VFloat q2 => imonad_pure (Qccompare q1 q2)
  | VTrue, VTrue => imonad_pure Eq
  | VTrue, VFalse => imonad_pure Gt
  | VFalse, VTrue => imonad_pure Lt
  | VFalse, VFalse => imonad_pure Eq
  | VChar a1, VChar a2 => imonad_pure (Ascii.compare a1 a2)
  | VString s1, VString s2 => imonad_pure (String.compare s1 s2)
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
  '(v1', v2') <- unwrap_vprod arg;
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
  | VTt, VTt => imonad_pure true
  | VInt z1, VInt z2 => imonad_pure (Z.eqb z1 z2)
  | VFloat q1, VFloat q2 => imonad_pure (Qc_eq_bool q1 q2)
  | VTrue, VTrue => imonad_pure true
  | VTrue, VFalse => imonad_pure false
  | VFalse, VTrue => imonad_pure false
  | VFalse, VFalse => imonad_pure true
  | VChar a1, VChar a2 => imonad_pure (Ascii.eqb a1 a2)
  | VString s1, VString s2 => imonad_pure (String.eqb s1 s2)
  | VPair v11 v12, VPair v21 v22 =>
      b <- equal_val v11 v21;
      if b then equal_val v12 v22 else imonad_pure false
  | VTuple t1, VTuple t2 => equal_tuple t1 t2
  | VRecord r1, VRecord r2 => equal_record r1 r2
  | VInl v1', VInl v2' => equal_val v1' v2'
  | VInr v1', VInr v2' => equal_val v1' v2'
  | VInl _, VInr _ => imonad_pure false
  | VInr _, VInl _ => imonad_pure false
  | VVariant tag1 v1', VVariant tag2 v2' => if tag_eqb tag1 tag2 then equal_val v1' v2' else imonad_pure false
  | VRef l1, VRef l2 => imonad_pure (loc_eqb l1 l2)
  | VExn tag1 v1', VExn tag2 v2' => if tag_eqb tag1 tag2 then equal_val v1' v2' else imonad_pure false
  | VEff tag1 v1', VEff tag2 v2' => if tag_eqb tag1 tag2 then equal_val v1' v2' else imonad_pure false
  | _, _ => imonad_throw_error (Type_error "equal_val")
  end
with equal_tuple (t1 t2 : tuple) : imonad bool :=
  match t1, t2 with
  | TupleNil, TupleNil => imonad_pure true
  | TupleCons v1 t1', TupleCons v2 t2' =>
      b <- equal_val v1 v2;
      if b then equal_tuple t1' t2' else imonad_pure false
  | _, _ => imonad_pure false
  end
with equal_record (r1 r2 : record) : imonad bool :=
  match r1, r2 with
  | RecordNil, RecordNil => imonad_pure true
  | RecordCons tag1 v1 r1', RecordCons tag2 v2 r2' =>
      if tag_eqb tag1 tag2 then
        b <- equal_val v1 v2;
        if b then equal_record r1' r2' else imonad_pure false
      else imonad_pure false
  | _, _ => imonad_pure false
  end.

Definition vprod_equal (v1 v2 arg : val) : imonad bool :=
  '(v1', v2') <- unwrap_vprod arg;
  b <- equal_val v1 v1';
  if b then equal_val v2 v2' else imonad_pure false.

Definition vtuple_equal (t : tuple) (arg : val) : imonad bool :=
  unwrap_vtuple arg >>= equal_tuple t.

Definition vrecord_equal (r : record) (arg : val) : imonad bool :=
  unwrap_vrecord arg >>= equal_record r.

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

Definition vvariant_equal (tag : tag) (v arg : val) : imonad bool :=
  '(Variant tag' v') <- unwrap_vvariant arg;
  if tag_eqb tag tag' then equal_val v v' else imonad_pure false.

Definition vexn_equal (tag : tag) (v arg : val) : imonad bool :=
  '(Exn tag' v') <- unwrap_vexn arg;
  if tag_eqb tag tag' then equal_val v v' else imonad_pure false.

Definition veff_equal (tag : tag) (v arg : val) : imonad bool :=
  '(Eff tag' v') <- unwrap_veff arg;
  if tag_eqb tag tag' then equal_val v v' else imonad_pure false.

(** Unit *)

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

(** Int *)

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

(** Float *)

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

(** Bool *)

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

(** Char *)

Definition vchar_lt (a : ascii) (arg : val) : imonad val :=
  VBool_by2 Ascii.ltb a <$> unwrap_vchar arg.

Definition vchar_le (a : ascii) (arg : val) : imonad val :=
  VBool_by2 Ascii.leb a <$> unwrap_vchar arg.

Definition vchar_gt (a : ascii) (arg : val) : imonad val :=
  VBool_by2 ascii_gtb a <$> unwrap_vchar arg.

Definition vchar_ge (a : ascii) (arg : val) : imonad val :=
  VBool_by2 ascii_geb a <$> unwrap_vchar arg.

Definition vchar_eq (a : ascii) (arg : val) : imonad val :=
  VBool_by2 Ascii.eqb a <$> unwrap_vchar arg.

Definition vchar_neq (a : ascii) (arg : val) : imonad val :=
  VBool_by2 ascii_neqb a <$> unwrap_vchar arg.

(** String *)

Definition vstring_lt (s : string) (arg : val) : imonad val :=
  VBool_by2 String.ltb s <$> unwrap_vstring arg.

Definition vstring_le (s : string) (arg : val) : imonad val :=
  VBool_by2 String.leb s <$> unwrap_vstring arg.

Definition vstring_gt (s : string) (arg : val) : imonad val :=
  VBool_by2 string_gtb s <$> unwrap_vstring arg.

Definition vstring_ge (s : string) (arg : val) : imonad val :=
  VBool_by2 string_geb s <$> unwrap_vstring arg.

Definition vstring_eq (s : string) (arg : val) : imonad val :=
  VBool_by2 String.eqb s <$> unwrap_vstring arg.

Definition vstring_neq (s : string) (arg : val) : imonad val :=
  VBool_by2 string_neqb s <$> unwrap_vstring arg.

(** Prod *)

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

(** Sum *)

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

(** Tuple *)

Definition vtuple_eq (t : tuple) (arg : val) : imonad val :=
  VBool <$> vtuple_equal t arg.

Definition vtuple_neq (t : tuple) (arg : val) : imonad val :=
  VBool_by negb <$> vtuple_equal t arg.

(** Record *)

Definition vrecord_eq (r : record) (arg : val) : imonad val :=
  VBool <$> vrecord_equal r arg.

Definition vrecord_neq (r : record) (arg : val) : imonad val :=
  VBool_by negb <$> vrecord_equal r arg.

(** Variant *)

Definition vvariant_eq (tag : tag) (v arg : val) : imonad val :=
  VBool <$> vvariant_equal tag v arg.

Definition vvariant_neq (tag : tag) (v arg : val) : imonad val :=
  VBool_by negb <$> vvariant_equal tag v arg.

(** Ref *)

Definition vref_eq (l : loc) (arg : val) : imonad val :=
  VBool_by2 loc_eqb l <$> unwrap_vref arg.

Definition vref_neq (l : loc) (arg : val) : imonad val :=
  VBool_by2 loc_neqb l <$> unwrap_vref arg.

(** Exn *)

Definition vexn_eq (tag : tag) (v arg : val) : imonad val :=
  VBool <$> vexn_equal tag v arg.

Definition vexn_neq (tag : tag) (v arg : val) : imonad val :=
  VBool_by negb <$> vexn_equal tag v arg.

(** Eff *)

Definition veff_eq (tag : tag) (v arg : val) : imonad val :=
  VBool <$> veff_equal tag v arg.

Definition veff_neq (tag : tag) (v arg : val) : imonad val :=
  VBool_by negb <$> veff_equal tag v arg.

Definition dispatch_lt (v : val) : imonad (val -> imonad val) :=
  match v with
  | VTt => imonad_pure vunit_lt
  | VInt z => imonad_pure (vint_lt z)
  | VFloat q => imonad_pure (vfloat_lt q)
  | VTrue => imonad_pure vbool_lt1
  | VFalse => imonad_pure vbool_lt2
  | VChar a => imonad_pure (vchar_lt a)
  | VString s => imonad_pure (vstring_lt s)
  | VPair v1 v2 => imonad_pure (vprod_lt v1 v2)
  | VInl v' => imonad_pure (vsum_lt1 v')
  | VInr v' => imonad_pure (vsum_lt2 v')
  | _ => imonad_throw_error (Type_error "dispatch_lt")
  end.

Definition dispatch_le (v : val) : imonad (val -> imonad val) :=
  match v with
  | VTt => imonad_pure vunit_le
  | VInt z => imonad_pure (vint_le z)
  | VFloat q => imonad_pure (vfloat_le q)
  | VTrue => imonad_pure vbool_le1
  | VFalse => imonad_pure vbool_le2
  | VChar a => imonad_pure (vchar_le a)
  | VString s => imonad_pure (vstring_le s)
  | VPair v1 v2 => imonad_pure (vprod_le v1 v2)
  | VInl v' => imonad_pure (vsum_le1 v')
  | VInr v' => imonad_pure (vsum_le2 v')
  | _ => imonad_throw_error (Type_error "dispatch_le")
  end.

Definition dispatch_gt (v : val) : imonad (val -> imonad val) :=
  match v with
  | VTt => imonad_pure vunit_gt
  | VInt z => imonad_pure (vint_gt z)
  | VFloat q => imonad_pure (vfloat_gt q)
  | VTrue => imonad_pure vbool_gt1
  | VFalse => imonad_pure vbool_gt2
  | VChar a => imonad_pure (vchar_gt a)
  | VString s => imonad_pure (vstring_gt s)
  | VPair v1 v2 => imonad_pure (vprod_gt v1 v2)
  | VInl v' => imonad_pure (vsum_gt1 v')
  | VInr v' => imonad_pure (vsum_gt2 v')
  | _ => imonad_throw_error (Type_error "dispatch_gt")
  end.

Definition dispatch_ge (v : val) : imonad (val -> imonad val) :=
  match v with
  | VTt => imonad_pure vunit_ge
  | VInt z => imonad_pure (vint_ge z)
  | VFloat q => imonad_pure (vfloat_ge q)
  | VTrue => imonad_pure vbool_ge1
  | VFalse => imonad_pure vbool_ge2
  | VChar a => imonad_pure (vchar_ge a)
  | VString s => imonad_pure (vstring_ge s)
  | VPair v1 v2 => imonad_pure (vprod_ge v1 v2)
  | VInl v' => imonad_pure (vsum_ge1 v')
  | VInr v' => imonad_pure (vsum_ge2 v')
  | _ => imonad_throw_error (Type_error "dispatch_ge")
  end.

Definition dispatch_eq (v : val) : imonad (val -> imonad val) :=
  match v with
  | VTt => imonad_pure vunit_eq
  | VInt z => imonad_pure (vint_eq z)
  | VFloat q => imonad_pure (vfloat_eq q)
  | VTrue => imonad_pure vbool_eq1
  | VFalse => imonad_pure vbool_eq2
  | VChar a => imonad_pure (vchar_eq a)
  | VString s => imonad_pure (vstring_eq s)
  | VPair v1 v2 => imonad_pure (vprod_eq v1 v2)
  | VTuple t => imonad_pure (vtuple_eq t)
  | VRecord r => imonad_pure (vrecord_eq r)
  | VInl v' => imonad_pure (vsum_eq1 v')
  | VInr v' => imonad_pure (vsum_eq2 v')
  | VVariant tag v' => imonad_pure (vvariant_eq tag v')
  | VRef l => imonad_pure (vref_eq l)
  | VExn tag v' => imonad_pure (vexn_eq tag v')
  | VEff tag v' => imonad_pure (veff_eq tag v')
  | _ => imonad_throw_error (Type_error "dispatch_eq")
  end.

Definition dispatch_neq (v : val) : imonad (val -> imonad val) :=
  match v with
  | VTt => imonad_pure vunit_neq
  | VInt z => imonad_pure (vint_neq z)
  | VFloat q => imonad_pure (vfloat_neq q)
  | VTrue => imonad_pure vbool_neq1
  | VFalse => imonad_pure vbool_neq2
  | VChar a => imonad_pure (vchar_neq a)
  | VString s => imonad_pure (vstring_neq s)
  | VPair v1 v2 => imonad_pure (vprod_neq v1 v2)
  | VTuple t => imonad_pure (vtuple_neq t)
  | VRecord r => imonad_pure (vrecord_neq r)
  | VInl v' => imonad_pure (vsum_neq1 v')
  | VInr v' => imonad_pure (vsum_neq2 v')
  | VVariant tag v' => imonad_pure (vvariant_neq tag v')
  | VRef l => imonad_pure (vref_neq l)
  | VExn tag v' => imonad_pure (vexn_neq tag v')
  | VEff tag v' => imonad_pure (veff_neq tag v')
  | _ => imonad_throw_error (Type_error "dispatch_neq")
  end.

Definition dispatch_op2 (op : op2) : val -> imonad (val -> imonad val) :=
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
