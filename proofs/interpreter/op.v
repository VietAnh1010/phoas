From Stdlib Require Import Ascii Bool String Qcanon ZArith.
From shift_reset.lib Require Import compare float.
From shift_reset.core Require Import syntax ident loc val.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad op.
Import ExceptNotations.

Local Open Scope Z_scope.
Local Open Scope Qc_scope.
Local Open Scope except_scope.
Local Open Scope string_scope.
Local Open Scope lazy_bool_scope.

Lemma fold_unfold_compare_val_VTt_VTt :
  compare_val VTt VTt = pure Eq.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VInt_VInt :
  forall (z1 z2 : Z), compare_val (VInt z1) (VInt z2) = pure (z1 ?= z2)%Z.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VFloat_VFloat :
  forall (q1 q2 : Qc), compare_val (VFloat q1) (VFloat q2) = pure (q1 ?= q2)%Qc.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VTrue_VTrue :
  compare_val VTrue VTrue = pure Eq.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VFalse_VFalse :
  compare_val VFalse VFalse = pure Eq.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VTrue_VFalse :
  compare_val VTrue VFalse = pure Gt.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VFalse_VTrue :
  compare_val VFalse VTrue = pure Lt.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VChar_VChar :
  forall (a1 a2 : ascii), compare_val (VChar a1) (VChar a2) = pure (a1 ?= a2)%char.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VString_VString :
  forall (s1 s2 : string), compare_val (VString s1) (VString s2) = pure (s1 ?= s2)%string.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VPair_VPair :
  forall (v11 v12 v21 v22 : val),
    compare_val (VPair v11 v12) (VPair v21 v22) =
    let* c := compare_val v11 v21 in
    match c with
    | Eq => compare_val v12 v22
    | _ => pure c
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VInl_VInl :
  forall (v1' v2' : val), compare_val (VInl v1') (VInl v2') = compare_val v1' v2'.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VInr_VInr :
  forall (v1' v2' : val), compare_val (VInr v1') (VInr v2') = compare_val v1' v2'.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VInl_VInr :
  forall (v1' v2' : val), compare_val (VInl v1') (VInr v2') = pure Lt.
Proof. reflexivity. Qed.

Lemma fold_unfold_compare_val_VInr_VInl :
  forall (v1' v2' : val), compare_val (VInr v1') (VInl v2') = pure Gt.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VTt_VTt :
  equal_val VTt VTt = pure true.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VInt_VInt :
  forall (z1 z2 : Z), equal_val (VInt z1) (VInt z2) = pure (z1 =? z2)%Z.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VFloat_VFloat :
  forall (q1 q2 : Qc), equal_val (VFloat q1) (VFloat q2) = pure (q1 =? q2)%Qc.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VTrue_VTrue :
  equal_val VTrue VTrue = pure true.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VFalse_VFalse :
  equal_val VFalse VFalse = pure true.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VTrue_VFalse :
  equal_val VTrue VFalse = pure false.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VFalse_VTrue :
  equal_val VFalse VTrue = pure false.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VChar_VChar :
  forall (a1 a2 : ascii), equal_val (VChar a1) (VChar a2) = pure (a1 =? a2)%char.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VString_VString :
  forall (s1 s2 : string), equal_val (VString s1) (VString s2) = pure (s1 =? s2)%string.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VPair_VPair :
  forall (v11 v12 v21 v22 : val),
    equal_val (VPair v11 v12) (VPair v21 v22) =
    let* b := equal_val v11 v21 in
    if b then equal_val v12 v22 else pure false.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VTuple_VTuple :
  forall (t1 t2 : tuple), equal_val (VTuple t1) (VTuple t2) = equal_tuple t1 t2.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VRecord_VRecord :
  forall (r1 r2 : record), equal_val (VRecord r1) (VRecord r2) = equal_record r1 r2.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VInl_VInl :
  forall (v1' v2' : val), equal_val (VInl v1') (VInl v2') = equal_val v1' v2'.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VInr_VInr :
  forall (v1' v2' : val), equal_val (VInr v1') (VInr v2') = equal_val v1' v2'.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VInl_VInr :
  forall (v1' v2' : val), equal_val (VInl v1') (VInr v2') = pure false.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VInr_VInl :
  forall (v1' v2' : val), equal_val (VInr v1') (VInl v2') = pure false.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VVariant_VVariant :
  forall (l1 l2 : ident)
         (v1' v2' : val),
    equal_val (VVariant l1 v1') (VVariant l2 v2') =
    if ident_eqb l1 l2 then equal_val v1' v2' else pure false.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VRef_VRef :
  forall (l1 l2 : loc), equal_val (VRef l1) (VRef l2) = pure (loc_eqb l1 l2).
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_val_VArray_VArray :
  forall (l1 l2 : loc)
         (z1 z2 : Z),
    equal_val (VArray l1 z1) (VArray l2 z2) =
    pure (loc_eqb l1 l2 &&& (z1 =? z2)%Z).
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_tuple_TupleNil_TupleNil :
  equal_tuple TupleNil TupleNil = pure true.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_tuple_TupleCons_TupleCons :
  forall (v1 v2 : val)
         (t1' t2' : tuple),
    equal_tuple (TupleCons v1 t1') (TupleCons v2 t2') =
    let* b := equal_val v1 v2 in
    if b then equal_tuple t1' t2' else pure false.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_record_RecordNil_RecordNil :
  equal_record RecordNil RecordNil = pure true.
Proof. reflexivity. Qed.

Lemma fold_unfold_equal_record_RecordCons_RecordCons :
  forall (l1 l2 : ident)
         (v1 v2 : val)
         (r1' r2' : record),
    equal_record (RecordCons l1 v1 r1') (RecordCons l2 v2 r2') =
    if ident_eqb l1 l2 then
      let* b := equal_val v1 v2 in
      if b then equal_record r1' r2' else pure false
    else pure false.
Proof. reflexivity. Qed.
