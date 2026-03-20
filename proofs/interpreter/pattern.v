From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.lib Require Import float.
From shift_reset.core Require Import syntax ident record.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error pattern.
Import ExceptNotations.

Local Open Scope except_scope.

Lemma fold_unfold_match_pattern_PAny :
  forall (v : val) (e : env), match_pattern PAny v e = pure (Some e).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PVar :
  forall (x : ident)
         (v : val)
         (e : env),
    match_pattern (PVar x) v e =
    pure (Some (ECons x v e)).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PAlias :
  forall (p' : pattern)
         (x : ident)
         (v : val)
         (e : env),
    match_pattern (PAlias p' x) v e =
    let+ o := match_pattern p' v e in
    match o with
    | None => None
    | Some e' => Some (ECons x v e')
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_POr :
  forall (p1 p2 : pattern)
         (v : val)
         (e : env),
    match_pattern (POr p1 p2) v e =
    let* o := match_pattern p1 v e in
    match o with
    | None => match_pattern p2 v e
    | Some _ => pure o
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PTt_VTt :
  forall (e : env), match_pattern PTt VTt e = pure (Some e).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PInt_VInt :
  forall (z1 z2 : Z)
         (e : env),
    match_pattern (PInt z1) (VInt z2) e =
    pure (if (z1 =? z2)%Z then Some e else None).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PFloat_VFloat :
  forall (q1 q2 : Qc)
         (e : env),
    match_pattern (PFloat q1) (VFloat q2) e =
    pure (if (q1 =? q2)%Qc then Some e else None).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PTrue_VTrue :
  forall (e : env), match_pattern PTrue VTrue e = pure (Some e).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PFalse_VFalse :
  forall (e : env), match_pattern PFalse VFalse e = pure (Some e).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PTrue_VFalse :
  forall (e : env), match_pattern PTrue VFalse e = pure None.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PFalse_VTrue :
  forall (e : env), match_pattern PFalse VTrue e = pure None.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PChar_VChar :
  forall (a1 a2 : ascii)
         (e : env),
    match_pattern (PChar a1) (VChar a2) e =
    pure (if (a1 =? a2)%char then Some e else None).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PString_VString :
  forall (s1 s2 : string)
         (e : env),
    match_pattern (PString s1) (VString s2) e =
    pure (if (s1 =? s2)%string then Some e else None).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PPair_VPair :
  forall (p1 p2 : pattern)
         (v1 v2 : val)
         (e : env),
    match_pattern (PPair p1 p2) (VPair v1 v2) e =
    let* o := match_pattern p1 v1 e in
    match o with
    | None => pure None
    | Some e' => match_pattern p2 v2 e'
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PTuple_VTuple :
  forall (p' : tuple_pattern)
         (t : tuple)
         (e : env),
    match_pattern (PTuple p') (VTuple t) e =
    match_tuple_pattern p' t e.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PRecord_VRecord :
  forall (p' : record_pattern)
         (r : record)
         (e : env),
    match_pattern (PRecord p') (VRecord r) e =
    match_record_pattern p' r e.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PInl_VInl :
  forall (p' : pattern)
         (v' : val)
         (e : env),
    match_pattern (PInl p') (VInl v') e =
    match_pattern p' v' e.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PInr_VInr :
  forall (p' : pattern)
         (v' : val)
         (e : env),
    match_pattern (PInr p') (VInr v') e =
    match_pattern p' v' e.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PInl_VInr :
  forall (p' : pattern)
         (v' : val)
         (e : env),
    match_pattern (PInl p') (VInr v') e =
    pure None.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PInr_VInl :
  forall (p' : pattern)
         (v' : val)
         (e : env),
    match_pattern (PInr p') (VInl v') e =
    pure None.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_pattern_PVariant_VVariant :
  forall (l1 l2 : ident)
         (p' : pattern)
         (v' : val)
         (e : env),
    match_pattern (PVariant l1 p') (VVariant l2 v') e =
    if ident_eqb l1 l2 then match_pattern p' v' e else pure None.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_tuple_pattern_PTupleNil_TupleNil :
  forall (e : env), match_tuple_pattern PTupleNil TupleNil e = pure (Some e).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_tuple_pattern_PTupleCons_TupleCons :
  forall (p1 : pattern)
         (p2 : tuple_pattern)
         (v : val)
         (t' : tuple)
         (e : env),
    match_tuple_pattern (PTupleCons p1 p2) (TupleCons v t') e =
    let* o := match_pattern p1 v e in
    match o with
    | None => pure None
    | Some e' => match_tuple_pattern p2 t' e'
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_record_pattern_PRecordNil_RecordNil :
  forall (e : env), match_record_pattern PRecordNil RecordNil e = pure (Some e).
Proof. reflexivity. Qed.

Lemma fold_unfold_match_record_pattern_PRecordNil_RecordCons :
  forall (l : ident)
         (v : val)
         (r : record)
         (e : env),
    match_record_pattern PRecordNil (RecordCons l v r) e =
    throw (Match_failure "match_record_pattern").
Proof. reflexivity. Qed.

Lemma fold_unfold_match_record_pattern_PRecordRest :
  forall (p' : pattern)
         (r : record)
         (e : env),
    match_record_pattern (PRecordRest p') r e =
    match_pattern p' (VRecord r) e.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_record_pattern_PRecordCons0 :
  forall (l : ident)
         (p' : record_pattern)
         (r : record)
         (e : env),
    match_record_pattern (PRecordCons0 l p') r e =
    let (o, r') := record_find_remove l r in
    match o with
    | None => throw (Match_failure "match_record_pattern")
    | Some v => match_record_pattern p' r' (ECons l v e)
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_match_record_pattern_PRecordCons1 :
  forall (l : ident)
         (p1 : pattern)
         (p2 : record_pattern)
         (r : record)
         (e : env),
    match_record_pattern (PRecordCons1 l p1 p2) r e =
    let (o, r') := record_find_remove l r in
    match o with
    | None => throw (Match_failure "match_record_pattern")
    | Some v =>
        let* o := match_pattern p1 v e in
        match o with
        | None => pure None
        | Some e' => match_record_pattern p2 r' e'
        end
    end.
Proof. reflexivity. Qed.
