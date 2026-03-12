From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.lib Require Import float.
From shift_reset.core Require Import syntax ident record.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.
Import ExceptNotations.

Local Open Scope except_scope.

Fixpoint dispatch_pattern (p : pattern) (v : val) (e : env) : iv_monad (option env) :=
  match p, v with
  | PAny, _ => pure (Some e)
  | PVar x, _ => pure (Some (ECons x v e))
  | PAlias p' x, _ => dispatch_pattern p' v (ECons x v e)
  | POr p1 p2, _ =>
      let* o := dispatch_pattern p1 v e in
      match o with
      | None => dispatch_pattern p2 v e
      | Some _ => pure o
      end
  | PTt, VTt => pure (Some e)
  | PInt z1, VInt z2 => pure (if (z1 =? z2)%Z then Some e else None)
  | PFloat q1, VFloat q2 => pure (if (q1 =? q2)%Qc then Some e else None)
  | PTrue, VTrue => pure (Some e)
  | PTrue, VFalse => pure None
  | PFalse, VTrue => pure None
  | PFalse, VFalse => pure (Some e)
  | PChar a1, VChar a2 => pure (if (a1 =? a2)%char then Some e else None)
  | PString s1, VString s2 => pure (if (s1 =? s2)%string then Some e else None)
  | PPair p1 p2, VPair v1 v2 =>
      let* o := dispatch_pattern p1 v1 e in
      match o with
      | None => pure None
      | Some e => dispatch_pattern p2 v2 e
      end
  | PTuple p', VTuple t => dispatch_tuple_pattern p' t e
  | PRecord p', VRecord r => dispatch_record_pattern p' r e
  | PInl p', VInl v' => dispatch_pattern p' v' e
  | PInl _, VInr _ => pure None
  | PInr _, VInl _ => pure None
  | PInr p', VInr v' => dispatch_pattern p' v' e
  | PVariant l1 p', VVariant l2 v' => if ident_eqb l1 l2 then dispatch_pattern p' v' e else pure None
  | _, _ => throw (Type_error "dispatch_pattern")
  end
with dispatch_tuple_pattern (p : tuple_pattern) (t : tuple) (e : env) : iv_monad (option env) :=
  match p, t with
  | PTupleNil, TupleNil => pure (Some e)
  | PTupleCons p1 p2, TupleCons v t' =>
      let* o := dispatch_pattern p1 v e in
      match o with
      | None => pure None
      | Some e => dispatch_tuple_pattern p2 t' e
      end
  | _, _ => throw (Match_failure "dispatch_tuple_pattern")
  end
with dispatch_record_pattern (p : record_pattern) (r : record) (e : env) : iv_monad (option env) :=
  match p with
  | PRecordNil =>
      match r with
      | RecordNil => pure (Some e)
      | RecordCons _ _ _ => throw (Match_failure "dispatch_record_pattern")
      end
  | PRecordAny => pure (Some e)
  | PRecordRest x => pure (Some (ECons x (VRecord r) e))
  | PRecordCons0 l p' =>
      let (o, r') := record_lookup_remove l r in
      match o with
      | None => throw (Match_failure "dispatch_record_pattern")
      | Some v => dispatch_record_pattern p' r' (ECons l v e)
      end
  | PRecordCons1 l p1 p2 =>
      let (o, r') := record_lookup_remove l r in
      match o with
      | None => throw (Match_failure "dispatch_record_pattern")
      | Some v =>
          let* o := dispatch_pattern p1 v e in
          match o with
          | None => pure None
          | Some e => dispatch_record_pattern p2 r' e
          end
      end
  end.
