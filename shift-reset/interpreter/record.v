From Stdlib Require Import String.
From shift_reset.core Require Import syntax ident record.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.
Import ExceptNotations.

Local Open Scope except_scope.

Definition add_field (l : ident) (v : val) (r : record) : iv_monad record :=
  if record_member l r
  then throw (Invalid_argument "duplicate label" (VString (ident_car l)))
  else pure (record_add l v r).

Fixpoint disjoint_union_record (r1 r2 : record) : iv_monad record :=
  match r1 with
  | RecordNil => pure r2
  | RecordCons l1 v1 r1' =>
      let fix go r2 :=
        match r2 with
        | RecordNil => pure r1
        | RecordCons l2 v2 r2' =>
            match ident_compare l1 l2 with
            | Lt => RecordCons l1 v1 <$> disjoint_union_record r1' r2
            | Eq => throw (Invalid_argument "duplicate label" (VString (ident_car l1)))
            | Gt => RecordCons l2 v2 <$> go r2'
            end
        end
      in go r2
  end.

Fixpoint update_record (r1 r2 : record) : iv_monad record :=
  match r1, r2 with
  | _, RecordNil => pure r1
  | RecordNil, RecordCons l _ _ => throw (Name_error (ident_car l))
  | RecordCons l1 v1 r1', RecordCons l2 v2 r2' =>
      match ident_compare l1 l2 with
      | Lt => RecordCons l1 v1 <$> update_record r1' r2
      | Eq => RecordCons l2 v2 <$> update_record r1' r2'
      | Gt => throw (Name_error (ident_car l2))
      end
  end.
