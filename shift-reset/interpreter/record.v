From Stdlib Require Import String.
From shift_reset.core Require Import syntax ident record.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.
Import ExceptNotations.

Local Open Scope except_scope.

Fixpoint add_field (l : ident) (v : val) (r : record) : iv_monad record :=
  match r with
  | RecordNil => pure (record_singleton l v)
  | RecordCons l' v' r' =>
      match ident_compare l l' with
      | Lt => pure (RecordCons l v r)
      | Eq => throw (Invalid_argument "duplicate label" (VString (ident_car l)))
      | Gt => RecordCons l' v' <$> add_field l v r'
      end
  end.

Fixpoint extend_record (r1 : record) : record -> iv_monad record :=
  match r1 with
  | RecordNil => pure
  | RecordCons l1 v1 r1' =>
      fix go r2 :=
        match r2 with
        | RecordNil => pure r1
        | RecordCons l2 v2 r2' =>
            match ident_compare l1 l2 with
            | Lt => RecordCons l1 v1 <$> extend_record r1' r2
            | Eq => throw (Invalid_argument "duplicate label" (VString (ident_car l2)))
            | Gt => RecordCons l2 v2 <$> go r2'
            end
        end
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
