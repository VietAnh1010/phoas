From shift_reset.core Require Import syntax ident.

Definition record_singleton (l : ident) (v : val) : record :=
  RecordCons l v RecordNil.

Fixpoint record_cardinal (r : record) : nat :=
  match r with
  | RecordNil => O
  | RecordCons _ _ r' => S (record_cardinal r')
  end.

Fixpoint record_add (l : ident) (v : val) (r : record) : record :=
  match r with
  | RecordNil => record_singleton l v
  | RecordCons l' v' r' =>
      match ident_compare l l' with
      | Lt => RecordCons l v r
      | Eq => RecordCons l v r'
      | Gt => RecordCons l' v' (record_add l v r')
      end
  end.

Fixpoint record_find (l : ident) (r : record) : option val :=
  match r with
  | RecordNil => None
  | RecordCons l' v r' =>
      match ident_compare l l' with
      | Lt => None
      | Eq => Some v
      | Gt => record_find l r'
      end
  end.

Fixpoint record_member (l : ident) (r : record) : bool :=
  match r with
  | RecordNil => false
  | RecordCons l' _ r' =>
      match ident_compare l l' with
      | Lt => false
      | Eq => true
      | Gt => record_member l r'
      end
  end.

Fixpoint record_remove (l : ident) (r : record) : record :=
  match r with
  | RecordNil => RecordNil
  | RecordCons l' v r' =>
      match ident_compare l l' with
      | Lt => r
      | Eq => r'
      | Gt => RecordCons l' v (record_remove l r')
      end
  end.
