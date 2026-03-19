From shift_reset.core Require Import syntax ident.

Fixpoint record_cardinal (r : record) : nat :=
  match r with
  | RecordNil => O
  | RecordCons _ _ r' => S (record_cardinal r')
  end.

Fixpoint record_find (l : ident) (r : record) : option val :=
  match r with
  | RecordNil => None
  | RecordCons l' v r' => if ident_eqb l l' then Some v else record_find l r'
  end.

Fixpoint record_find_remove (l : ident) (r : record) : option val * record :=
  match r with
  | RecordNil => (None, r)
  | RecordCons l' v r' =>
      if ident_eqb l l' then (Some v, r')
      else let (o, r') := record_find_remove l r' in (o, RecordCons l' v r')
  end.
