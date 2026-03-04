From shift_reset.core Require Import syntax ident.

Fixpoint record_lookup (l : ident) (r : record) : option val :=
  match r with
  | RecordNil => None
  | RecordCons l' v r' => if ident_eqb l l' then Some v else record_lookup l r'
  end.

Fixpoint record_lookup_remove (l : ident) (r : record) : option val * record :=
  match r with
  | RecordNil => (None, r)
  | RecordCons l' v r' =>
      if ident_eqb l l' then (Some v, r')
      else let (o, r') := record_lookup_remove l r' in (o, RecordCons l' v r')
  end.
