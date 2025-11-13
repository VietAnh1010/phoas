From shift_reset.core Require Import syntax tag.

Fixpoint record_lookup (tag : tag) (r : record) : option val :=
  match r with
  | RecordNil => None
  | RecordCons tag' v r' => if tag_eqb tag tag' then Some v else record_lookup tag r'
  end.

Fixpoint record_lookup_remove (tag : tag) (r : record) : option val * record :=
  match r with
  | RecordNil => (None, r)
  | RecordCons tag' v r' =>
      if tag_eqb tag tag'
      then (Some v, r')
      else let (o, r') := record_lookup_remove tag r' in (o, RecordCons tag' v r')
  end.
