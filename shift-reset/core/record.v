From shift_reset.core Require Import syntax tag.

Fixpoint record_lookup (tag : tag) (r : record) : option val :=
  match r with
  | RecordNil => None
  | RecordCons tag' v r' => if tag_eqb tag tag' then Some v else record_lookup tag r'
  end.
