From shift_reset.core Require Import syntax.

Fixpoint tuple_length (t : tuple) : nat :=
  match t with
  | TupleNil => O
  | TupleCons _ t' => S (tuple_length t')
  end.
