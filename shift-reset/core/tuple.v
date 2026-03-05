From shift_reset.core Require Import syntax.

Fixpoint tuple_length (t : tuple) : nat :=
  match t with
  | TupleNil => O
  | TupleCons _ t' => S (tuple_length t')
  end.

Fixpoint tuple_get (n : nat) (t : tuple) : option val :=
  match t with
  | TupleNil => None
  | TupleCons v t' =>
      match n with
      | O => Some v
      | S n' => tuple_get n' t'
      end
  end.
