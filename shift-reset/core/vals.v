From shift_reset.core Require Import syntax.

Fixpoint vals_length (vs : vals) : nat :=
  match vs with
  | VsNil => O
  | VsCons _ vs' => S (vals_length vs')
  end.

Fixpoint vals_get (n : nat) (vs : vals) : option val :=
  match vs with
  | VsNil => None
  | VsCons v vs' =>
      match n with
      | O => Some v
      | S n' => vals_get n' vs'
      end
  end.
