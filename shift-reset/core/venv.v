From shift_reset.core Require Import var syntax.

Definition venv_lookup (x : var) : venv -> option val :=
  fix go ve :=
    match ve with
    | VENil => None
    | VECons x' v ve' => if var_eq_dec x x' then Some v else go ve'
    end.
