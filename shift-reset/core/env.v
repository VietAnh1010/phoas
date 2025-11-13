From shift_reset.core Require Import syntax var.

Fixpoint env_lookup (x : var) (e : env) : option val :=
  match e with
  | ENil => None
  | ECons x' v e' => if var_eqb x x' then Some v else env_lookup x e'
  end.
