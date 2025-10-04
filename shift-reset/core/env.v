From shift_reset.core Require Import var syntax.

Fixpoint env_lookup (x : var) (env : env) : option val :=
  match env with
  | ENil => None
  | ECons x' v env' => if var_eq_dec x x' then Some v else env_lookup x env'
  end.
