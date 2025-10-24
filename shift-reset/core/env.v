From shift_reset.core Require Import syntax var.

Fixpoint env_lookup (x : var) (env : env) : option val :=
  match env with
  | EnvNil => None
  | EnvCons x' v env' => if var_eqb x x' then Some v else env_lookup x env'
  end.
