From shift_reset.core Require Import ident syntax.

Fixpoint env_lookup (x : ident) (env : env) : option val :=
  match env with
  | EnvNil => None
  | EnvCons x' v env' => if ident_eq_dec x x' then Some v else env_lookup x env'
  end.
