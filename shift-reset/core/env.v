From shift_reset.core Require Import var syntax.

Definition env_lookup (x : var) : env -> option val :=
  fix go env :=
    match env with
    | ENil => None
    | ECons x' v env' => if var_eq_dec x x' then Some v else go env'
    end.
