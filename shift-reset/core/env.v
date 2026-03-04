From shift_reset.core Require Import syntax ident.

Fixpoint env_lookup (x : ident) (e : env) : option val :=
  match e with
  | ENil => None
  | ECons x' v e' => if ident_eqb x x' then Some v else env_lookup x e'
  end.
