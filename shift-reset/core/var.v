From Stdlib Require Import String.

Record var : Type := Var { var_car : string }.

Definition var_eq_dec : forall (v1 v2 : var), {v1 = v2} + {v1 <> v2}.
Proof. decide equality; auto using string_dec. Defined.
