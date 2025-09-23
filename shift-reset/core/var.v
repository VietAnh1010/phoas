From Stdlib Require Import String.

Record var : Type := Var { var_car : string }.

Definition var_eq_dec : forall (x1 x2 : var), {x1 = x2} + {x1 <> x2}.
Proof. decide equality; auto using string_dec. Defined.
