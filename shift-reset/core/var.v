From Stdlib Require Import String.

Record var : Type := Var { var_car : string }.

Lemma var_eq_dec : forall (x1 x2 : var), {x1 = x2} + {x1 <> x2}.
Proof. decide equality; auto using string_dec. Defined.

Definition var_eqb (x1 x2 : var) : bool :=
  eqb (var_car x1) (var_car x2).
