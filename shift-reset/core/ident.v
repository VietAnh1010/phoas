From Stdlib Require Import String.

Record ident : Type := Ident { ident_car : string }.

Definition ident_eq_dec : forall (x1 x2 : ident), {x1 = x2} + {x1 <> x2}.
Proof. decide equality; auto using string_dec. Defined.
