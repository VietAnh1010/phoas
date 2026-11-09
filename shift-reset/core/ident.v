From Stdlib Require Import String.

Record ident : Type := Ident { ident_car : string }.

Lemma ident_eq_dec : forall (x1 x2 : ident), {x1 = x2} + {x1 <> x2}.
Proof. decide equality; auto using string_dec. Defined.

Definition ident_eqb (x1 x2 : ident) : bool := eqb (ident_car x1) (ident_car x2).

Definition ident_compare (x1 x2 : ident) : comparison := String.compare (ident_car x1) (ident_car x2).
