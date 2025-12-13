From Stdlib Require Import String.

Record tag : Type := Tag { tag_car : string }.

Lemma tag_eq_dec : forall (l1 l2 : tag), {l1 = l2} + {l1 <> l2}.
Proof. decide equality; auto using string_dec. Defined.

Definition tag_eqb (l1 l2 : tag) : bool :=
  eqb (tag_car l1) (tag_car l2).

Definition tag_empty : tag := Tag "".
