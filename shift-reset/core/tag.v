From Stdlib Require Import String.

Record tag : Type := Tag { tag_car : string }.

Lemma tag_eq_dec : forall (tag1 tag2 : tag), {tag1 = tag2} + {tag1 <> tag2}.
Proof. decide equality; auto using string_dec. Defined.

Definition tag_eqb (tag1 tag2 : tag) : bool :=
  eqb (tag_car tag1) (tag_car tag2).

Definition tag_empty : tag := Tag EmptyString.
