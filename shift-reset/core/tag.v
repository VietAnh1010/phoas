From Stdlib Require Import String.

Record tag : Type := Tag { tag_car : string }.

Definition tag_eq_dec : forall (tag1 tag2 : tag), {tag1 = tag2} + {tag1 <> tag2}.
Proof. decide equality; auto using string_dec. Defined.
