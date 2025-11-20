From Stdlib Require Import Ascii.

Local Open Scope char_scope.

Definition ascii_gtb (a1 a2 : ascii) : bool := a2 <? a1.
Definition ascii_geb (a1 a2 : ascii) : bool := a2 <=? a1.
Definition ascii_neqb (a1 a2 : ascii) : bool := negb (a1 =? a2).
