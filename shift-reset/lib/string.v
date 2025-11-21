From Stdlib Require Import String.

Local Open Scope string_scope.

Definition string_gtb (s1 s2 : string) : bool := s2 <? s1.
Definition string_geb (s1 s2 : string) : bool := s2 <=? s1.
Definition string_neqb (s1 s2 : string) : bool := negb (s1 =? s2).
