From Stdlib Require Import ZArith.

Local Open Scope Z_scope.

Definition Z_neqb (z1 z2 : Z) : bool := negb (z1 =? z2).
