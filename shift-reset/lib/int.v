From Stdlib Require Import ZArith.

Definition Z_neqb (z1 z2 : Z) : bool := negb (Z.eqb z1 z2).
