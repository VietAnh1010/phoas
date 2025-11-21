From Stdlib Require Import DecimalString String ZArith.
Import NilZero.

Local Open Scope Z_scope.

Definition Z_neqb (z1 z2 : Z) : bool := negb (z1 =? z2).
Definition Z_to_string (z : Z) : string := string_of_int (Z.to_int z).
