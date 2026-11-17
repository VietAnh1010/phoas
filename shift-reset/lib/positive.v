From Stdlib Require Import PArith.

Local Open Scope positive_scope.

Fixpoint reverse_append (p1 p2 : positive) : positive :=
  match p1 with
  | 1 => p2
  | p1~0 => reverse_append p1 p2~0
  | p1~1 => reverse_append p1 p2~1
  end.

Definition reverse (p : positive) : positive :=
  reverse_append p 1.
