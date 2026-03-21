From shift_reset.lib Require Import signatures.

Module Type SemigroupLaws (M : Semigroup).
  Import M.
  Parameter append_assoc : forall (x y z : t), append (append x y) z = append x (append y z).
End SemigroupLaws.

Module Type MonoidLaws (M : Monoid).
  Import M.
  Include SemigroupLaws M.
  Parameter append_empty_l : forall (x : t), append empty x = x.
  Parameter append_empty_r : forall (x : t), append x empty = x.
End MonoidLaws.
