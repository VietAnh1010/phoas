From shift_reset.monad Require Import signatures.

Module Type SemigroupLaws (M : Semigroup).
  Import M.
  Parameter combine_assoc : forall (x y z : t), combine (combine x y) z = combine x (combine y z).
End SemigroupLaws.

Module Type MonoidLaws (M : Monoid).
  Import M.
  Include SemigroupLaws M.
  Parameter combine_empty_l : forall (x : t), combine empty x = x.
  Parameter combine_empty_r : forall (x : t), combine x empty = x.
End MonoidLaws.
