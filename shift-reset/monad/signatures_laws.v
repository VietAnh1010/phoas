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

Module Type FunctorLaws (F : Functor).
  Import F.
  Parameter map_id : forall {A} (m : t A), map (fun x => x) m = m.
  Parameter map_comp : forall {A B C} (f : B -> C) (g : A -> B) (m : t A), map (fun x => f (g x)) m = map f (map g m).
End FunctorLaws.

Module Type ApplicativeLaws (F : Applicative).
  Import F.
  Include FunctorLaws F.
  Parameter apply_pure_l : forall {A B} (f : A -> B) (m : t A), apply (pure f) m = map f m.
  Parameter apply_pure_r : forall {A B} (m : t (A -> B)) (x : A), apply m (pure x) = map (fun g => g x) m.
  Parameter apply_assoc :
    forall {A B C}
           (m1 : t (B -> C))
           (m2 : t (A -> B))
           (m3 : t A),
      apply m1 (apply m2 m3) = apply (apply (map (fun f g x => f (g x)) m1) m2) m3.
End ApplicativeLaws.

Module Type MonadLaws (M : Monad).
  Import M.
  Include ApplicativeLaws M.
  Parameter bind_pure_l : forall {A B} (x : A) (f : A -> t B), bind (pure x) f = f x.
  Parameter bind_pure_r : forall {A} (m : t A), bind m pure = m.
  Parameter bind_assoc : forall {A B C} (m : t A) (f : A -> t B) (g : B -> t C), bind (bind m f) g = bind m (fun x => bind (f x) g).
End MonadLaws.
