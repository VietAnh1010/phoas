Module Type Semigroup.
  Parameter t : Type.
  Parameter combine : t -> t -> t.
End Semigroup.

Module Type Monoid.
  Include Semigroup.
  Parameter empty : t.
End Monoid.

Module Type Functor.
  Parameter t : Type -> Type.
  Parameter map : forall {A B}, (A -> B) -> t A -> t B.
End Functor.

Module Type Applicative.
  Include Functor.
  Parameter pure : forall {A}, A -> t A.
  Parameter apply : forall {A B}, t (A -> B) -> t A -> t B.
End Applicative.

Module Type Alternative.
  Include Applicative.
  Parameter empty : forall {A}, A -> t A.
  Parameter combine : forall {A}, t A -> t A -> t A.
End Alternative.

Module Type Monad.
  Include Applicative.
  Parameter bind : forall {A B}, t A -> (A -> t B) -> t B.
End Monad.

Module Type MonadReader.
  Include Monad.
  Parameter r : Type.
  Parameter ask : t r.
  Parameter reader : forall {A}, (r -> A) -> t A.
  Parameter local : forall {A}, (r -> r) -> t A -> t A.
End MonadReader.

Module Type MonadWriter.
  Include Monad.
  Parameter w : Type.
  Parameter tell : w -> t unit.
  Parameter writer : forall {A}, A * w -> t A.
  Parameter listen : forall {A}, t A -> t (A * w).
  Parameter pass : forall {A}, t (A * (w -> w)) -> t A.
End MonadWriter.

Module Type MonadState.
  Include Monad.
  Parameter s : Type.
  Parameter get : t s.
  Parameter put : s -> t unit.
  Parameter state : forall {A}, (s -> A * s) -> t A.
End MonadState.

Module Type MonadExcept.
  Include Monad.
  Parameter e : Type.
  Parameter throw : forall {A}, e -> t A.
  Parameter except : forall {A}, e + A -> t A.
  Parameter catch : forall {A}, t A -> (e -> t A) -> t A.
End MonadExcept.

Module Type MonadCont.
  Include Monad.
  Parameter callcc : forall {A B}, ((A -> t B) -> t A) -> t A.
End MonadCont.

Module Type MonadSelect.
  Include Monad.
  Parameter r : Type.
  Parameter select : forall {A}, ((A -> r) -> A) -> t A.
End MonadSelect.

Module Type MonadAccum.
  Include Monad.
  Parameter w : Type.
  Parameter look : t w.
  Parameter add : w -> t unit.
  Parameter accum : forall {A}, (w -> A * w) -> t A.
End MonadAccum.
