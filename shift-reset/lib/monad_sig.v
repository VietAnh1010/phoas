Module Type Monad.
  Parameter t : Type -> Type.
  Parameter pure : forall {A}, A -> t A.
  Parameter map : forall {A B}, (A -> B) -> t A -> t B.
  Parameter app : forall {A B}, t (A -> B) -> t A -> t B.
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
  Parameter writer : forall {A}, (A * w) -> t A.
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
