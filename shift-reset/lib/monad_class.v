Local Open Scope type_scope.

(** class Functor m where *)

Class Map (M : Type -> Type) : Type :=
  map : forall {A B}, (A -> B) -> M A -> M B.

Class Mapl (M : Type -> Type) : Type :=
  mapl : forall {A B}, B -> M A -> M B.

(** class Functor m => Applicative m where *)

Class Pure (M : Type -> Type) : Type :=
  pure : forall {A}, A -> M A.

Class App (M : Type -> Type) : Type :=
  app : forall {A B}, M (A -> B) -> M A -> M B.

Class Appl (M : Type -> Type) : Type :=
  appl : forall {A B}, M A -> M B -> M A.

Class Appr (M : Type -> Type) : Type :=
  appr : forall {A B}, M A -> M B -> M B.

(** class Applicative m => Monad m where *)

Class Bind (M : Type -> Type) : Type :=
  bind : forall {A B}, M A -> (A -> M B) -> M B.

Class Join (M : Type -> Type) : Type :=
  join : forall {A}, M (M A) -> M A.

(** class Monad m => MonadReader r m where *)

Class Ask (R : Type) (M : Type -> Type) : Type :=
  ask : M R.

Class Local (R : Type) (M : Type -> Type) : Type :=
  local : forall {A}, (R -> R) -> M A -> M A.

Class Reader (R : Type) (M : Type -> Type) : Type :=
  reader : forall {A}, (R -> A) -> M A.

(** class Monad m => MonadExcept e m where *)

Class Throw (E : Type) (M : Type -> Type) : Type :=
  throw : forall {A}, E -> M A.

Class Catch (E : Type) (M : Type -> Type) : Type :=
  catch : forall {A}, M A -> (E -> M A) -> M A.

Class Except (E : Type) (M : Type -> Type) : Type :=
  except : forall {A}, E + A -> M A.

(** class Monad m => MonadState s m where *)

Class Get (S : Type) (M : Type -> Type) : Type :=
  get : M S.

Class Put (S : Type) (M : Type -> Type) : Type :=
  put : S -> M unit.

Class State (S : Type) (M : Type -> Type) : Type :=
  state : forall {A}, (S -> A * S) -> M A.

(** class (Monoid w, Monad m) => MonadWriter w m where *)

Class Tell (W : Type) (M : Type -> Type) : Type :=
  tell : W -> M unit.

Class Listen (W : Type) (M : Type -> Type) : Type :=
  listen : forall {A}, M A -> M (A * W).

Class Pass (W : Type) (M : Type -> Type) : Type :=
  pass : forall {A}, M (A * (W -> W)) -> M A.

Class Writer (W : Type) (M : Type -> Type) : Type :=
  writer : forall {A}, A * W -> M A.

(** Derived functions, and notations *)

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Local Open Scope monad_scope.

Notation "f <$> m" := (map f m) (at level 65, right associativity) : monad_scope.
Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : monad_scope.
Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m >>= f" := (bind m f) (at level 50, left associativity) : monad_scope.

Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : monad_scope.
Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : monad_scope.
