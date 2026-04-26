Local Open Scope type_scope.

(** class Functor f where *)

Class Map (F : Type -> Type) : Type :=
  map : forall {A B}, (A -> B) -> F A -> F B.

Class MapConst (F : Type -> Type) : Type :=
  map_const : forall {A B}, B -> F A -> F B.

(** class Functor f => Applicative f where *)

Class Pure (F : Type -> Type) : Type :=
  pure : forall {A}, A -> F A.

Class Apply (F : Type -> Type) : Type :=
  apply : forall {A B}, F (A -> B) -> F A -> F B.

Class SeqLeft (F : Type -> Type) : Type :=
  seq_left : forall {A B}, F A -> F B -> F A.

Class SeqRight (F : Type -> Type) : Type :=
  seq_right : forall {A B}, F A -> F B -> F B.

(** class Applicative f => Alternative f where *)

Class Empty (F : Type -> Type) : Type :=
  empty : forall {A}, A -> F A.

Class Combine (F : Type -> Type) : Type :=
  combine : forall {A}, F A -> F A -> F A.

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

(** class Monad m => MonadCont m where *)

Class CallCC (M : Type -> Type) : Type :=
  callcc : forall {A B}, ((A -> M B) -> M A) -> M A.

(** class Monad m => MonadSelect r m where *)

Class Select (R : Type) (M : Type -> Type) : Type :=
  select : forall {A}, ((A -> R) -> A) -> M A.

(** class (Monoid w, Monad m) => MonadAccum w m where *)

Class Look (W : Type) (M : Type -> Type) : Type :=
  look : M W.

Class Add (W : Type) (M : Type -> Type) : Type :=
  add : W -> M unit.

Class Accum (W : Type) (M : Type -> Type) : Type :=
  accum : forall {A}, (W -> A * W) -> M A.

(** Derived functions, and notations *)

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

Notation "f <$> m" := (map f m) (at level 65, right associativity) : monad_scope.
Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : monad_scope.
Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m1 <|> m2" := (combine m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m >>= f" := (bind m f) (at level 50, left associativity) : monad_scope.

Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : monad_scope.
Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : monad_scope.
