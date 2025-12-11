Local Open Scope type_scope.

(** class Functor m where *)

Class MonadMap (M : Type -> Type) : Type :=
  monad_map : forall {A B}, (A -> B) -> M A -> M B.

Class MonadReplace (M : Type -> Type) : Type :=
  monad_replace : forall {A B}, B -> M A -> M B.

(** class Functor m => Applicative m where *)

Class MonadPure (M : Type -> Type) : Type :=
  monad_pure : forall {A}, A -> M A.

Class MonadApp (M : Type -> Type) : Type :=
  monad_app : forall {A B}, M (A -> B) -> M A -> M B.

(** class Applicative m => Monad m where *)

Class MonadBind (M : Type -> Type) : Type :=
  monad_bind : forall {A B}, M A -> (A -> M B) -> M B.

Class MonadThen (M : Type -> Type) : Type :=
  monad_then : forall {A B}, M A -> M B -> M B.

Class MonadJoin (M : Type -> Type) : Type :=
  monad_join : forall {A}, M (M A) -> M A.

(** class Monad m => MonadReader r m where *)

Class MonadAsk (R : Type) (M : Type -> Type) : Type :=
  monad_ask : M R.

Class MonadLocal (R : Type) (M : Type -> Type) : Type :=
  monad_local : forall {A}, (R -> R) -> M A -> M A.

Class MonadScope (R : Type) (M : Type -> Type) : Type :=
  monad_scope : forall {A}, R -> M A -> M A.

Class MonadReader (R : Type) (M : Type -> Type) : Type :=
  monad_reader : forall {A}, (R -> A) -> M A.

(** class Monad m => MonadExcept e m where *)

Class MonadThrow (E : Type) (M : Type -> Type) : Type :=
  monad_throw : forall {A}, E -> M A.

Class MonadCatch (E : Type) (M : Type -> Type) : Type :=
  monad_catch : forall {A}, M A -> (E -> M A) -> M A.

Class MonadExcept (E : Type) (M : Type -> Type) : Type :=
  monad_except : forall {A}, E + A -> M A.

(** class Monad m => MonadState s m where *)

Class MonadGet (S : Type) (M : Type -> Type) : Type :=
  monad_get : M S.

Class MonadPut (S : Type) (M : Type -> Type) : Type :=
  monad_put : S -> M unit.

Class MonadModify (S : Type) (M : Type -> Type) : Type :=
  monad_modify : (S -> S) -> M unit.

Class MonadState (S : Type) (M : Type -> Type) : Type :=
  monad_state : forall {A}, (S -> A * S) -> M A.

(** Derived functions, and notations *)

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Local Open Scope monad_scope.

Notation "f <$> m" := (monad_map f m) (at level 65, right associativity) : monad_scope.
Notation "x <$ m" := (monad_replace x m) (at level 65, right associativity) : monad_scope.
Notation "m1 <*> m2" := (monad_app m1 m2) (at level 55, left associativity) : monad_scope.
Notation "m >>= f" := (monad_bind m f) (at level 50, left associativity) : monad_scope.
Notation "m1 >> m2" := (monad_then m1 m2) (at level 50, left associativity) : monad_scope.

Notation "let+ x := m 'in' k" := (monad_map (fun x => k) m) (at level 100, x binder, right associativity) : monad_scope.
Notation "let* x := m 'in' k" := (monad_bind m (fun x => k)) (at level 100, x binder, right associativity) : monad_scope.
