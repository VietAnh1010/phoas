Record sc_monad (S R A : Type) : Type := SCMonad { run_sc_monad : S -> (A -> S -> R) -> R }.
Definition t : Type -> Type -> Type -> Type := sc_monad.

Arguments SCMonad {S R A} _.
Arguments run_sc_monad {S R A} _ _ _.

Definition pure {S R A} (x : A) : sc_monad S R A :=
  SCMonad (fun s k => k x s).

Definition map {S R A B} (f : A -> B) (m : sc_monad S R A) : sc_monad S R B :=
  SCMonad (fun s k => run_sc_monad m s (fun x => k (f x))).

Definition mapl {S R A B} (x : B) (m : sc_monad S R A) : sc_monad S R B :=
  SCMonad (fun s k => run_sc_monad m s (fun _ => k x)).

Definition app {S R A B} (m1 : sc_monad S R (A -> B)) (m2 : sc_monad S R A) : sc_monad S R B :=
  SCMonad (fun s k => run_sc_monad m1 s (fun f s => run_sc_monad m2 s (fun x => k (f x)))).

Definition appl {S R A B} (m1 : sc_monad S R A) (m2 : sc_monad S R B) : sc_monad S R A :=
  SCMonad (fun s k => run_sc_monad m1 s (fun x s => run_sc_monad m2 s (fun _ => k x))).

Definition appr {S R A B} (m1 : sc_monad S R A) (m2 : sc_monad S R B) : sc_monad S R B :=
  SCMonad (fun s k => run_sc_monad m1 s (fun _ s => run_sc_monad m2 s k)).

Definition bind {S R A B} (m : sc_monad S R A) (f : A -> sc_monad S R B) : sc_monad S R B :=
  SCMonad (fun s k => run_sc_monad m s (fun x s => run_sc_monad (f x) s k)).

Definition join {S R A} (m : sc_monad S R (sc_monad S R A)) : sc_monad S R A :=
  SCMonad (fun s k => run_sc_monad m s (fun m s => run_sc_monad m s k)).

Definition get {S R} : sc_monad S R S :=
  SCMonad (fun s k => k s s).

Definition put {S R} (s : S) : sc_monad S R unit :=
  SCMonad (fun _ k => k tt s).

Definition state {S R A} (f : S -> A * S) : sc_monad S R A :=
  SCMonad (fun s k => let (x, s) := f s in k x s).

Definition gets {S R A} (f : S -> A) : sc_monad S R A :=
  SCMonad (fun s k => k (f s) s).

Definition modify {S R} (f : S -> S) : sc_monad S R unit :=
  SCMonad (fun s k => k tt (f s)).

Definition cont {S R A} (f : (A -> R) -> R) : sc_monad S R A :=
  SCMonad (fun s k => f (fun x => k x s)).

Definition callcc {S R A B} (f : (A -> sc_monad S R B) -> sc_monad S R A) : sc_monad S R A :=
  SCMonad (fun s k => run_sc_monad (f (fun x => SCMonad (fun _ _ => k x s))) s k).

Definition callcc' {S R A B} (f : (A -> sc_monad S R B) -> sc_monad S R A) : sc_monad S R A :=
  SCMonad (fun s k => run_sc_monad (f (fun x => SCMonad (fun s _ => k x s))) s k).

Definition map_state {S R A B} (f : A * S -> B * S) (m : sc_monad S R A) : sc_monad S R B :=
  SCMonad (fun s k => run_sc_monad m s (fun x s => let (y, s) := f (x, s) in k y s)).

Definition with_state {S R A} (f : S -> S) (m : sc_monad S R A) : sc_monad S R A :=
  SCMonad (fun s => run_sc_monad m (f s)).

Definition map_cont {S R A} (f : R -> R) (m : sc_monad S R A) : sc_monad S R A :=
  SCMonad (fun s k => f (run_sc_monad m s k)).

Definition with_cont {S R A B} (f : (B -> R) -> A -> R) (m : sc_monad S R A) : sc_monad S R B :=
  SCMonad (fun s k => run_sc_monad m s (fun x s => f (fun y => k y s) x)).

Module SCMonadNotations.
  Declare Scope sc_monad_scope.
  Delimit Scope sc_monad_scope with sc_monad.
  Bind Scope sc_monad_scope with sc_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : sc_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : sc_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : sc_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : sc_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : sc_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : sc_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : sc_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : sc_monad_scope.
End SCMonadNotations.
