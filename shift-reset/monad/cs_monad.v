Record cs_monad (R S A : Type) : Type := CSMonad { run_cs_monad : (A -> S -> R * S) -> S -> R * S }.
Definition t : Type -> Type -> Type -> Type := cs_monad.

Arguments CSMonad {R S A} _.
Arguments run_cs_monad {R S A} _ _ _.

Definition pure {R S A} (x : A) : cs_monad R S A :=
  CSMonad (fun k => k x).

Definition map {R S A B} (f : A -> B) (m : cs_monad R S A) : cs_monad R S B :=
  CSMonad (fun k => run_cs_monad m (fun x => k (f x))).

Definition mapl {R S A B} (x : B) (m : cs_monad R S A) : cs_monad R S B :=
  CSMonad (fun k => run_cs_monad m (fun _ => k x)).

Definition app {R S A B} (m1 : cs_monad R S (A -> B)) (m2 : cs_monad R S A) : cs_monad R S B :=
  CSMonad (fun k => run_cs_monad m1 (fun f => run_cs_monad m2 (fun x => k (f x)))).

Definition appl {R S A B} (m1 : cs_monad R S A) (m2 : cs_monad R S B) : cs_monad R S A :=
  CSMonad (fun k => run_cs_monad m1 (fun x => run_cs_monad m2 (fun _ => k x))).

Definition appr {R S A B} (m1 : cs_monad R S A) (m2 : cs_monad R S B) : cs_monad R S B :=
  CSMonad (fun k => run_cs_monad m1 (fun _ => run_cs_monad m2 k)).

Definition bind {R S A B} (m : cs_monad R S A) (f : A -> cs_monad R S B) : cs_monad R S B :=
  CSMonad (fun k => run_cs_monad m (fun x => run_cs_monad (f x) k)).

Definition join {R S A} (m : cs_monad R S (cs_monad R S A)) : cs_monad R S A :=
  CSMonad (fun k => run_cs_monad m (fun m => run_cs_monad m k)).

Definition callcc {R S A B} (f : (A -> cs_monad R S B) -> cs_monad R S A) : cs_monad R S A :=
  CSMonad (fun k => run_cs_monad (f (fun x => CSMonad (fun _ => k x))) k).

Definition reset {R R' S} (m : cs_monad R S R) : cs_monad R' S R :=
  CSMonad (fun k s => let (x, s) := run_cs_monad m pair s in k x s).

Definition shift {R R' S A} (f : (A -> cs_monad R' S R) -> cs_monad R S R) : cs_monad R S A :=
  CSMonad (fun k s => run_cs_monad (f (fun x => CSMonad (fun k' s => let (y, s) := k x s in k' y s))) pair s).

Definition get {R S} : cs_monad R S S :=
  CSMonad (fun k s => k s s).

Definition put {R S} (s : S) : cs_monad R S unit :=
  CSMonad (fun k _ => k tt s).

Definition state {R S A} (f : S -> A * S) : cs_monad R S A :=
  CSMonad (fun k s => let (x, s) := f s in k x s).

Definition gets {R S A} (f : S -> A) : cs_monad R S A :=
  CSMonad (fun k s => k (f s) s).

Definition modify {R S} (f : S -> S) : cs_monad R S unit :=
  CSMonad (fun k s => k tt (f s)).

Definition map_cont {R S A} (f : R -> R) (m : cs_monad R S A) : cs_monad R S A :=
  CSMonad (fun k s => let (x, s) := run_cs_monad m k s in (f x, s)).

Definition map_state {R S A B} (f : A * S -> B * S) (m : cs_monad R S A) : cs_monad R S B :=
  CSMonad (fun k s => run_cs_monad m (fun x s => let (y, s) := f (x, s) in k y s) s).

Definition with_state {R S A} (f : S -> S) (m : cs_monad R S A) : cs_monad R S A :=
  CSMonad (fun k s => run_cs_monad m k (f s)).

Module CSMonadNotations.
  Declare Scope cs_monad_scope.
  Delimit Scope cs_monad_scope with cs_monad.
  Bind Scope cs_monad_scope with cs_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : cs_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : cs_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : cs_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : cs_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : cs_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : cs_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : cs_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : cs_monad_scope.
End CSMonadNotations.
