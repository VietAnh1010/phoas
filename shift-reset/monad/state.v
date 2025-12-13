Record state (S A : Type) : Type := State { run_state : S -> A * S }.
Definition t : Type -> Type -> Type := state.

Arguments State {S A} _.
Arguments run_state {S A} _ _.

Definition pure {S A} (x : A) : state S A :=
  State (fun s => (x, s)).

Definition map {S A B} (f : A -> B) (m : state S A) : state S B :=
  State (fun s => let (x, s) := run_state m s in (f x, s)).

Definition mapl {S A B} (x : B) (m : state S A) : state S B :=
  State (fun s => let (_, s) := run_state m s in (x, s)).

Definition app {S A B} (m1 : state S (A -> B)) (m2 : state S A) : state S B :=
  State (fun s => let (f, s) := run_state m1 s in let (x, s) := run_state m2 s in (f x, s)).

Definition appl {S A B} (m1 : state S A) (m2 : state S B) : state S A :=
  State (fun s => let (x, s) := run_state m1 s in let (_, s) := run_state m2 s in (x, s)).

Definition appr {S A B} (m1 : state S A) (m2 : state S B) : state S B :=
  State (fun s => let (_, s) := run_state m2 s in run_state m2 s).

Definition bind {S A B} (m : state S A) (f : A -> state S B) : state S B :=
  State (fun s => let (x, s) := run_state m s in run_state (f x) s).

Definition join {S A} (m : state S (state S A)) : state S A :=
  State (fun s => let (m, s) := run_state m s in run_state m s).

Definition get {S} : state S S :=
  State (fun s => (s, s)).

Definition put {S} (s : S) : state S unit :=
  State (fun _ => (tt, s)).

Definition gets {S A} (f : S -> A) : state S A :=
  State (fun s => (f s, s)).

Definition modify {S} (f : S -> S) : state S unit :=
  State (fun s => (tt, f s)).

Definition with_state {S A} (f : S -> S) (m : state S A) : state S A :=
  State (fun s => run_state m (f s)).

Definition map_state {S A B} (f : A * S -> B * S) (m : state S A) : state S B :=
  State (fun s => f (run_state m s)).

Module StateNotations.
  Declare Scope state_scope.
  Delimit Scope state_scope with state.
  Bind Scope state_scope with state.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : state_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : state_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : state_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : state_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : state_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : state_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : state_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : state_scope.
End StateNotations.
