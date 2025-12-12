Record select (R A : Type) : Type := Select { run_select : (A -> R) -> A }.
Definition t : Type -> Type -> Type := select.

Arguments Select {R A} _.
Arguments run_select {R A} _ _.

Definition pure {R A} (x : A) : select R A :=
  Select (fun _ => x).

Definition map {R A B} (f : A -> B) (m : select R A) : select R B :=
  Select (fun k => f (run_select m (fun x => k (f x)))).

Definition mapl {R A B} (x : B) (_ : select R A) : select R B :=
  Select (fun _ => x).

Definition app {R A B} (m1 : select R (A -> B)) (m2 : select R A) : select R B :=
  Select (fun k => let f := run_select m1 (fun f => k (f (run_select m2 (fun x => k (f x))))) in f (run_select m2 (fun x => k (f x)))).

Definition appl {R A B} (m : select R A) (_ : select R B) : select R A := m.
Definition appr {R A B} (_ : select R A) (m : select R B) : select R B := m.

Definition bind {R A B} (m : select R A) (f : A -> select R B) : select R B :=
  Select (fun k => run_select (f (run_select m (fun x => k (run_select (f x) k)))) k).

Definition join {R A} (m : select R (select R A)) : select R A :=
  Select (fun k => run_select (run_select m (fun m => k (run_select m k))) k).

Definition map_select {R A} (f : A -> A) (m : select R A) : select R A :=
  Select (fun k => f (run_select m k)).

Module SelectNotations.
  Declare Scope select_scope.
  Delimit Scope select_scope with select.
  Bind Scope select_scope with select.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : select_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : select_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : select_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : select_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : select_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : select_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : select_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : select_scope.
End SelectNotations.
