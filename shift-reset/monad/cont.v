Record cont (R A : Type) : Type := Cont { run_cont : (A -> R) -> R }.
Definition t : Type -> Type -> Type := cont.

Arguments Cont {R A} _.
Arguments run_cont {R A} _ _.

Definition pure {R A} (x : A) : cont R A :=
  Cont (fun k => k x).

Definition map {R A B} (f : A -> B) (m : cont R A) : cont R B :=
  Cont (fun k => run_cont m (fun x => k (f x))).

Definition mapl {R A B} (x : B) (m : cont R A) : cont R B :=
  Cont (fun k => run_cont m (fun _ => k x)).

Definition app {R A B} (m1 : cont R (A -> B)) (m2 : cont R A) : cont R B :=
  Cont (fun k => run_cont m1 (fun f => run_cont m2 (fun x => k (f x)))).

Definition appl {R A B} (m1 : cont R A) (m2 : cont R B) : cont R A :=
  Cont (fun k => run_cont m1 (fun x => run_cont m2 (fun _ => k x))).

Definition appr {R A B} (m1 : cont R A) (m2 : cont R B) : cont R B :=
  Cont (fun k => run_cont m1 (fun _ => run_cont m2 k)).

Definition bind {R A B} (m : cont R A) (f : A -> cont R B) : cont R B :=
  Cont (fun k => run_cont m (fun x => run_cont (f x) k)).

Definition join {R A} (m : cont R (cont R A)) : cont R A :=
  Cont (fun k => run_cont m (fun m => run_cont m k)).

Definition callcc {R A B} (f : (A -> cont R B) -> cont R A) : cont R A :=
  Cont (fun k => run_cont (f (fun x => Cont (fun _ => k x))) k).

Definition reset {R R'} (m : cont R R) : cont R' R :=
  Cont (fun k => k (run_cont m (fun x => x))).

Definition shift {R R' A} (f : (A -> cont R' R) -> cont R R) : cont R A :=
  Cont (fun k => run_cont (f (fun x => Cont (fun k' => k' (k x)))) (fun x => x)).

Definition map_cont {R A} (f : R -> R) (m : cont R A) : cont R A :=
  Cont (fun k => run_cont m (fun x => f (k x))).

Definition with_cont {R A B} (f : (B -> R) -> A -> R) (m : cont R A) : cont R B :=
  Cont (fun k => run_cont m (f k)).

Module ContNotations.
  Declare Scope cont_scope.
  Delimit Scope cont_scope with cont.
  Bind Scope cont_scope with cont.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : cont_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : cont_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : cont_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : cont_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : cont_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : cont_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : cont_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : cont_scope.
End ContNotations.
