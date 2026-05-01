Record reader (R A : Type) : Type := Reader { run_reader : R -> A }.
Definition t : Type -> Type -> Type := reader.

Arguments Reader {R A} _.
Arguments run_reader {R A} _ _.

Definition pure {R A} (x : A) : reader R A :=
  Reader (fun _ => x).

Definition map {R A B} (f : A -> B) (m : reader R A) : reader R B :=
  Reader (fun r => f (run_reader m r)).

Definition map_const {R A B} (x : B) (_ : reader R A) : reader R B :=
  Reader (fun _ => x).

Definition apply {R A B} (m1 : reader R (A -> B)) (m2 : reader R A) : reader R B :=
  Reader (fun r => run_reader m1 r (run_reader m2 r)).

Definition seq_left {R A B} (m : reader R A) (_ : reader R B) : reader R A := m.
Definition seq_right {R A B} (_ : reader R A) (m : reader R B) : reader R B := m.

Definition bind {R A B} (m : reader R A) (f : A -> reader R B) : reader R B :=
  Reader (fun r => run_reader (f (run_reader m r)) r).

Definition join {R A} (m : reader R (reader R A)) : reader R A :=
  Reader (fun r => run_reader (run_reader m r) r).

Definition ask {R} : reader R R :=
  Reader (fun r => r).

Definition local {R A} (f : R -> R) (m : reader R A) : reader R A :=
  Reader (fun r => run_reader m (f r)).

Definition with_reader {R' R A} (f : R' -> R) (m : reader R A) : reader R' A :=
  Reader (fun r => run_reader m (f r)).

Module ReaderNotations.
  Declare Scope reader_scope.
  Delimit Scope reader_scope with reader.
  Bind Scope reader_scope with reader.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : reader_scope.
  Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : reader_scope.
  Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : reader_scope.
  Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : reader_scope.
  Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : reader_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : reader_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : reader_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : reader_scope.
End ReaderNotations.
