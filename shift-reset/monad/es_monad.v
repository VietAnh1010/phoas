Record es_monad (E S A : Type) : Type := ESMonad { run_es_monad : S -> (E + A) * S }.
Definition t : Type -> Type -> Type -> Type := es_monad.

Arguments ESMonad {E S A} _.
Arguments run_es_monad {E S A} _ _.

Definition pure {E S A} (x : A) : es_monad E S A :=
  ESMonad (fun s => (inr x, s)).

Definition map {E S A B} (f : A -> B) (m : es_monad E S A) : es_monad E S B :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl e, s)
       | inr x => (inr (f x), s)
       end).

Definition mapl {E S A B} (x : B) (m : es_monad E S A) : es_monad E S B :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl e, s)
       | inr _ => (inr x, s)
       end).

Definition app {E S A B} (m1 : es_monad E S (A -> B)) (m2 : es_monad E S A) : es_monad E S B :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m1 s in
       match m with
       | inl e => (inl e, s)
       | inr f =>
           let (m, s) := run_es_monad m2 s in
           match m with
           | inl e => (inl e, s)
           | inr x => (inr (f x), s)
           end
       end).

Definition appl {E S A B} (m1 : es_monad E S A) (m2 : es_monad E S B) : es_monad E S A :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m1 s in
       match m with
       | inl e => (inl e, s)
       | inr x =>
           let (m, s) := run_es_monad m2 s in
           match m with
           | inl e => (inl e, s)
           | inr _ => (inr x, s)
           end
       end).

Definition appr {E S A B} (m1 : es_monad E S A) (m2 : es_monad E S B) : es_monad E S B :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m1 s in
       match m with
       | inl e => (inl e, s)
       | inr _ => run_es_monad m2 s
       end).

Definition bind {E S A B} (m : es_monad E S A) (f : A -> es_monad E S B) : es_monad E S B :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl e, s)
       | inr x => run_es_monad (f x) s
       end).

Definition join {E S A} (m : es_monad E S (es_monad E S A)) : es_monad E S A :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl e, s)
       | inr m => run_es_monad m s
       end).

Definition throw {E S A} (e : E) : es_monad E S A :=
  ESMonad (fun s => (inl e, s)).

Definition except {E S A} (m : E + A) : es_monad E S A :=
  ESMonad (fun s => (m, s)).

Definition catch {E S A} (m : es_monad E S A) (f : E -> es_monad E S A) : es_monad E S A :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => run_es_monad (f e) s
       | inr x => (inr x, s)
       end).

Definition try {E S A} (m : es_monad E S A) : es_monad E S (E + A) :=
  ESMonad (fun s => let (m, s) := run_es_monad m s in (inr m, s)).

Definition finally {E S A} (m1 : es_monad E S A) (m2 : es_monad E S unit) : es_monad E S A :=
  ESMonad
    (fun s =>
       let (m1, s) := run_es_monad m1 s in
       let (m2, s) := run_es_monad m2 s in
       match m2 with
       | inl e => (inl e, s)
       | inr _ => (m1, s)
       end).

Definition get {E S} : es_monad E S S :=
  ESMonad (fun s => (inr s, s)).

Definition put {E S} (s : S) : es_monad E S unit :=
  ESMonad (fun _ => (inr tt, s)).

Definition state {E S A} (f : S -> A * S) : es_monad E S A :=
  ESMonad (fun s => let (x, s) := f s in (inr x, s)).

Definition gets {E S A} (f : S -> A) : es_monad E S A :=
  ESMonad (fun s => (inr (f s), s)).

Definition modify {E S} (f : S -> S) : es_monad E S unit :=
  ESMonad (fun s => (inr tt, f s)).

Definition map_state {E S A B} (f : A * S -> B * S) (m : es_monad E S A) : es_monad E S B :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl e, s)
       | inr x => let (y, s) := f (x, s) in (inr y, s)
       end).

Definition with_state {E S A} (f : S -> S) (m : es_monad E S A) : es_monad E S A :=
  ESMonad (fun s => run_es_monad m (f s)).

Definition map_except {E E' S A B} (f : E + A -> E' + B) (m : es_monad E S A) : es_monad E' S B :=
  ESMonad (fun s => let (m, s) := run_es_monad m s in (f m, s)).

Definition with_except {E E' S A} (f : E -> E') (m : es_monad E S A) : es_monad E' S A :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl (f e), s)
       | inr x => (inr x, s)
       end).

Module ESMonadNotations.
  Declare Scope es_monad_scope.
  Delimit Scope es_monad_scope with es_monad.
  Bind Scope es_monad_scope with es_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : es_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : es_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : es_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : es_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : es_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : es_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : es_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : es_monad_scope.
End ESMonadNotations.
