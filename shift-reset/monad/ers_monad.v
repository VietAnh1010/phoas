Record ers_monad (E R S A : Type) : Type := ERSMonad { run_ers_monad : R -> S -> (E + A) * S }.
Definition t : Type -> Type -> Type -> Type -> Type := ers_monad.

Arguments ERSMonad {E R S A} _.
Arguments run_ers_monad {E R S A} _ _ _.

Definition pure {E R S A} (x : A) : ers_monad E R S A :=
  ERSMonad (fun _ s => (inr x, s)).

Definition map {E R S A B} (f : A -> B) (m : ers_monad E R S A) : ers_monad E R S B :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr x => (inr (f x), s)
       end).

Definition mapl {E R S A B} (x : B) (m : ers_monad E R S A) : ers_monad E R S B :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr _ => (inr x, s)
       end).

Definition app {E R S A B} (m1 : ers_monad E R S (A -> B)) (m2 : ers_monad E R S A) : ers_monad E R S B :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m1 r s in
       match m with
       | inl e => (inl e, s)
       | inr f =>
           let (m, s) := run_ers_monad m2 r s in
           match m with
           | inl e => (inl e, s)
           | inr x => (inr (f x), s)
           end
       end).

Definition appl {E R S A B} (m1 : ers_monad E R S A) (m2 : ers_monad E R S B) : ers_monad E R S A :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m1 r s in
       match m with
       | inl e => (inl e, s)
       | inr x =>
           let (m, s) := run_ers_monad m2 r s in
           match m with
           | inl e => (inl e, s)
           | inr _ => (inr x, s)
           end
       end).

Definition appr {E R S A B} (m1 : ers_monad E R S A) (m2 : ers_monad E R S B) : ers_monad E R S B :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m1 r s in
       match m with
       | inl e => (inl e, s)
       | inr x => run_ers_monad m2 r s
       end).

Definition bind {E R S A B} (m : ers_monad E R S A) (f : A -> ers_monad E R S B) : ers_monad E R S B :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr x => run_ers_monad (f x) r s
       end).

Definition join {E R S A} (m : ers_monad E R S (ers_monad E R S A)) : ers_monad E R S A :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr m => run_ers_monad m r s
       end).

Definition ask {E R S} : ers_monad E R S R :=
  ERSMonad (fun r s => (inr r, s)).

Definition reader {E R S A} (f : R -> A) : ers_monad E R S A :=
  ERSMonad (fun r s => (inr (f r), s)).

Definition local {E R S A} (f : R -> R) (m : ers_monad E R S A) : ers_monad E R S A :=
  ERSMonad (fun r => run_ers_monad m (f r)).

Definition scope {E R S A} (r : R) (m : ers_monad E R S A) : ers_monad E R S A :=
  ERSMonad (fun _ => run_ers_monad m r).

Definition get {E R S} : ers_monad E R S S :=
  ERSMonad (fun _ s => (inr s, s)).

Definition put {E R S} (s : S) : ers_monad E R S unit :=
  ERSMonad (fun _ _ => (inr tt, s)).

Definition state {E R S A} (f : S -> A * S) : ers_monad E R S A :=
  ERSMonad (fun _ s => let (x, s) := f s in (inr x, s)).

Definition gets {E R S A} (f : S -> A) : ers_monad E R S A :=
  ERSMonad (fun _ s => (inr (f s), s)).

Definition modify {E R S} (f : S -> S) : ers_monad E R S unit :=
  ERSMonad (fun _ s => (inr tt, f s)).

Definition throw {E R S A} (e : E) : ers_monad E R S A :=
  ERSMonad (fun _ s => (inl e, s)).

Definition except {E R S A} (m : E + A) : ers_monad E R S A :=
  ERSMonad (fun _ s => (m, s)).

Definition catch {E R S A} (m : ers_monad E R S A) (f : E -> ers_monad E R S A) : ers_monad E R S A :=
  ERSMonad
    (fun r s =>
       let (m, s) := run_ers_monad m r s in
       match m with
       | inl e => run_ers_monad (f e) r s
       | inr x => (inr x, s)
       end).

Definition try {E R S A} (m : ers_monad E R S A) : ers_monad E R S (E + A) :=
  ERSMonad (fun r s => let (m, s) := run_ers_monad m r s in (inr m, s)).

Definition finally {E R S A} (m1 : ers_monad E R S A) (m2 : ers_monad E R S unit) : ers_monad E R S A :=
  ERSMonad
    (fun r s =>
       let (m1, s) := run_ers_monad m1 r s in
       let (m2, s) := run_ers_monad m2 r s in
       match m2 with
       | inl e => (inl e, s)
       | inr _ => (m1, s)
       end).

Module ERSMonadNotations.
  Declare Scope ers_monad_scope.
  Delimit Scope ers_monad_scope with ers_monad.
  Bind Scope ers_monad_scope with ers_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : ers_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : ers_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : ers_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : ers_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : ers_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : ers_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : ers_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : ers_monad_scope.
End ERSMonadNotations.
