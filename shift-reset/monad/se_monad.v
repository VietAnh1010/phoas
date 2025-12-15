Record se_monad (S E A : Type) : Type := SEMonad { run_se_monad : S -> E + (A * S) }.
Definition t : Type -> Type -> Type -> Type := se_monad.

Arguments SEMonad {S E A} _.
Arguments run_se_monad {S E A} _ _.

Definition pure {S E A} (x : A) : se_monad S E A :=
  SEMonad (fun s => inr (x, s)).

Definition map {S E A B} (f : A -> B) (m : se_monad S E A) : se_monad S E B :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => inl e
       | inr (x, s) => inr (f x, s)
       end).

Definition mapl {S E A B} (x : B) (m : se_monad S E A) : se_monad S E B :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => inl e
       | inr (_, s) => inr (x, s)
       end).

Definition app {S E A B} (m1 : se_monad S E (A -> B)) (m2 : se_monad S E A) : se_monad S E B :=
  SEMonad
    (fun s =>
       match run_se_monad m1 s with
       | inl e => inl e
       | inr (f, s) =>
           match run_se_monad m2 s with
           | inl e => inl e
           | inr (x, s) => inr (f x, s)
           end
       end).

Definition appl {S E A B} (m1 : se_monad S E A) (m2 : se_monad S E B) : se_monad S E A :=
  SEMonad
    (fun s =>
       match run_se_monad m1 s with
       | inl e => inl e
       | inr (x, s) =>
           match run_se_monad m2 s with
           | inl e => inl e
           | inr (_, s) => inr (x, s)
           end
       end).

Definition appr {S E A B} (m1 : se_monad S E A) (m2 : se_monad S E B) : se_monad S E B :=
  SEMonad
    (fun s =>
       match run_se_monad m1 s with
       | inl e => inl e
       | inr (_, s) => run_se_monad m2 s
       end).

Definition bind {S E A B} (m : se_monad S E A) (f : A -> se_monad S E B) : se_monad S E B :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => inl e
       | inr (x, s) => run_se_monad (f x) s
       end).

Definition join {S E A} (m : se_monad S E (se_monad S E A)) : se_monad S E A :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => inl e
       | inr (m, s) => run_se_monad m s
       end).

Definition get {S E} : se_monad S E S :=
  SEMonad (fun s => inr (s, s)).

Definition put {S E} (s : S) : se_monad S E unit :=
  SEMonad (fun _ => inr (tt, s)).

Definition state {S E A} (f : S -> A * S) : se_monad S E A :=
  SEMonad (fun s => inr (f s)).

Definition gets {S E A} (f : S -> A) : se_monad S E A :=
  SEMonad (fun s => inr (f s, s)).

Definition modify {S E} (f : S -> S) : se_monad S E unit :=
  SEMonad (fun s => inr (tt, f s)).

Definition throw {S E A} (e : E) : se_monad S E A :=
  SEMonad (fun _ => inl e).

Definition except {S E A} (m : E + A) : se_monad S E A :=
  SEMonad
    (fun s =>
       match m with
       | inl e => inl e
       | inr x => inr (x, s)
       end).

Definition catch {S E A} (m : se_monad S E A) (f : E -> se_monad S E A) : se_monad S E A :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => run_se_monad (f e) s
       | inr p => inr p
       end).

Definition try {S E A} (m : se_monad S E A) : se_monad S E (E + A) :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => inr (inl e, s)
       | inr (x, s) => inr (inr x, s)
       end).

Definition finally {S E A} (m1 : se_monad S E A) (m2 : se_monad S E unit) : se_monad S E A :=
  SEMonad
    (fun s =>
       match run_se_monad m1 s with
       | inl e1 =>
           match run_se_monad m2 s with
           | inl e2 => inl e2
           | inr _ => inl e1
           end
       | inr (x, s) =>
           match run_se_monad m2 s with
           | inl e => inl e
           | inr (_, s) => inr (x, s)
           end
       end).

Definition map_except {S E E' A B} (f : E + A -> E' + B) (m : se_monad S E A) : se_monad S E' B :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e =>
           match f (inl e) with
           | inl e => inl e
           | inr x => inr (x, s)
           end
       | inr (x, s) =>
           match f (inr x) with
           | inl e => inl e
           | inr y => inr (y, s)
           end
       end).

Definition with_except {S E E' A} (f : E -> E') (m : se_monad S E A) : se_monad S E' A :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => inl (f e)
       | inr p => inr p
       end).

Definition map_state {S E A B} (f : A * S -> B * S) (m : se_monad S E A) : se_monad S E B :=
  SEMonad
    (fun s =>
       match run_se_monad m s with
       | inl e => inl e
       | inr p => inr (f p)
       end).

Definition with_state {S E A} (f : S -> S) (m : se_monad S E A) : se_monad S E A :=
  SEMonad (fun s => run_se_monad m (f s)).

Module SEMonadNotations.
  Declare Scope se_monad_scope.
  Delimit Scope se_monad_scope with se_monad.
  Bind Scope se_monad_scope with se_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : se_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : se_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : se_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : se_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : se_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : se_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : se_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : se_monad_scope.
End SEMonadNotations.
