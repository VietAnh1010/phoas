From shift_reset.monad Require Import signatures.

Record ew_monad (E W A : Type) : Type := EWMonad { run_ew_monad : (E + A) * W }.
Definition t : Type -> Type -> Type -> Type := ew_monad.

Arguments EWMonad {E W A} _.
Arguments run_ew_monad {E W A} _.

Definition map {E W A B} (f : A -> B) (m : ew_monad E W A) : ew_monad E W B :=
  EWMonad
    (let (m, w) := run_ew_monad m in
     match m with
     | inl e => (inl e, w)
     | inr x => (inr (f x), w)
     end).

Definition map_const {E W A B} (x : B) (m : ew_monad E W A) : ew_monad E W B :=
  EWMonad
    (let (m, w) := run_ew_monad m in
     match m with
     | inl e => (inl e, w)
     | inr _ => (inr x, w)
     end).

Module EWMonadNotations.
  Declare Scope ew_monad_scope.
  Delimit Scope ew_monad_scope with ew_monad.
  Bind Scope ew_monad_scope with ew_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : ew_monad_scope.
  Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : ew_monad_scope.
  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : ew_monad_scope.
End EWMonadNotations.

Module Make (W : Monoid).
  Definition pure {E A} (x : A) : ew_monad E W.t A :=
    EWMonad (inr x, W.empty).

  Definition apply {E A B} (m1 : ew_monad E W.t (A -> B)) (m2 : ew_monad E W.t A) : ew_monad E W.t B :=
    EWMonad
      (let (m, w1) := run_ew_monad m1 in
       match m with
       | inl e => (inl e, w1)
       | inr f =>
           let (m, w2) := run_ew_monad m2 in
           match m with
           | inl e => (inl e, W.combine w1 w2)
           | inr x => (inr (f x), W.combine w1 w2)
           end
       end).

  Definition seq_left {E A B} (m1 : ew_monad E W.t A) (m2 : ew_monad E W.t B) : ew_monad E W.t A :=
    EWMonad
      (let (m, w1) := run_ew_monad m1 in
       match m with
       | inl e => (inl e, w1)
       | inr x =>
           let (m, w2) := run_ew_monad m2 in
           match m with
           | inl e => (inl e, W.combine w1 w2)
           | inr _ => (inr x, W.combine w1 w2)
           end
       end).

  Definition seq_right {E A B} (m1 : ew_monad E W.t A) (m2 : ew_monad E W.t B) : ew_monad E W.t B :=
    EWMonad
      (let (m, w1) := run_ew_monad m1 in
       match m with
       | inl e => (inl e, w1)
       | inr _ => let (m, w2) := run_ew_monad m2 in (m, W.combine w1 w2)
       end).

  Definition bind {E A B} (m : ew_monad E W.t A) (f : A -> ew_monad E W.t B) : ew_monad E W.t B :=
    EWMonad
      (let (m, w1) := run_ew_monad m in
       match m with
       | inl e => (inl e, w1)
       | inr x => let (m, w2) := run_ew_monad (f x) in (m, W.combine w1 w2)
       end).

  Definition join {E A} (m : ew_monad E W.t (ew_monad E W.t A)) : ew_monad E W.t A :=
    EWMonad
      (let (m, w1) := run_ew_monad m in
       match m with
       | inl e => (inl e, w1)
       | inr m => let (m, w2) := run_ew_monad m in (m, W.combine w1 w2)
       end).

  Definition throw {E A} (e : E) : ew_monad E W.t A :=
    EWMonad (inl e, W.empty).

  Definition except {E A} (m : E + A) : ew_monad E W.t A :=
    EWMonad (m, W.empty).

  Definition catch {E A} (m : ew_monad E W.t A) (f : E -> ew_monad E W.t A) : ew_monad E W.t A :=
    EWMonad
      (let (m, w1) := run_ew_monad m in
       match m with
       | inl e => let (m, w2) := run_ew_monad (f e) in (m, W.combine w1 w2)
       | inr x => (inr x, w1)
       end).

  Definition finally {E A B} (m1 : ew_monad E W.t A) (m2 : ew_monad E W.t B) : ew_monad E W.t A :=
    EWMonad
      (let (m1, w1) := run_ew_monad m1 in
       let (m2, w2) := run_ew_monad m2 in
       match m2 with
       | inl e => (inl e, W.combine w1 w2)
       | inr _ => (m1, W.combine w1 w2)
       end).

  Definition combine {E A} (m1 m2 : ew_monad E W.t A) : ew_monad E W.t A :=
    EWMonad
      (let (m, w1) := run_ew_monad m1 in
       match m with
       | inl _ => let (m, w2) := run_ew_monad m2 in (m, W.combine w1 w2)
       | inr x => (inr x, w1)
       end).

  Module Notations.
    Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : ew_monad_scope.
    Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : ew_monad_scope.
    Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : ew_monad_scope.
    Notation "m >>= f" := (bind m f) (at level 50, left associativity) : ew_monad_scope.
    Notation "m1 <|> m2" := (combine m1 m2) (at level 55, left associativity) : ew_monad_scope.
    Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : ew_monad_scope.
  End Notations.
End Make.

Definition try {E W A} (m : ew_monad E W A) : ew_monad E W (E + A) :=
  EWMonad (let (m, w) := run_ew_monad m in (inr m, w)).

Definition tell {E W} (w : W) : ew_monad E W unit :=
  EWMonad (inr tt, w).

Definition listen {E W A} (m : ew_monad E W A) : ew_monad E W (A * W) :=
  EWMonad
    (let (m, w) := run_ew_monad m in
     match m with
     | inl e => (inl e, w)
     | inr x => (inr (x, w), w)
     end).

Definition pass {E W A} (m : ew_monad E W (A * (W -> W))) : ew_monad E W A :=
  EWMonad
    (let (m, w) := run_ew_monad m in
     match m with
     | inl e => (inl e, w)
     | inr (x, f) => (inr x, f w)
     end).

Definition censor {E W A} (f : W -> W) (m : ew_monad E W A) : ew_monad E W A :=
  EWMonad
    (let (m, w) := run_ew_monad m in
     match m with
     | inl e => (inl e, w)
     | inr x => (inr x, f w)
     end).

Definition listens {E W A B} (f : W -> B) (m : ew_monad E W A) : ew_monad E W (A * B) :=
  EWMonad
    (let (m, w) := run_ew_monad m in
     match m with
     | inl e => (inl e, w)
     | inr x => (inr (x, f w), w)
     end).

Definition map_except {E E' W A B} (f : E + A -> E' + B) (m : ew_monad E W A) : ew_monad E' W B :=
  EWMonad (let (m, w) := run_ew_monad m in (f m, w)).

Definition with_except {E E' W A} (f : E -> E') (m : ew_monad E W A) : ew_monad E' W A :=
  EWMonad
    (let (m, w) := run_ew_monad m in
     match m with
     | inl e => (inl (f e), w)
     | inr x => (inr x, w)
     end).
