From shift_reset.monad Require Import signatures.

Record rws_monad (R W S A : Type) : Type := RWSMonad { run_rws_monad : R -> S -> A * W * S }.
Definition t : Type -> Type -> Type -> Type -> Type := rws_monad.

Arguments RWSMonad {R W S A} _.
Arguments run_rws_monad {R W S A} _ _ _.

Definition map {R W S A B} (f : A -> B) (m : rws_monad R W S A) : rws_monad R W S B :=
  RWSMonad (fun r s => let '(x, w, s) := run_rws_monad m r s in (f x, w, s)).

Definition map_const {R W S A B} (x : B) (m : rws_monad R W S A) : rws_monad R W S B :=
  RWSMonad (fun r s => let '(_, w, s) := run_rws_monad m r s in (x, w, s)).

Module RWSMonadNotations.
  Declare Scope rws_monad_scope.
  Delimit Scope rws_monad_scope with rws_monad.
  Bind Scope rws_monad_scope with rws_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : rws_monad_scope.
  Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : rws_monad_scope.
  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : rws_monad_scope.
End RWSMonadNotations.

Module Make (W : Monoid).
  Definition pure {R S A} (x : A) : rws_monad R W.t S A :=
    RWSMonad (fun _ s => (x, W.empty, s)).

  Definition apply {R S A B} (m1 : rws_monad R W.t S (A -> B)) (m2 : rws_monad R W.t S A) : rws_monad R W.t S B :=
    RWSMonad (fun r s => let '(f, w1, s) := run_rws_monad m1 r s in let '(x, w2, s) := run_rws_monad m2 r s in (f x, W.combine w1 w2, s)).

  Definition seq_left {R S A B} (m1 : rws_monad R W.t S A) (m2 : rws_monad R W.t S B) : rws_monad R W.t S A :=
    RWSMonad (fun r s => let '(x, w1, s) := run_rws_monad m1 r s in let '(_, w2, s) := run_rws_monad m2 r s in (x, W.combine w1 w2, s)).

  Definition seq_right {R S A B} (m1 : rws_monad R W.t S A) (m2 : rws_monad R W.t S B) : rws_monad R W.t S B :=
    RWSMonad (fun r s => let '(_, w1, s) := run_rws_monad m1 r s in let '(x, w2, s) := run_rws_monad m2 r s in (x, W.combine w1 w2, s)).

  Definition bind {R S A B} (m : rws_monad R W.t S A) (f : A -> rws_monad R W.t S B) : rws_monad R W.t S B :=
    RWSMonad (fun r s => let '(x, w1, s) := run_rws_monad m r s in let '(y, w2, s) := run_rws_monad (f x) r s in (y, W.combine w1 w2, s)).

  Definition join {R S A} (m : rws_monad R W.t S (rws_monad R W.t S A)) : rws_monad R W.t S A :=
    RWSMonad (fun r s => let '(m, w1, s) := run_rws_monad m r s in let '(x, w2, s) := run_rws_monad m r s in (x, W.combine w1 w2, s)).

  Definition ask {R S} : rws_monad R W.t S R :=
    RWSMonad (fun r s => (r, W.empty, s)).

  Definition reader {R S A} (f : R -> A) : rws_monad R W.t S A :=
    RWSMonad (fun r s => (f r, W.empty, s)).

  Definition get {R S} : rws_monad R W.t S S :=
    RWSMonad (fun _ s => (s, W.empty, s)).

  Definition put {R S} (s : S) : rws_monad R W.t S unit :=
    RWSMonad (fun _ _ => (tt, W.empty, s)).

  Definition state {R S A} (f : S -> A * S) : rws_monad R W.t S A :=
    RWSMonad (fun _ s => let (x, s) := f s in (x, W.empty, s)).

  Definition gets {R S A} (f : S -> A) : rws_monad R W.t S A :=
    RWSMonad (fun _ s => (f s, W.empty, s)).

  Definition modify {R S} (f : S -> S) : rws_monad R W.t S unit :=
    RWSMonad (fun _ s => (tt, W.empty, f s)).

  Module Notations.
    Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : rws_monad_scope.
    Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : rws_monad_scope.
    Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : rws_monad_scope.
    Notation "m >>= f" := (bind m f) (at level 50, left associativity) : rws_monad_scope.
    Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : rws_monad_scope.
  End Notations.
End Make.

Definition local {R W S A} (f : R -> R) (m : rws_monad R W S A) : rws_monad R W S A :=
  RWSMonad (fun r => run_rws_monad m (f r)).

Definition scope {R W S A} (r : R) (m : rws_monad R W S A) : rws_monad R W S A :=
  RWSMonad (fun _ => run_rws_monad m r).

Definition tell {R W S} (w : W) : rws_monad R W S unit :=
  RWSMonad (fun _ s => (tt, w, s)).

Definition listen {R W S A} (m : rws_monad R W S A) : rws_monad R W S (A * W) :=
  RWSMonad (fun r s => let '(x, w, s) := run_rws_monad m r s in (x, w, w, s)).

Definition pass {R W S A} (m : rws_monad R W S (A * (W -> W))) : rws_monad R W S A :=
  RWSMonad (fun r s => let '(x, f, w, s) := run_rws_monad m r s in (x, f w, s)).

Definition censor {R W S A} (f : W -> W) (m : rws_monad R W S A) : rws_monad R W S A :=
  RWSMonad (fun r s => let '(x, w, s) := run_rws_monad m r s in (x, f w, s)).

Definition listens {R W S A B} (f : W -> B) (m : rws_monad R W S A) : rws_monad R W S (A * B) :=
  RWSMonad (fun r s => let '(x, w, s) := run_rws_monad m r s in (x, f w, w, s)).

Definition writer {R W S A} (m : A * W) : rws_monad R W S A :=
  RWSMonad (fun _ s => (m, s)).

Definition with_reader {R' R W S A} (f : R' -> R) (m : rws_monad R W S A) : rws_monad R' W S A :=
  RWSMonad (fun r => run_rws_monad m (f r)).

Definition map_state {R W S A B} (f : A * S -> B * S) (m : rws_monad R W S A) : rws_monad R W S B :=
  RWSMonad (fun r s => let '(x, w, s) := run_rws_monad m r s in let (y, s) := f (x, s) in (y, w, s)).

Definition with_state {R W S A} (f : S -> S) (m : rws_monad R W S A) : rws_monad R W S A :=
  RWSMonad (fun r s => run_rws_monad m r (f s)).

Definition map_writer {R W W' S A B} (f : A * W -> B * W') (m : rws_monad R W S A) : rws_monad R W' S B :=
  RWSMonad (fun r s => let (m, w) := run_rws_monad m r s in (f m, s)).

Definition map_rws_monad {R W W' S A B} (f : A * W * S -> B * W' * S) (m : rws_monad R W S A) : rws_monad R W' S B :=
  RWSMonad (fun r s => f (run_rws_monad m r s)).

Definition with_rws_monad {R' R W S A} (f : R' -> S -> R * S) (m : rws_monad R W S A) : rws_monad R' W S A :=
  RWSMonad (fun r s => let (r, s) := f r s in run_rws_monad m r s).
