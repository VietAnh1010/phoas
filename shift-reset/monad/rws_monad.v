From shift_reset.lib Require Import monoid_sig.

Record rws_monad (R W S A : Type) : Type := RWSMonad { run_rws_monad : R -> S -> A * W * S }.
Definition t : Type -> Type -> Type -> Type -> Type := rws_monad.

Arguments RWSMonad {R W S A} _.
Arguments run_rws_monad {R W S A} _ _ _.

Definition map {R W S A B} (f : A -> B) (m : rws_monad R W S A) : rws_monad R W S B :=
  RWSMonad (fun r s => let '(x, w, s) := run_rws_monad m r s in (f x, w, s)).

Definition mapl {R W S A B} (x : B) (m : rws_monad R W S A) : rws_monad R W S B :=
  RWSMonad (fun r s => let '(_, w, s) := run_rws_monad m r s in (x, w, s)).

Module RWSMonadNotations.
  Declare Scope rws_monad_scope.
  Delimit Scope rws_monad_scope with rws_monad.
  Bind Scope rws_monad_scope with rws_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : rws_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : rws_monad_scope.
  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : rws_monad_scope.
End RWSMonadNotations.

Module Make (M : Monoid).
  Definition w : Type := M.t.
  Definition t (R : Type) : Type -> Type -> Type := rws_monad R w.

  Definition pure {R S A} (x : A) : rws_monad R w S A :=
    RWSMonad (fun _ s => (x, M.empty, s)).

  Definition app {R S A B} (m1 : rws_monad R w S (A -> B)) (m2 : rws_monad R w S A) : rws_monad R w S B :=
    RWSMonad (fun r s => let '(f, w1, s) := run_rws_monad m1 r s in let '(x, w2, s) := run_rws_monad m2 r s in (f x, M.append w1 w2, s)).

  Definition appl {R S A B} (m1 : rws_monad R w S A) (m2 : rws_monad R w S B) : rws_monad R w S A :=
    RWSMonad (fun r s => let '(x, w1, s) := run_rws_monad m1 r s in let '(_, w2, s) := run_rws_monad m2 r s in (x, M.append w1 w2, s)).

  Definition appr {R S A B} (m1 : rws_monad R w S A) (m2 : rws_monad R w S B) : rws_monad R w S B :=
    RWSMonad (fun r s => let '(_, w1, s) := run_rws_monad m1 r s in let '(x, w2, s) := run_rws_monad m2 r s in (x, M.append w1 w2, s)).

  Definition bind {R S A B} (m : rws_monad R w S A) (f : A -> rws_monad R w S B) : rws_monad R w S B :=
    RWSMonad (fun r s => let '(x, w1, s) := run_rws_monad m r s in let '(y, w2, s) := run_rws_monad (f x) r s in (y, M.append w1 w2, s)).

  Definition join {R S A} (m : rws_monad R w S (rws_monad R w S A)) : rws_monad R w S A :=
    RWSMonad (fun r s => let '(m, w1, s) := run_rws_monad m r s in let '(x, w2, s) := run_rws_monad m r s in (x, M.append w1 w2, s)).

  Definition ask {R S} : rws_monad R w S R :=
    RWSMonad (fun r s => (r, M.empty, s)).

  Definition reader {R S A} (f : R -> A) : rws_monad R w S A :=
    RWSMonad (fun r s => (f r, M.empty, s)).

  Definition get {R S} : rws_monad R w S S :=
    RWSMonad (fun _ s => (s, M.empty, s)).

  Definition put {R S} (s : S) : rws_monad R w S unit :=
    RWSMonad (fun _ _ => (tt, M.empty, s)).

  Definition state {R S A} (f : S -> A * S) : rws_monad R w S A :=
    RWSMonad (fun _ s => let (x, s) := f s in (x, M.empty, s)).

  Definition gets {R S A} (f : S -> A) : rws_monad R w S A :=
    RWSMonad (fun _ s => (f s, M.empty, s)).

  Definition modify {R S} (f : S -> S) : rws_monad R w S unit :=
    RWSMonad (fun _ s => (tt, M.empty, f s)).

  Module Notations.
    Import RWSMonadNotations.
    Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : rws_monad_scope.
    Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : rws_monad_scope.
    Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : rws_monad_scope.
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

Definition map_rws {R W W' S A B} (f : A * W * S -> B * W' * S) (m : rws_monad R W S A) : rws_monad R W' S B :=
  RWSMonad (fun r s => f (run_rws_monad m r s)).

Definition with_rws {R' R W S A} (f : R' -> S -> R * S) (m : rws_monad R W S A) : rws_monad R' W S A :=
  RWSMonad (fun r s => let (r, s) := f r s in run_rws_monad m r s).
