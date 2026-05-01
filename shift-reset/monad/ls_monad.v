From Stdlib Require Import List.
Import ListNotations.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Inductive ls_monad (S A : Type) : Type :=
| LSMonad : (S -> step S A * S) -> ls_monad S A
with step (S A : Type) : Type :=
| Nil : step S A
| Cons : A -> ls_monad S A -> step S A.

Definition t : Type -> Type -> Type := ls_monad.

Arguments LSMonad {S A} _.
Arguments Nil {S A}.
Arguments Cons {S A} _ _.

Definition run_ls_monad {S A} : ls_monad S A -> S -> step S A * S :=
  fun '(LSMonad m) => m.

Definition empty {S A} : ls_monad S A :=
  LSMonad (fun s => (Nil, s)).

Definition cons {S A} (x : A) (m : ls_monad S A) : ls_monad S A :=
  LSMonad (fun s => (Cons x m, s)).

Fixpoint combine {S A} (m1 : ls_monad S A) (m2 : ls_monad S A) : ls_monad S A :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m1 s in
       match m with
       | Nil => run_ls_monad m2 s
       | Cons x m1' => (Cons x (combine m1' m2), s)
       end).

Definition pure {S A} (x : A) : ls_monad S A :=
  LSMonad (fun s => (Cons x empty, s)).

Fixpoint map {S A B} (f : A -> B) (m : ls_monad S A) : ls_monad S B :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons x m' => (Cons (f x) (map f m'), s)
       end).

Fixpoint map_const {S A B} (x : B) (m : ls_monad S A) : ls_monad S B :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons _ m' => (Cons x (map_const x m'), s)
       end).

Fixpoint apply {S A B} (m1 : ls_monad S (A -> B)) (m2 : ls_monad S A) : ls_monad S B :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m1 s in
       match m with
       | Nil => (Nil, s)
       | Cons f m1' => run_ls_monad (combine (map f m2) (apply m1' m2)) s
       end).

Fixpoint seq_left {S A B} (m1 : ls_monad S A) (m2 : ls_monad S B) : ls_monad S A :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m1 s in
       match m with
       | Nil => (Nil, s)
       | Cons x m1' => run_ls_monad (combine (map_const x m2) (seq_left m1' m2)) s
       end).

Fixpoint seq_right {S A B} (m1 : ls_monad S A) (m2 : ls_monad S B) : ls_monad S B :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m1 s in
       match m with
       | Nil => (Nil, s)
       | Cons _ m1' => run_ls_monad (combine m2 (seq_right m1' m2)) s
       end).

Fixpoint bind {S A B} (m : ls_monad S A) (f : A -> ls_monad S B) : ls_monad S B :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons x m' => run_ls_monad (combine (f x) (bind m' f)) s
       end).

Fixpoint join {S A} (m : ls_monad S (ls_monad S A)) : ls_monad S A :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons m m' => run_ls_monad (combine m (join m')) s
       end).

Fixpoint of_list {S A} (xs : list A) : ls_monad S A :=
  LSMonad
    (fun s =>
       match xs with
       | [] => (Nil, s)
       | x :: xs' => (Cons x (of_list xs'), s)
       end).

Fixpoint take {S A} (n : nat) (m : ls_monad S A) : ls_monad S A :=
  LSMonad
    (fun s =>
       match n with
       | O => (Nil, s)
       | S n' =>
           let (m, s) := run_ls_monad m s in
           match m with
           | Nil => (Nil, s)
           | Cons x m' => (Cons x (take n' m'), s)
           end
       end).

Fixpoint drop {S A} (n : nat) (m : ls_monad S A) : ls_monad S A :=
  LSMonad
    (fun s =>
       match n with
       | O => run_ls_monad m s
       | S n' =>
           let (m, s) := run_ls_monad m s in
           match m with
           | Nil => (Nil, s)
           | Cons _ m' => run_ls_monad (drop n' m') s
           end
       end).

Fixpoint filter {S A} (f : A -> bool) (m : ls_monad S A) : ls_monad S A :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons x m' => if f x then (Cons x (filter f m'), s) else run_ls_monad (filter f m') s
       end).

Fixpoint take_while {S A} (f : A -> bool) (m : ls_monad S A) : ls_monad S A :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons x m' => if f x then (Cons x (take_while f m'), s) else (Nil, s)
       end).

Fixpoint drop_while {S A} (f : A -> bool) (m : ls_monad S A) : ls_monad S A :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons x m' => if f x then run_ls_monad (drop_while f m') s else (Cons x m', s)
       end).

Fixpoint zip {S A B} (m1 : ls_monad S A) (m2 : ls_monad S B) : ls_monad S (A * B) :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m1 s in
       match m with
       | Nil => (Nil, s)
       | Cons x m1' =>
           let (m, s) := run_ls_monad m2 s in
           match m with
           | Nil => (Nil, s)
           | Cons y m2' => (Cons (x, y) (zip m1' m2'), s)
           end
       end).

Definition get {S} : ls_monad S S :=
  LSMonad (fun s => (Cons s empty, s)).

Definition put {S} (s : S) : ls_monad S unit :=
  LSMonad (fun _ => (Cons tt empty, s)).

Definition state {S A} (f : S -> A * S) : ls_monad S A :=
  LSMonad (fun s => let (x, s) := f s in (Cons x empty, s)).

Definition gets {S A} (f : S -> A) : ls_monad S A :=
  LSMonad (fun s => (Cons (f s) empty, s)).

Definition modify {S} (f : S -> S) : ls_monad S unit :=
  LSMonad (fun s => (Cons tt empty, f s)).

Fixpoint map_state {S A B} (f : A * S -> B * S) (m : ls_monad S A) : ls_monad S B :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m s in
       match m with
       | Nil => (Nil, s)
       | Cons x m' => let (y, s) := f (x, s) in (Cons y (map_state f m'), s)
       end).

Fixpoint with_state {S A} (f : S -> S) (m : ls_monad S A) : ls_monad S A :=
  LSMonad
    (fun s =>
       let (m, s) := run_ls_monad m (f s) in
       match m with
       | Nil => (Nil, s)
       | Cons x m' => (Cons x (with_state f m'), s)
       end).

Module LSMonadNotations.
  Declare Scope ls_monad_scope.
  Delimit Scope ls_monad_scope with ls_monad.
  Bind Scope ls_monad_scope with ls_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : ls_monad_scope.
  Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : ls_monad_scope.
  Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : ls_monad_scope.
  Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : ls_monad_scope.
  Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : ls_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : ls_monad_scope.
  Notation "m1 <|> m2" := (combine m1 m2) (at level 55, left associativity) : ls_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : ls_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : ls_monad_scope.
End LSMonadNotations.
