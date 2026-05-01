From Stdlib Require Import List.
Import ListNotations.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Inductive lr_monad (R A : Type) : Type :=
| LRMonad : (R -> step R A) -> lr_monad R A
with step (R A : Type) : Type :=
| Nil : step R A
| Cons : A -> lr_monad R A -> step R A.

Definition t : Type -> Type -> Type := lr_monad.

Arguments LRMonad {R A} _.
Arguments Nil {R A}.
Arguments Cons {R A} _ _.

Definition run_lr_monad {R A} : lr_monad R A -> R -> step R A :=
  fun '(LRMonad m) => m.

Definition empty {R A} : lr_monad R A :=
  LRMonad (fun _ => Nil).

Definition cons {R A} (x : A) (m : lr_monad R A) : lr_monad R A :=
  LRMonad (fun _ => Cons x m).

Fixpoint combine {R A} (m1 : lr_monad R A) (m2 : lr_monad R A) : lr_monad R A :=
  LRMonad
    (fun r =>
       match run_lr_monad m1 r with
       | Nil => run_lr_monad m2 r
       | Cons x m1' => Cons x (combine m1' m2)
       end).

Definition pure {R A} (x : A) : lr_monad R A :=
  LRMonad (fun _ => Cons x empty).

Fixpoint map {R A B} (f : A -> B) (m : lr_monad R A) : lr_monad R B :=
  LRMonad
    (fun r =>
       match run_lr_monad m r with
       | Nil => Nil
       | Cons x m' => Cons (f x) (map f m')
       end).

Fixpoint map_const {R A B} (x : B) (m : lr_monad R A) : lr_monad R B :=
  LRMonad
    (fun r =>
       match run_lr_monad m r with
       | Nil => Nil
       | Cons _ m' => Cons x (map_const x m')
       end).

Fixpoint apply {R A B} (m1 : lr_monad R (A -> B)) (m2 : lr_monad R A) : lr_monad R B :=
  LRMonad
    (fun r =>
       match run_lr_monad m1 r with
       | Nil => Nil
       | Cons f m1' => run_lr_monad (combine (map f m2) (apply m1' m2)) r
       end).

Fixpoint seq_left {R A B} (m1 : lr_monad R A) (m2 : lr_monad R B) : lr_monad R A :=
  LRMonad
    (fun r =>
       match run_lr_monad m1 r with
       | Nil => Nil
       | Cons x m1' => run_lr_monad (combine (map_const x m2) (seq_left m1' m2)) r
       end).

Fixpoint seq_right {R A B} (m1 : lr_monad R A) (m2 : lr_monad R B) : lr_monad R B :=
  LRMonad
    (fun r =>
       match run_lr_monad m1 r with
       | Nil => Nil
       | Cons _ m1' => run_lr_monad (combine m2 (seq_right m1' m2)) r
       end).

Fixpoint bind {R A B} (m : lr_monad R A) (f : A -> lr_monad R B) : lr_monad R B :=
  LRMonad
    (fun r =>
       match run_lr_monad m r with
       | Nil => Nil
       | Cons x m' => run_lr_monad (combine (f x) (bind m' f)) r
       end).

Fixpoint join {R A} (m : lr_monad R (lr_monad R A)) : lr_monad R A :=
  LRMonad
    (fun r =>
       match run_lr_monad m r with
       | Nil => Nil
       | Cons m m' => run_lr_monad (combine m (join m')) r
       end).

Fixpoint of_list {R A} (xs : list A) : lr_monad R A :=
  LRMonad
    (fun _ =>
       match xs with
       | [] => Nil
       | x :: xs' => Cons x (of_list xs')
       end).

Fixpoint take {R A} (n : nat) (m : lr_monad R A) : lr_monad R A :=
  LRMonad
    (fun r =>
       match n with
       | O => Nil
       | S n' =>
           match run_lr_monad m r with
           | Nil => Nil
           | Cons x m' => Cons x (take n' m')
           end
       end).

Fixpoint drop {R A} (n : nat) (m : lr_monad R A) : lr_monad R A :=
  LRMonad
    (fun r =>
       match n with
       | O => run_lr_monad m r
       | S n' =>
           match run_lr_monad m r with
           | Nil => Nil
           | Cons _ m' => run_lr_monad (drop n' m') r
           end
       end).

Fixpoint filter {R A} (f : A -> bool) (m : lr_monad R A) : lr_monad R A :=
  LRMonad
    (fun r =>
       match run_lr_monad m r with
       | Nil => Nil
       | Cons x m' => if f x then Cons x (filter f m') else run_lr_monad (filter f m') r
       end).

Fixpoint take_while {R A} (f : A -> bool) (m : lr_monad R A) : lr_monad R A :=
  LRMonad
    (fun r =>
       match run_lr_monad m r with
       | Nil => Nil
       | Cons x m' => if f x then Cons x (take_while f m') else Nil
       end).

Fixpoint drop_while {R A} (f : A -> bool) (m : lr_monad R A) : lr_monad R A :=
  LRMonad
    (fun r =>
       match run_lr_monad m r with
       | Nil => Nil
       | Cons x m' => if f x then run_lr_monad (drop_while f m') r else Cons x m'
       end).

Fixpoint zip {R A B} (m1 : lr_monad R A) (m2 : lr_monad R B) : lr_monad R (A * B) :=
  LRMonad
    (fun r =>
       match run_lr_monad m1 r with
       | Nil => Nil
       | Cons x m1' =>
           match run_lr_monad m2 r with
           | Nil => Nil
           | Cons y m2' => Cons (x, y) (zip m1' m2')
           end
       end).

Definition ask {R} : lr_monad R R :=
  LRMonad (fun r => Cons r empty).

Fixpoint local {R A} (f : R -> R) (m : lr_monad R A) : lr_monad R A :=
  LRMonad
    (fun r =>
       match run_lr_monad m (f r) with
       | Nil => Nil
       | Cons x m' => Cons x (local f m')
       end).

Module LRMonadNotations.
  Declare Scope lr_monad_scope.
  Delimit Scope lr_monad_scope with lr_monad.
  Bind Scope lr_monad_scope with lr_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : lr_monad_scope.
  Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : lr_monad_scope.
  Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : lr_monad_scope.
  Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : lr_monad_scope.
  Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : lr_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : lr_monad_scope.
  Notation "m1 <|> m2" := (combine m1 m2) (at level 55, left associativity) : lr_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : lr_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : lr_monad_scope.
End LRMonadNotations.
