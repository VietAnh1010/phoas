From Stdlib Require Import List.
Import ListNotations.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Inductive le_monad (E A : Type) : Type :=
| LEMonad : E + step E A -> le_monad E A
with step (E A : Type) : Type :=
| Nil : step E A
| Cons : A -> le_monad E A -> step E A.

Definition t : Type -> Type -> Type := le_monad.

Arguments LEMonad {E A} _.
Arguments Nil {E A}.
Arguments Cons {E A} _ _.

Definition run_le_monad {E A} : le_monad E A -> E + step E A :=
  fun '(LEMonad m) => m.

Definition empty {E A} : le_monad E A :=
  LEMonad (inr Nil).

Definition cons {E A} (x : A) (m : le_monad E A) : le_monad E A :=
  LEMonad (inr (Cons x m)).

Fixpoint combine {E A} (m1 m2 : le_monad E A) : le_monad E A :=
  LEMonad match run_le_monad m1 with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => run_le_monad m2
        | Cons x m1' => inr (Cons x (combine m1' m2))
        end
    end.

Definition pure {E A} (x : A) : le_monad E A :=
  LEMonad (inr (Cons x empty)).

Fixpoint map {E A B} (f : A -> B) (m : le_monad E A) : le_monad E B :=
  LEMonad match run_le_monad m with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => inr (Cons (f x) (map f m'))
        end
    end.

Fixpoint map_const {E A B} (x : B) (m : le_monad E A) : le_monad E B :=
  LEMonad match run_le_monad m with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons _ m' => inr (Cons x (map_const x m'))
        end
    end.

Fixpoint apply {E A B} (m1 : le_monad E (A -> B)) (m2 : le_monad E A) : le_monad E B :=
  LEMonad match run_le_monad m1 with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons f m1' => run_le_monad (combine (map f m2) (apply m1' m2))
        end
    end.

Fixpoint seq_left {E A B} (m1 : le_monad E A) (m2 : le_monad E B) : le_monad E A :=
  LEMonad match run_le_monad m1 with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m1' => run_le_monad (combine (map_const x m2) (seq_left m1' m2))
        end
    end.

Fixpoint seq_right {E A B} (m1 : le_monad E A) (m2 : le_monad E B) : le_monad E B :=
  LEMonad match run_le_monad m1 with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons _ m1' => run_le_monad (combine m2 (seq_right m1' m2))
        end
    end.

Fixpoint bind {E A B} (m : le_monad E A) (f : A -> le_monad E B) : le_monad E B :=
  LEMonad match run_le_monad m with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => run_le_monad (combine (f x) (bind m' f))
        end
    end.

Fixpoint join {E A} (m : le_monad E (le_monad E A)) : le_monad E A :=
  LEMonad match run_le_monad m with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons m m' => run_le_monad (combine m (join m'))
        end
    end.

Fixpoint of_list {E A} (xs : list A) : le_monad E A :=
  LEMonad match xs with
    | [] => inr Nil
    | x :: xs' => inr (Cons x (of_list xs'))
    end.

Fixpoint take {E A} (n : nat) (m : le_monad E A) : le_monad E A :=
  LEMonad match n with
    | O => inr Nil
    | S n' =>
        match run_le_monad m with
        | inl e => inl e
        | inr m =>
            match m with
            | Nil => inr Nil
            | Cons x m' => inr (Cons x (take n' m'))
            end
        end
    end.

Fixpoint drop {E A} (n : nat) (m : le_monad E A) : le_monad E A :=
  LEMonad match n with
    | O => run_le_monad m
    | S n' =>
        match run_le_monad m with
        | inl e => inl e
        | inr m =>
            match m with
            | Nil => inr Nil
            | Cons _ m' => run_le_monad (drop n' m')
            end
        end
    end.

Fixpoint filter {E A} (f : A -> bool) (m : le_monad E A) : le_monad E A :=
  LEMonad match run_le_monad m with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => if f x then inr (Cons x (filter f m')) else run_le_monad (filter f m')
        end
    end.

Fixpoint take_while {E A} (f : A -> bool) (m : le_monad E A) : le_monad E A :=
  LEMonad match run_le_monad m with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => if f x then inr (Cons x (take_while f m')) else inr Nil
        end
    end.

Fixpoint drop_while {E A} (f : A -> bool) (m : le_monad E A) : le_monad E A :=
  LEMonad match run_le_monad m with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => if f x then run_le_monad (drop_while f m') else inr (Cons x m')
        end
    end.

Fixpoint zip {E A B} (m1 : le_monad E A) (m2 : le_monad E B) : le_monad E (A * B) :=
  LEMonad match run_le_monad m1 with
    | inl e => inl e
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m1' =>
            match run_le_monad m2 with
            | inl e => inl e
            | inr m =>
                match m with
                | Nil => inr Nil
                | Cons y m2' => inr (Cons (x, y) (zip m1' m2'))
                end
            end
        end
    end.

Definition throw {E A} (e : E) : le_monad E A :=
  LEMonad (inl e).

Fixpoint catch {E A} (m : le_monad E A) (f : E -> le_monad E A) : le_monad E A :=
  LEMonad match run_le_monad m with
    | inl e => run_le_monad (f e)
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => inr (Cons x (catch m' f))
        end
    end.

Definition catch' {E A} (m : le_monad E A) (f : E -> le_monad E A) : le_monad E A :=
  LEMonad match run_le_monad m with
    | inl e => run_le_monad (f e)
    | inr m => inr m
    end.

Fixpoint try {E A} (m : le_monad E A) : le_monad E (E + A) :=
  LEMonad match run_le_monad m with
    | inl e => inr (Cons (inl e) empty)
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => inr (Cons (inr x) (try m'))
        end
    end.

Fixpoint map_except {E E' A B} (f : E + A -> E' + B) (m : le_monad E A) : le_monad E' B :=
  LEMonad match run_le_monad m with
    | inl e =>
        match f (inl e) with
        | inl e => inl e
        | inr x => inr (Cons x empty)
        end
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' =>
            match f (inr x) with
            | inl e => inl e
            | inr y => inr (Cons y (map_except f m'))
            end
        end
    end.

Fixpoint with_except {E E' A} (f : E -> E') (m : le_monad E A) : le_monad E' A :=
  LEMonad match run_le_monad m with
    | inl e => inl (f e)
    | inr m =>
        match m with
        | Nil => inr Nil
        | Cons x m' => inr (Cons x (with_except f m'))
        end
    end.

Module LEMonadNotations.
  Declare Scope le_monad_scope.
  Delimit Scope le_monad_scope with le_monad.
  Bind Scope le_monad_scope with le_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : le_monad_scope.
  Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : le_monad_scope.
  Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : le_monad_scope.
  Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : le_monad_scope.
  Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : le_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : le_monad_scope.
  Notation "m1 <|> m2" := (combine m1 m2) (at level 55, left associativity) : le_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : le_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : le_monad_scope.
End LEMonadNotations.
