From Stdlib Require Import List.
Import ListNotations.

Record lc_monad (R A : Type) : Type := LCMonad { run_lc_monad : R -> (A -> R -> R) -> R }.
Definition t : Type -> Type -> Type := lc_monad.

Arguments LCMonad {R A} _.
Arguments run_lc_monad {R A} _ _ _.

Definition pure {R A} (x : A) : lc_monad R A :=
  LCMonad (fun r k => k x r).

Definition map {R A B} (f : A -> B) (m : lc_monad R A) : lc_monad R B :=
  LCMonad (fun r k => run_lc_monad m r (fun x => k (f x))).

Definition map_const {R A B} (x : B) (m : lc_monad R A) : lc_monad R B :=
  LCMonad (fun r k => run_lc_monad m r (fun _ => k x)).

Definition apply {R A B} (m1 : lc_monad R (A -> B)) (m2 : lc_monad R A) : lc_monad R B :=
  LCMonad (fun r k => run_lc_monad m1 r (fun f r => run_lc_monad m2 r (fun x => k (f x)))).

Definition seq_left {R A B} (m1 : lc_monad R A) (m2 : lc_monad R B) : lc_monad R A :=
  LCMonad (fun r k => run_lc_monad m1 r (fun x r => run_lc_monad m2 r (fun _ => k x))).

Definition seq_right {R A B} (m1 : lc_monad R A) (m2 : lc_monad R B) : lc_monad R B :=
  LCMonad (fun r k => run_lc_monad m1 r (fun _ r => run_lc_monad m2 r k)).

Definition bind {R A B} (m : lc_monad R A) (f : A -> lc_monad R B) : lc_monad R B :=
  LCMonad (fun r k => run_lc_monad m r (fun x r => run_lc_monad (f x) r k)).

Definition join {R A} (m : lc_monad R (lc_monad R A)) : lc_monad R A :=
  LCMonad (fun r k => run_lc_monad m r (fun m r => run_lc_monad m r k)).

Definition empty {R A} : lc_monad R A :=
  LCMonad (fun r _ => r).

Definition combine {R A} (m1 m2 : lc_monad R A) : lc_monad R A :=
  LCMonad (fun r k => run_lc_monad m1 (run_lc_monad m2 r k) k).

Definition cons {R A} (x : A) (m : lc_monad R A) : lc_monad R A :=
  LCMonad (fun r k => k x (run_lc_monad m r k)).

Fixpoint of_list {R A} (xs : list A) : lc_monad R A :=
  LCMonad
    (fun r k =>
       match xs with
       | [] => r
       | x :: xs' => k x (run_lc_monad (of_list xs') r k)
       end).

Definition cont {R A} (f : (A -> R) -> R) : lc_monad R A :=
  LCMonad (fun r k => f (fun x => k x r)).

Definition callcc {R A B} (f : (A -> lc_monad R B) -> lc_monad R A) : lc_monad R A :=
  LCMonad (fun r k => run_lc_monad (f (fun x => LCMonad (fun r _ => k x r))) r k).

Definition callcc' {R A B} (f : (A -> lc_monad R B) -> lc_monad R A) : lc_monad R A :=
  LCMonad (fun r k => run_lc_monad (f (fun x => LCMonad (fun _ _ => k x r))) r k).

Definition map_cont {R A} (f : R -> R) (m : lc_monad R A) : lc_monad R A :=
  LCMonad (fun r k => f (run_lc_monad m r (fun x r => k x (f r)))).

Definition with_cont {R A B} (f : (B -> R) -> A -> R) (m : lc_monad R A) : lc_monad R B :=
  LCMonad (fun r k => run_lc_monad m r (fun x r => f (fun y => k y r) x)).

Module LCMonadNotations.
  Declare Scope lc_monad_scope.
  Delimit Scope lc_monad_scope with lc_monad.
  Bind Scope lc_monad_scope with lc_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : lc_monad_scope.
  Notation "x <$ m" := (map_const x m) (at level 65, right associativity) : lc_monad_scope.
  Notation "m1 <*> m2" := (apply m1 m2) (at level 55, left associativity) : lc_monad_scope.
  Notation "m1 <* m2" := (seq_left m1 m2) (at level 55, left associativity) : lc_monad_scope.
  Notation "m1 *> m2" := (seq_right m1 m2) (at level 55, left associativity) : lc_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : lc_monad_scope.
  Notation "m1 <|> m2" := (combine m1 m2) (at level 55, left associativity) : lc_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : lc_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : lc_monad_scope.
End LCMonadNotations.
