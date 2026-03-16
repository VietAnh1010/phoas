From shift_reset.lib Require Import signatures.

Record cw_monad (R W A : Type) : Type := CWMonad { run_cw_monad : (A -> R * W) -> R * W }.
Definition t : Type -> Type -> Type -> Type := cw_monad.

Arguments CWMonad {R W A} _.
Arguments run_cw_monad {R W A} _ _.

Definition pure {R W A} (x : A) : cw_monad R W A :=
  CWMonad (fun k => k x).

Definition map {R W A B} (f : A -> B) (m : cw_monad R W A) : cw_monad R W B :=
  CWMonad (fun k => run_cw_monad m (fun x => k (f x))).

Definition mapl {R W A B} (x : B) (m : cw_monad R W A) : cw_monad R W B :=
  CWMonad (fun k => run_cw_monad m (fun _ => k x)).

Definition app {R W A B} (m1 : cw_monad R W (A -> B)) (m2 : cw_monad R W A) : cw_monad R W B :=
  CWMonad (fun k => run_cw_monad m1 (fun f => run_cw_monad m2 (fun x => k (f x)))).

Definition appl {R W A B} (m1 : cw_monad R W A) (m2 : cw_monad R W B) : cw_monad R W A :=
  CWMonad (fun k => run_cw_monad m1 (fun x => run_cw_monad m2 (fun _ => k x))).

Definition appr {R W A B} (m1 : cw_monad R W A) (m2 : cw_monad R W B) : cw_monad R W B :=
  CWMonad (fun k => run_cw_monad m1 (fun _ => run_cw_monad m2 k)).

Definition bind {R W A B} (m : cw_monad R W A) (f : A -> cw_monad R W B) : cw_monad R W B :=
  CWMonad (fun k => run_cw_monad m (fun x => run_cw_monad (f x) k)).

Definition join {R W A} (m : cw_monad R W (cw_monad R W A)) : cw_monad R W A :=
  CWMonad (fun k => run_cw_monad m (fun m => run_cw_monad m k)).

Definition callcc {R W A B} (f : (A -> cw_monad R W B) -> cw_monad R W A) : cw_monad R W A :=
  CWMonad (fun k => run_cw_monad (f (fun x => CWMonad (fun _ => k x))) k).

Module Make (M : Monoid).
  Definition w : Type := M.t.
  Definition t (R : Type) : Type -> Type := cw_monad R w.

  Definition reset {R R'} (m : cw_monad R w R) : cw_monad R' w R :=
    CWMonad (fun k => let (x, w1) := run_cw_monad m (fun x => (x, M.empty)) in let (y, w2) := k x in (y, M.append w1 w2)).

  Definition shift {R R' A} (f : (A -> cw_monad R' w R) -> cw_monad R w R) : cw_monad R w A :=
    CWMonad
      (fun k =>
         run_cw_monad
           (f (fun x => CWMonad (fun k' => let (y, w1) := k x in let (z, w2) := k' y in (z, M.append w1 w2))))
           (fun x => (x, M.empty))).

  Definition tell {R} (w' : w) : cw_monad R w unit :=
    CWMonad (fun k => let (x, w'') := k tt in (x, M.append w' w'')).
End Make.

Definition map_cont {R W A} (f : R -> R) (m : cw_monad R W A) : cw_monad R W A :=
  CWMonad (fun k => let (x, w) := run_cw_monad m k in (f x, w)).

Module CWMonadNotations.
  Declare Scope cw_monad_scope.
  Delimit Scope cw_monad_scope with cw_monad.
  Bind Scope cw_monad_scope with cw_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : cw_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : cw_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : cw_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : cw_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : cw_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : cw_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : cw_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : cw_monad_scope.
End CWMonadNotations.
