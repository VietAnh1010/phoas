From shift_reset.lib Require Import signatures.

Record wc_monad (W R A : Type) : Type := WCMonad { run_wc_monad : (A -> W -> R) -> R }.
Definition t : Type -> Type -> Type -> Type := wc_monad.

Arguments WCMonad {W R A} _.
Arguments run_wc_monad {W R A} _ _.

Definition map {W R A B} (f : A -> B) (m : wc_monad W R A) : wc_monad W R B :=
  WCMonad (fun k => run_wc_monad m (fun x => k (f x))).

Definition mapl {W R A B} (x : B) (m : wc_monad W R A) : wc_monad W R B :=
  WCMonad (fun k => run_wc_monad m (fun _ => k x)).

Module WCMonadNotations.
  Declare Scope wc_monad_wcope.
  Delimit Scope wc_monad_wcope with wc_monad.
  Bind Scope wc_monad_wcope with wc_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : wc_monad_wcope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : wc_monad_wcope.
  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : wc_monad_wcope.
End WCMonadNotations.

Module Make (M : Monoid).
  Definition w : Type := M.t.
  Definition t : Type -> Type -> Type := wc_monad w.

  Definition pure {R A} (x : A) : wc_monad w R A :=
    WCMonad (fun k => k x M.empty).

  Definition app {R A B} (m1 : wc_monad w R (A -> B)) (m2 : wc_monad w R A) : wc_monad w R B :=
    WCMonad (fun k => run_wc_monad m1 (fun f w1 => run_wc_monad m2 (fun x w2 => k (f x) (M.append w1 w2)))).

  Definition appl {R A B} (m1 : wc_monad w R A) (m2 : wc_monad w R B) : wc_monad w R A :=
    WCMonad (fun k => run_wc_monad m1 (fun x w1 => run_wc_monad m2 (fun _ w2 => k x (M.append w1 w2)))).

  Definition appr {R A B} (m1 : wc_monad w R A) (m2 : wc_monad w R B) : wc_monad w R B :=
    WCMonad (fun k => run_wc_monad m1 (fun _ w1 => run_wc_monad m2 (fun x w2 => k x (M.append w1 w2)))).

  Definition bind {R A B} (m : wc_monad w R A) (f : A -> wc_monad w R B) : wc_monad w R B :=
    WCMonad (fun k => run_wc_monad m (fun x w1 => run_wc_monad (f x) (fun y w2 => k y (M.append w1 w2)))).

  Definition join {R A} (m : wc_monad w R (wc_monad w R A)) : wc_monad w R A :=
    WCMonad (fun k => run_wc_monad m (fun m w1 => run_wc_monad m (fun x w2 => k x (M.append w1 w2)))).

  Definition cont {R A} (f : (A -> R) -> R) : wc_monad w R A :=
    WCMonad (fun k => f (fun x => k x M.empty)).

  Definition callcc {R A B} (f : (A -> wc_monad w R B) -> wc_monad w R A) : wc_monad w R A :=
    WCMonad (fun k => run_wc_monad (f (fun x => WCMonad (fun _ => k x M.empty))) k).

  Module Notations.
    Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : wc_monad_wcope.
    Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : wc_monad_wcope.
    Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : wc_monad_wcope.
    Notation "m >>= f" := (bind m f) (at level 50, left associativity) : wc_monad_wcope.
    Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : wc_monad_wcope.
  End Notations.
End Make.

Definition tell {W R} (w : W) : wc_monad W R unit :=
  WCMonad (fun k => k tt w).

Definition writer {W R A} (m : A * W) : wc_monad W R A :=
  WCMonad (fun k => let (x, w) := m in k x w).

Definition listen {W R A} (m : wc_monad W R A) : wc_monad W R (A * W) :=
  WCMonad (fun k => run_wc_monad m (fun x w => k (x, w) w)).

Definition pass {W R A} (m : wc_monad W R (A * (W -> W))) : wc_monad W R A :=
  WCMonad (fun k => run_wc_monad m (fun '(x, f) w => k x (f w))).

Definition censor {W R A} (f : W -> W) (m : wc_monad W R A) : wc_monad W R A :=
  WCMonad (fun k => run_wc_monad m (fun x w => k x (f w))).

Definition listens {W R A B} (f : W -> B) (m : wc_monad W R A) : wc_monad W R (A * B) :=
  WCMonad (fun k => run_wc_monad m (fun x w => k (x, f w) w)).

Definition map_writer {W W' R A B} (f : A * W -> B * W') (m : wc_monad W R A) : wc_monad W' R B :=
  WCMonad (fun k => run_wc_monad m (fun x w => let (y, w) := f (x, w) in k y w)).

Definition map_cont {W R A} (f : R -> R) (m : wc_monad W R A) : wc_monad W R A :=
  WCMonad (fun k => f (run_wc_monad m k)).

Definition with_cont {W R A B} (f : (B -> R) -> A -> R) (m : wc_monad W R A) : wc_monad W R B :=
  WCMonad (fun k => run_wc_monad m (fun x w => f (fun y => k y w) x)).
