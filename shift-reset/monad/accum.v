From shift_reset.lib Require Import signatures.

Record accum (W A : Type) : Type := Accum { run_accum : W -> A * W }.
Definition t : Type -> Type -> Type := accum.

Arguments Accum {W A} _.
Arguments run_accum {W A} _ _.

Definition map {W A B} (f : A -> B) (m : accum W A) : accum W B :=
  Accum (fun w => let (x, w) := run_accum m w in (f x, w)).

Definition mapl {W A B} (x : B) (m : accum W A) : accum W B :=
  Accum (fun w => let (_, w) := run_accum m w in (x, w)).

Module AccumNotations.
  Declare Scope accum_scope.
  Delimit Scope accum_scope with accum.
  Bind Scope accum_scope with accum.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : accum_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : accum_scope.
  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : accum_scope.
End AccumNotations.

Module Make (M : Monoid).
  Definition w : Type := M.t.
  Definition t : Type -> Type := accum w.

  Definition pure {A} (x : A) : accum w A :=
    Accum (fun _ => (x, M.empty)).

  Definition app {A B} (m1 : accum w (A -> B)) (m2 : accum w A) : accum w B :=
    Accum (fun w => let (f, w1) := run_accum m1 w in let (x, w2) := run_accum m2 (M.append w w1) in (f x, M.append w1 w2)).

  Definition appl {A B} (m1 : accum w A) (m2 : accum w B) : accum w A :=
    Accum (fun w => let (x, w1) := run_accum m1 w in let (_, w2) := run_accum m2 (M.append w w1) in (x, M.append w1 w2)).

  Definition appr {A B} (m1 : accum w A) (m2 : accum w B) : accum w B :=
    Accum (fun w => let (_, w1) := run_accum m1 w in let (x, w2) := run_accum m2 (M.append w w1) in (x, M.append w1 w2)).

  Definition bind {A B} (m : accum w A) (f : A -> accum w B) : accum w B :=
    Accum (fun w => let (x, w1) := run_accum m w in let (y, w2) := run_accum (f x) (M.append w w1) in (y, M.append w1 w2)).

  Definition join {A} (m : accum w (accum w A)) : accum w A :=
    Accum (fun w => let (m, w1) := run_accum m w in let (x, w2) := run_accum m (M.append w w1) in (x, M.append w1 w2)).

  Definition look : accum w w :=
    Accum (fun w => (w, M.empty)).

  Definition looks {A} (f : w -> A) : accum w A :=
    Accum (fun w => (f w, M.empty)).

  Module Notations.
    Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : accum_scope.
    Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : accum_scope.
    Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : accum_scope.
    Notation "m >>= f" := (bind m f) (at level 50, left associativity) : accum_scope.
    Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : accum_scope.
  End Notations.
End Make.

Definition add {W} (w : W) : accum W unit :=
  Accum (fun _ => (tt, w)).

Definition map_accum {W A B} (f : A * W -> B * W) (m : accum W A) : accum W B :=
  Accum (fun w => f (run_accum m w)).
