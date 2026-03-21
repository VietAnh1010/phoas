From shift_reset.lib Require Import signatures.

Record writer (W A : Type) : Type := Writer { run_writer : A * W }.
Definition t : Type -> Type -> Type := writer.

Arguments Writer {W A} _.
Arguments run_writer {W A} _.

Definition map {W A B} (f : A -> B) (m : writer W A) : writer W B :=
  Writer (let (x, w) := run_writer m in (f x, w)).

Definition mapl {W A B} (x : B) (m : writer W A) : writer W B :=
  Writer (let (_, w) := run_writer m in (x, w)).

Module WriterNotations.
  Declare Scope writer_scope.
  Delimit Scope writer_scope with writer.
  Bind Scope writer_scope with writer.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : writer_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : writer_scope.
  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : writer_scope.
End WriterNotations.

Module Make (W : Monoid).
  Definition pure {A} (x : A) : writer W.t A :=
    Writer (x, W.empty).

  Definition app {A B} (m1 : writer W.t (A -> B)) (m2 : writer W.t A) : writer W.t B :=
    Writer (let (f, w1) := run_writer m1 in let (x, w2) := run_writer m2 in (f x, W.append w1 w2)).

  Definition appl {A B} (m1 : writer W.t A) (m2 : writer W.t B) : writer W.t A :=
    Writer (let (x, w1) := run_writer m1 in let (_, w2) := run_writer m2 in (x, W.append w1 w2)).

  Definition appr {A B} (m1 : writer W.t A) (m2 : writer W.t B) : writer W.t B :=
    Writer (let (_, w1) := run_writer m1 in let (x, w2) := run_writer m2 in (x, W.append w1 w2)).

  Definition bind {A B} (m : writer W.t A) (f : A -> writer W.t B) : writer W.t B :=
    Writer (let (x, w1) := run_writer m in let (y, w2) := run_writer (f x) in (y, W.append w1 w2)).

  Definition join {A} (m : writer W.t (writer W.t A)) : writer W.t A :=
    Writer (let (m, w1) := run_writer m in let (x, w2) := run_writer m in (x, W.append w1 w2)).

  Module Notations.
    Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : writer_scope.
    Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : writer_scope.
    Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : writer_scope.
    Notation "m >>= f" := (bind m f) (at level 50, left associativity) : writer_scope.
    Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : writer_scope.
  End Notations.
End Make.

Definition tell {W} (w : W) : writer W unit :=
  Writer (tt, w).

Definition listen {W A} (m : writer W A) : writer W (A * W) :=
  Writer (let (x, w) := run_writer m in (x, w, w)).

Definition pass {W A} (m : writer W (A * (W -> W))) : writer W A :=
  Writer (let '(x, f, w) := run_writer m in (x, f w)).

Definition censor {W A} (f : W -> W) (m : writer W A) : writer W A :=
  Writer (let (x, w) := run_writer m in (x, f w)).

Definition listens {W A B} (f : W -> B) (m : writer W A) : writer W (A * B) :=
  Writer (let (x, w) := run_writer m in (x, f w, w)).

Definition map_writer {W W' A B} (f : A * W -> B * W') (m : writer W A) : writer W' B :=
  Writer (f (run_writer m)).
