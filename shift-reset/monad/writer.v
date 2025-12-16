From shift_reset.lib Require Import monoid_sig.

Record writer (W A : Type) : Type := Writer { run_writer : A * W }.
Definition t : Type -> Type -> Type := writer.

Arguments Writer {W A} _.
Arguments run_writer {W A} _.

Definition map {W A B} (f : A -> B) (m : writer W A) : writer W B :=
  Writer (let (x, w) := run_writer m in (f x, w)).

Definition mapl {W A B} (x : B) (m : writer W A) : writer W B :=
  Writer (let (_, w) := run_writer m in (x, w)).

Module Make (M : Monoid).
  Definition w : Type := M.t.
  Definition t : Type -> Type := writer w.

  Definition pure {A} (x : A) : writer w A :=
    Writer (x, M.empty).

  Definition app {A B} (m1 : writer w (A -> B)) (m2 : writer w A) : writer w B :=
    Writer (let (f, w1) := run_writer m1 in let (x, w2) := run_writer m2 in (f x, M.append w1 w2)).

  Definition appl {A B} (m1 : writer w A) (m2 : writer w B) : writer w A :=
    Writer (let (x, w1) := run_writer m1 in let (_, w2) := run_writer m2 in (x, M.append w1 w2)).

  Definition appr {A B} (m1 : writer w A) (m2 : writer w B) : writer w B :=
    Writer (let (_, w1) := run_writer m1 in let (x, w2) := run_writer m2 in (x, M.append w1 w2)).

  Definition bind {A B} (m : writer w A) (f : A -> writer w B) : writer w B :=
    Writer (let (x, w1) := run_writer m in let (y, w2) := run_writer (f x) in (y, M.append w1 w2)).

  Definition join {A} (m : writer w (writer w A)) : writer w A :=
    Writer (let (m, w1) := run_writer m in let (x, w2) := run_writer m in (x, M.append w1 w2)).
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
