From Stdlib Require Import String.

Inductive var : Type := Var : string -> var.
Definition unvar (v : var) : string := match v with Var s => s end.
