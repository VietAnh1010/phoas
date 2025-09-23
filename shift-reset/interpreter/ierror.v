From Stdlib Require Import String.

Inductive ierror : Type :=
| Stuck : string -> ierror
| OutOfFuel : ierror.
