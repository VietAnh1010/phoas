From Stdlib Require Import String.

Local Unset Elimination Schemes.

Inductive ierror : Type :=
| TypeError : string -> ierror
| NameError : string -> ierror
| MemoryError : string -> ierror
| ControlError : string -> ierror
| OutOfFuel : ierror.
