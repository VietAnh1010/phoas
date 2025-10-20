From Stdlib Require Import String.
From shift_reset Require Import syntax tag var.

Local Unset Elimination Schemes.

Inductive ierror : Type :=
| Failure : string -> ierror
| Type_error : string -> ierror
| Name_error : var -> ierror
| Memory_error : string -> ierror
| Assert_failure : string -> ierror
| Undelimited_shift : tag -> ierror
| Undelimited_control : tag -> ierror
| Unhandled_exception : exn -> ierror
| Unhandled_effect : eff -> ierror
| Out_of_fuel : ierror.
