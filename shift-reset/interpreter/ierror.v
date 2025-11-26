From Stdlib Require Import String.

Local Unset Elimination Schemes.

Inductive ierror : Type :=
| Failure : string -> ierror
| Type_error : string -> ierror
| Name_error : string -> ierror
| Memory_error : string -> ierror
| Assert_failure : string -> ierror
| Match_failure : string -> ierror
| Invalid_argument : string -> ierror
| Unhandled_exception : string -> ierror
| Unhandled_effect : string -> ierror
| Division_by_zero : ierror
| Undelimited_shift : ierror
| Undelimited_control : ierror
| Out_of_fuel : ierror.
