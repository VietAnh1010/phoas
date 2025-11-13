From Stdlib Require Import String.

Local Unset Elimination Schemes.

Inductive ierror : Type :=
| Failure : string -> ierror
| Type_error : string -> ierror
| Name_error : string -> ierror
| Memory_error : string -> ierror
| Assert_failure : string -> ierror
| Match_failure : string -> ierror
| Undelimited_shift : string -> ierror
| Undelimited_control : string -> ierror
| Unhandled_exception : string -> ierror
| Unhandled_effect : string -> ierror
| Out_of_fuel : ierror.
