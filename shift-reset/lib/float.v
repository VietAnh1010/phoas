From Stdlib Require Import Qcanon.
From shift_reset.lib Require Import comparison.

Local Open Scope Qc_scope.

Definition Qc_ltb (q1 q2 : Qc) : bool := compare_ltb (q1 ?= q2).
Definition Qc_leb (q1 q2 : Qc) : bool := compare_leb (q1 ?= q2).
Definition Qc_gtb (q1 q2 : Qc) : bool := compare_gtb (q1 ?= q2).
Definition Qc_geb (q1 q2 : Qc) : bool := compare_geb (q1 ?= q2).
Definition Qc_eqb (q1 q2 : Qc) : bool := if Qc_eq_dec q1 q2 then true else false.
Definition Qc_neqb (q1 q2 : Qc) : bool := if Qc_eq_dec q1 q2 then false else true.

Infix "=?" := Qc_eqb (at level 70, no associativity) : Qc_scope.
