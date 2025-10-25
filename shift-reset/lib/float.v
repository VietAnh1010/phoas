From Stdlib Require Import Qcanon.
From shift_reset.lib Require Import comparison.

Definition Qc_ltb (q1 q2 : Qc) : bool := compare_ltb (q1 ?= q2).
Definition Qc_leb (q1 q2 : Qc) : bool := compare_leb (q1 ?= q2).
Definition Qc_gtb (q1 q2 : Qc) : bool := compare_gtb (q1 ?= q2).
Definition Qc_geb (q1 q2 : Qc) : bool := compare_geb (q1 ?= q2).
Definition Qc_neqb (q1 q2 : Qc) : bool := negb (Qc_eq_bool q1 q2).
