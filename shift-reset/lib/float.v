From Stdlib Require Import QArith Qcanon.
From shift_reset.lib Require Import compare.

Local Open Scope Qc_scope.
Local Open Scope lazy_bool_scope.

Definition Qc_ltb (q1 q2 : Qc) : bool := compare_ltb (q1 ?= q2).
Definition Qc_leb (q1 q2 : Qc) : bool := compare_leb (q1 ?= q2).
Definition Qc_gtb (q1 q2 : Qc) : bool := compare_gtb (q1 ?= q2).
Definition Qc_geb (q1 q2 : Qc) : bool := compare_geb (q1 ?= q2).
Definition Qc_eqb (q1 q2 : Qc) : bool := Z.eqb (Qnum q1) (Qnum q2) &&& Pos.eqb (Qden q1) (Qden q2).
Definition Qc_neqb (q1 q2 : Qc) : bool := negb (Qc_eqb q1 q2).
Definition Qc_pow (q : Qc) (z : Z) : Qc := Q2Qc (Qpower q z).

Infix "=?" := Qc_eqb (at level 70, no associativity) : Qc_scope.
