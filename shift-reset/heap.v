From Stdlib Require Import FMapAVL.
From shift_reset Require Import loc syntax.

Module M := Make(LocOrderedType).

Definition heap : Type := M.t val.

Print M.

Definition empty : heap := @M.empty val.
Definition get (l : loc) (h : heap) : option val := M.find l h.
Definition set (l : loc) (v : val) (h : heap) : heap := M.add l v h.

Compute (set (Loc 1) (val_loc (Loc 2)) (set (Loc 1) val_unit empty)).
