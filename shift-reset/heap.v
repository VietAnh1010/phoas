From Stdlib Require Import NArith.
From shift_reset Require Import loc syntax option.

Local Open Scope N_scope.

Record heap : Type := Heap { heap_car : LocMap.t val }.

Definition empty : heap := Heap LocMap.empty.

Definition singleton (l : loc) (v : val) : heap :=
  Heap (LocMap.singleton l v).

Definition get (l : loc) (h : heap) : option val :=
  LocMap.lookup l (heap_car h).

Definition mem (l : loc) (h : heap) : bool :=
  LocMap.member l (heap_car h).

Definition unsafe_put (l : loc) (v : val) (h : heap) : heap :=
  Heap (LocMap.insert l v (heap_car h)).

Definition unsafe_del (l : loc) (h : heap) : heap :=
  Heap (LocMap.remove l (heap_car h)).

Definition ref (l : loc) (v : val) (h : heap) : option heap :=
  if mem l h then None else Some (unsafe_put l v h).

Definition set (l : loc) (v : val) (h : heap) : option heap :=
  if mem l h then Some (unsafe_put l v h) else None.

Definition free (l : loc) (h : heap) : option heap :=
  if mem l h then Some (unsafe_del l h) else None.
