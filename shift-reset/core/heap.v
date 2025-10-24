From shift_reset.lib Require Import option.
From shift_reset.core Require Import syntax loc.

Record heap : Type := Heap { heap_car : LocMap.t val }.

Definition heap_empty : heap := Heap LocMap.empty.

Definition heap_singleton (l : loc) (v : val) : heap :=
  Heap (LocMap.singleton l v).

Definition heap_get (l : loc) (h : heap) : option val :=
  LocMap.lookup l (heap_car h).

Definition heap_mem (l : loc) (h : heap) : bool :=
  LocMap.member l (heap_car h).

Definition heap_unsafe_put (l : loc) (v : val) (h : heap) : heap :=
  Heap (LocMap.insert l v (heap_car h)).

Definition heap_unsafe_del (l : loc) (h : heap) : heap :=
  Heap (LocMap.remove l (heap_car h)).

Definition heap_ref (l : loc) (v : val) (h : heap) : option heap :=
  if heap_mem l h then None else Some (heap_unsafe_put l v h).

Definition heap_set (l : loc) (v : val) (h : heap) : option heap :=
  if heap_mem l h then Some (heap_unsafe_put l v h) else None.

Definition heap_free (l : loc) (h : heap) : option heap :=
  if heap_mem l h then Some (heap_unsafe_del l h) else None.
