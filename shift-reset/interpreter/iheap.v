From Stdlib Require Import NArith.
From shift_reset.lib Require option.
From shift_reset.core Require Import heap syntax loc.

Local Open Scope N_scope.

Record iheap : Type := IHeap { iheap_car : heap; iheap_next_loc : loc }.

Definition iheap_empty : iheap :=
  IHeap heap_empty (Loc 0).

Definition iheap_ref (v : val) (h : iheap) : option (loc * iheap) :=
  let l := iheap_next_loc h in
  option.map (fun h' => (l, IHeap h' (loc_succ l))) (heap_ref l v (iheap_car h)).

Definition iheap_get (l : loc) (h : iheap) : option val :=
  heap_get l (iheap_car h).

Definition iheap_set (l : loc) (v : val) (h : iheap) : option iheap :=
  option.map (fun h' => IHeap h' (iheap_next_loc h)) (heap_set l v (iheap_car h)).

Definition iheap_free (l : loc) (h : iheap) : option iheap :=
  option.map (fun h' => IHeap h' (iheap_next_loc h)) (heap_free l (iheap_car h)).
