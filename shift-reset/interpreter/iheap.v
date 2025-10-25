From shift_reset.lib Require option.
From shift_reset.core Require Import syntax heap loc.

Record iheap : Type := IHeap { iheap_car : heap; iheap_next_loc : loc }.

Definition iheap_empty : iheap :=
  IHeap heap_empty loc_init.

Definition iheap_ref (v : val) (h : iheap) : option (loc * iheap) :=
  let (h, l) := h in
  option.map (fun h' => (l, IHeap h' (loc_succ l))) (heap_ref l v h).

Definition iheap_get (l : loc) (h : iheap) : option val :=
  heap_get l (iheap_car h).

Definition iheap_set (l : loc) (v : val) (h : iheap) : option iheap :=
  let (h, l) := h in
  option.map (fun h' => IHeap h' l) (heap_set l v h).

Definition iheap_free (l : loc) (h : iheap) : option iheap :=
  let (h, l) := h in
  option.map (fun h' => IHeap h' l) (heap_free l h).
