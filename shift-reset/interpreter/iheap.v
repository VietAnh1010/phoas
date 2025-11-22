From shift_reset.core Require Import syntax loc.

Record iheap : Type := IHeap { iheap_car : LocMap.t val; iheap_next_loc : loc }.

Definition iheap_empty : iheap :=
  IHeap LocMap.empty loc_init.

Definition iheap_alloc (v : val) (h : iheap) : iheap :=
  let (m, l) := h in IHeap (LocMap.insert l v m) (loc_succ l).

Definition iheap_read (l : loc) (h : iheap) : option val :=
  LocMap.lookup l (iheap_car h).

Definition iheap_write (l : loc) (v : val) (h : iheap) : option iheap :=
  let (m, l') := h in
  if LocMap.member l m then Some (IHeap (LocMap.insert l v m) l') else None.

Definition iheap_dealloc (l : loc) (h : iheap) : option iheap :=
  let (m, l') := h in
  if LocMap.member l m then Some (IHeap (LocMap.remove l m) l') else None.
