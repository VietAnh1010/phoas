From shift_reset.lib Require gmap.
From shift_reset.core Require Import syntax loc.

Record iheap : Type := IHeap { iheap_car : gmap.t loc val; iheap_next_loc : loc }.

Definition iheap_empty : iheap :=
  IHeap gmap.empty loc_one.

Definition iheap_alloc (v : val) (h : iheap) : loc * iheap :=
  let (m, l) := h in (l, IHeap (LocMap.add l v m) (loc_succ l)).

Definition iheap_alloc_n (n : nat) (v : val) (h : iheap) : loc * iheap :=
  let fix go n m l :=
    match n with
    | O => IHeap m l
    | S n' => go n' (LocMap.add l v m) (loc_succ l)
    end
  in
  let (m, l) := h in (l, go n m l).

Definition iheap_alloc_vals (vs : vals) (h : iheap) : loc * iheap :=
  let fix go vs m l :=
    match vs with
    | VsNil => IHeap m l
    | VsCons v vs' => go vs' (LocMap.add l v m) (loc_succ l)
    end
  in
  let (m, l) := h in (l, go vs m l).

Definition iheap_read (l : loc) (h : iheap) : option val :=
  LocMap.find l (iheap_car h).

Definition iheap_write (l : loc) (v : val) (h : iheap) : option iheap :=
  let (m, l') := h in if LocMap.member l m then Some (IHeap (LocMap.add l v m) l') else None.

Definition iheap_dealloc (l : loc) (h : iheap) : option iheap :=
  let (m, l') := h in if LocMap.member l m then Some (IHeap (LocMap.remove l m) l') else None.

Fixpoint iheap_dealloc_n (n : nat) (l : loc) (h : iheap) : option iheap :=
  match n with
  | O => Some h
  | S n' =>
      match iheap_dealloc l h with
      | None => None
      | Some h => iheap_dealloc_n n' (loc_succ l) h
      end
  end.
