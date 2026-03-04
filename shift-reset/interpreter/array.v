From Stdlib Require Import List.
From shift_reset.core Require Import syntax loc.
From shift_reset.interpreter Require Import iheap.
Import ListNotations.

Fixpoint array_make_alloc (n : nat) (v : val) (h : iheap) : iheap :=
  match n with
  | O => h
  | S n' => array_make_alloc n' v (iheap_alloc v h)
  end.

Fixpoint array_of_list_alloc (vs : list val) (h : iheap) : iheap :=
  match vs with
  | [] => h
  | v :: vs' => array_of_list_alloc vs' (iheap_alloc v h)
  end.

Fixpoint array_free_dealloc (n : nat) (l : loc) (h : iheap) : option iheap :=
  match n with
  | O => Some h
  | S n' =>
      match iheap_dealloc l h with
      | Some h' => array_free_dealloc n' (loc_succ l) h'
      | None => None
      end
  end.
