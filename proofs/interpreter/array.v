From Stdlib Require Import List.
From shift_reset.core Require Import syntax loc.
From shift_reset.interpreter Require Import array iheap.
Import ListNotations.

Lemma fold_unfold_array_make_alloc_O :
  forall (v : val) (h : iheap), array_make_alloc O v h = h.
Proof. reflexivity. Qed.

Lemma fold_unfold_array_make_alloc_S :
  forall (n' : nat)
         (v : val)
         (h : iheap),
    array_make_alloc (S n') v h =
    array_make_alloc n' v (iheap_alloc v h).
Proof. reflexivity. Qed.

Lemma fold_unfold_array_of_list_alloc_nil :
  forall (h : iheap), array_of_list_alloc [] h = h.
Proof. reflexivity. Qed.

Lemma fold_unfold_array_of_list_alloc_cons :
  forall (v : val)
         (vs' : list val)
         (h : iheap),
    array_of_list_alloc (v :: vs') h =
    array_of_list_alloc vs' (iheap_alloc v h).
Proof. reflexivity. Qed.

Lemma fold_unfold_array_free_dealloc_O :
  forall (l : loc) (h : iheap), array_free_dealloc O l h = Some h.
Proof. reflexivity. Qed.

Lemma fold_unfold_array_free_dealloc_S :
  forall (n' : nat)
         (l : loc)
         (h : iheap),
    array_free_dealloc (S n') l h =
    match iheap_dealloc l h with
    | Some h' => array_free_dealloc n' (loc_succ l) h'
    | None => None
    end.
Proof. reflexivity. Qed.
