From Stdlib Require Import NArith.
From shift_reset.lib Require option.
From shift_reset.core Require Import heap syntax loc.

Local Open Scope N_scope.

Record istate : Type := IState { istate_heap : heap; istate_next_loc : loc }.

Definition istate_empty : istate :=
  IState heap_empty (Loc 0).

Definition istate_ref (v : val) (s : istate) : option (loc * istate) :=
  let l := istate_next_loc s in
  option.map (fun h => (l, IState h (loc_succ l))) (heap_ref l v (istate_heap s)).

Definition istate_get (l : loc) (s : istate) : option val :=
  heap_get l (istate_heap s).

Definition istate_set (l : loc) (v : val) (s : istate) : option istate :=
  option.map (fun h => IState h (istate_next_loc s)) (heap_set l v (istate_heap s)).

Definition istate_free (l : loc) (s : istate) : option istate :=
  option.map (fun h => IState h (istate_next_loc s)) (heap_free l (istate_heap s)).
