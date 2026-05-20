From Stdlib Require Import List Arith FunctionalExtensionality.
From shift_reset.monad Require Import lc_monad.
From proofs.monad Require Import lc_monad.

Import ListNotations.
Import LCMonadNotations.
Local Open Scope lc_monad_scope.

Example example {R} : lc_monad R _ :=
  callcc
    (fun k =>
       let* x := of_list [1; 2; 100] in
       let* y := of_list [3; 4] in
       let* _ := if x =? 2 then k (0, 0, 0) else pure tt in
       let* z := of_list [5; 6] in
       pure (x, y, z)).

Example example' {R} : lc_monad R _ :=
  callcc'
    (fun k =>
       let* x := of_list [1; 2; 100] in
       let* y := of_list [3; 4] in
       let* _ := if x =? 2 then k (0, 0, 0) else pure tt in
       let* z := of_list [5; 6] in
       pure (x, y, z)).

Check (run_lc_monad example [] List.cons).
Compute (run_lc_monad example [] List.cons).
Compute (run_lc_monad example' [] List.cons).

Example example_lift {R} : lc_monad R _ :=
  let* x := of_list [1; 2; 100] in
  let* y := of_list [3; 4] in
  callcc
    (fun k =>
       let* _ := if x =? 2 then k (0, 0, 0) else pure tt in
       let* z := of_list [5; 6] in
       pure (x, y, z)).

Example example'_lift {R} : lc_monad R _ :=
  let* x := of_list [1; 2; 100] in
  let* y := of_list [3; 4] in
  callcc'
    (fun k =>
       let* _ := if x =? 2 then k (0, 0, 0) else pure tt in
       let* z := of_list [5; 6] in
       pure (x, y, z)).

Compute (run_lc_monad example_lift [] List.cons).
Compute (run_lc_monad example'_lift [] List.cons).

Lemma example'_eq_example'_lift {R} : @example' R = example'_lift.
Proof.
  unfold example', example'_lift.
  rewrite -> callcc'_bind.
  apply f_equal. apply functional_extensionality. intros x.
  rewrite -> callcc'_bind.
  reflexivity.
Qed.
