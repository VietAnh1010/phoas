From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce val.
From examples Require Import common.
From examples.stdlib Require Import delayed_list delayed_tree.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example stern_brocot :=
  <{ fun _ =>
       let fix "go" "args" :=
         let `("a", "b", "x", "y") := "args" in
         let "m" := "a" + "x" in
         let "n" := "b" + "y" in
         let "t1" _ := "go" `("a", "b", "m", "n") in
         let "t2" _ := "go" `("m", "n", "x", "y") in
         Inr `(("m", "n"), "t1", "t2")
       in
       "go" `(0, 1, 1, 0) }>.

Example level :=
  let fix go i n :=
    match n with
    | O => <{ fun _ => Inl () }>
    | S n' => let t := go (i + 1) n' in <{ fun _ => Inr `(i, t, t) }>
    end
  in
  go 0.

Example breadth_it_dcont :=
  <{ fun "t" _ =>
       let "DelayedTree" := DelayedTree in
       let "f" "args" :=
         let `("x", "t1", "t2") := "args" in
         control0 (fun "k" => Inr ("x", fun _ => prompt0 ("k" (); "t1" (); "t2" (); Inl ())))
       in
       let "k" := "DelayedTree".`"fold" `((), "f", "t") in
       prompt0 ("k" (); Inl ()) }>.

Example breadth_it_effect :=
  <{ fun "t" =>
       let "DelayedTree" := DelayedTree in
       let "f" "args" := perform effect "Yield" "args" in
       let "k" := "DelayedTree".`"fold" `((), "f", "t") in
       let fix "go" "k" _ :=
         shallow handle ("k" (); Inl ());;;
         (fun '("Yield" "args"), "k" =>
            let `("x", "t1", "t2") := "args" in
            let "it" := "go" (fun _ => "k" (); "t1" (); "t2" (); Inl ()) in
            Inr ("x", "it"))
       in
       "go" "k" }>.

Example depth_it_dcont :=
  <{ fun "t" _ =>
       let "DelayedTree" := DelayedTree in
       let "f" "x" := shift0 (fun "k" => Inr ("x", "k")) in
       reset0 ("DelayedTree".`"iter" ("f", "t"); Inl ()) }>.

Example depth_it_effect :=
  <{ fun "t" _ =>
       let "DelayedTree" := DelayedTree in
       let "f" "x" := perform effect "Yield" "x" in
       handle ("DelayedTree".`"iter" ("f", "t"); Inl ());;;
       (fun '("Yield" "x"), "k" => Inr ("x", "k")) }>.

Definition eval_it {A} (f : val -> option A) (candidate : val_term) (fuel : nat) (n : Z) (t : val_term) :=
  deep_eval_term_to_list f fuel
  <{ let "DelayedList" := DelayedList in
     let `{"take"; "to_list"; .._} := "DelayedList" in
     let "it" := candidate t in
     let "it" := "take" (n, "it") in
     "to_list" "it" }>.

Definition eval_it_int := eval_it val_to_int.
Definition eval_it_prod_int_int := eval_it val_to_prod_int_int.

Time Compute (eval_it_prod_int_int breadth_it_dcont 17 10 stern_brocot).
Time Compute (eval_it_prod_int_int breadth_it_effect 23 10 stern_brocot).
Time Compute (eval_it_prod_int_int depth_it_dcont 17 10 stern_brocot).
Time Compute (eval_it_prod_int_int depth_it_effect 17 10 stern_brocot).

Time Compute (eval_it_int breadth_it_dcont 23 20 (level 4)).
Time Compute (eval_it_int breadth_it_effect 23 20 (level 4)).
Time Compute (eval_it_int depth_it_dcont 23 20 (level 4)).
Time Compute (eval_it_int depth_it_effect 23 20 (level 4)).
