From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From examples Require Import common.
From examples.stdlib Require Import list.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example powerset_filter :=
  <{ fun "xs" =>
       let "List" := List in
       let "r" := ref [] in
       let "f" "_" := shift (fun "k" => "k" true; "k" false) in
       let _ :=
         reset
           (let "s" := "List".`"filter" ("f", "xs") in
            "r" <- "s" :: !"r")
       in
       !"r" }>.

Example powerset_fold_right :=
  <{ fun "xs" =>
       let "List" := List in
       let "r" := ref [] in
       let "f" ("x", "s") :=
         let "b" := shift (fun "k" => "k" true; "k" false) in
         if "b" then "x" :: "s" else "s"
       in
       let _ :=
         reset
           (let "s" := "List".`"fold_right" `("f", [], "xs") in
            "r" <- "s" :: !"r")
       in
       !"r" }>.

Example powerset_fold_left :=
  <{ fun "xs" =>
       let "List" := List in
       let "r" := ref [] in
       let "f" ("s", "x") :=
         let "b" := shift (fun "k" => "k" true; "k" false) in
         if "b" then "x" :: "s" else "s"
       in
       let _ :=
         reset
           (let "s" := "List".`"fold_left" `("f", [], "xs") in
            "r" <- "s" :: !"r")
       in
       !"r" }>.

Definition eval_powerset (candidate : expr) (fuel : nat) (xs : list Z) :=
  deep_eval_comp_to_list val_to_list_int fuel <{ candidate {list_int_to_expr xs} }>.

Time Compute (eval_powerset powerset_filter 1010 (range 0 4)).
Time Compute (eval_powerset powerset_fold_left 1010 (range 0 4)).
Time Compute (eval_powerset powerset_fold_right 1010 (range 0 4)).
