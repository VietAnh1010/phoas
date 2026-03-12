From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From examples Require Import common.
From examples.stdlib Require Import delayed_list.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example fib_it :=
  <{ fun _ =>
       let fix "go" ("a", "b") := Inr ("a", fun _ => "go" ("b", "a" + "b")) in
       "go" (0, 1) }>.

Example fib_it_dcont :=
  <{ fun _ =>
       let fix "go" ("a", "b") :=
         shift (fun "k" => Inr ("a", "k"));
         "go" ("b", "a" + "b")
       in
       reset "go" (0, 1) }>.

Example eval_fib (candidate : val_term) (fuel : nat) (n : Z) :=
  eval_term_to_list_int fuel
  <{ let "DelayedList" := DelayedList in
     let `{"take"; "to_list"; .._} := "DelayedList" in
     let "it" := "take" (n, candidate) in
     "to_list" "it" }>.

Compute (eval_fib fib_it 100 50).
Compute (eval_fib fib_it_dcont 100 50).
