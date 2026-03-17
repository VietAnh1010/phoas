From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example incr :=
  <{ fun "x" => "x" <- !"x" + 1 }>.

Example do_toss :=
  <{ fun "x" =>
       shift
         (fun "k" =>
            incr "x";
            let "r1" := "k" true in
            incr "x";
            let "r2" := "k" false in
            "r1" + "r2") }>.

Example toss :=
  <{ fun "x" =>
       reset
         let "r" := do_toss "x" in
         if "r" then 1 else 0 }>.

Example run_toss x :=
  <{ let "x" := ref x in
     let "r" := toss "x" in
     !"x", "r" }>.

Compute (eval_term 4 (run_toss 0)).

Example do_toss_n :=
  <{ fun ("n", "x") =>
       let fix "go" "n" :=
         if "n" = 0 then true
         else
           let "r1" := do_toss "x" in
           let "r2" := "go" ("n" - 1) in
           "r1" && "r2"
       in
       "go" "n" }>.

Example toss_n :=
  <{ fun "args" =>
       reset
         let "r" := do_toss_n "args" in
         if "r" then 1 else 0 }>.

Example run_toss_n n x :=
  <{ let "x" := ref x in
     let "r" := toss_n (n, "x") in
     !"x", "r" }>.

Time Compute (eval_term 100 (run_toss_n 15 0)).
