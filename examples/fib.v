From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example fib_exponential :=
  <{ fix "go" "n" :=
       if "n" <= 1 then "n"
       else by "go" ("n" - 2) + by "go" ("n" - 1) }>.

Example fib_linear :=
  <{ fun "n" =>
       let fix "go" "n" :=
         if "n" = 0 then (0, 1)
         else
           let ("a", "b") := "go" ("n" - 1) in
           ("b", "a" + "b")
       in
       fst (by "go" "n") }>.

Example fib_logarithmic :=
  <{ fun "n" =>
       let fix "go" "n" :=
         if "n" = 0 then (0, 1)
         else
           let ("a", "b") := "go" ("n" / 2) in
           let "x" := "a" * "a" in
           let "c" := 2 * "a" * "b" - "x" in
           let "d" := "x" + "b" * "b" in
           if "n" mod 2 = 0 then ("c", "d") else ("d", "c" + "d")
       in
       fst (by "go" "n") }>.

Example eval_fib (candidate : val_term) (fuel : nat) (n : Z) :=
  eval_term fuel <{ candidate n }>.

Time Compute (eval_fib fib_linear 1012 1007).
Time Compute (eval_fib fib_logarithmic 1012 1007).
