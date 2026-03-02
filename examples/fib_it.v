From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example yield := <{ fun "v" => shift (fun "k" => Inr ("v", "k")) }>.

Example fib_it :=
  <{ fun _ =>
       let fix "go" "args" :=
         let ("a", "b") := "args" in
         let _ := yield "a" in
         "go" ("b", "a" + "b")
       in reset ("go" (0, 1); Inl ()) }>.

Example take_n :=
  <{ fix "go" "args" :=
       let ("n", "it") := "args" in
       if "n" <= 0 then Inl () else
         (match "it" with
          | Inl _ => Inl ()
          | Inr "p" =>
              let ("v", "k") := "p" in
              let "it" := "k" () in
              let "vs" := "go" ("n" - 1, "it") in
              Inr ("v", "vs")
          end) }>.

Example run_fib n :=
  <{ let "it" := fib_it () in
     take_n (n, "it") }>.

Compute (eval_term 100 (run_fib 10)).
