From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From examples.lib Require Import list.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example fib_it :=
  <{ fun _ =>
       let fix "go" "args" :=
         let ("a", "b") := "args" in
         Inr ("a", fun _ => "go" ("b", "a" + "b"))
       in
       "go" (0, 1) }>.

Example yield := <{ fun "v" => shift (fun "k" => Inr ("v", "k")) }>.

Example fib_it_dcont :=
  <{ fun _ =>
       let fix "go" "args" :=
         let ("a", "b") := "args" in
         yield "a";
         "go" ("b", "a" + "b")
       in
       reset "go" (0, 1) }>.

Example take :=
  <{ fix "go" "args" :=
       let ("n", "it") := "args" in
       if "n" <= 0 then Inl ()
       else
         let "it" := "it" () in
         match "it" with
         | Inl _ => Inl ()
         | Inr "p" =>
             let ("v", "it") := "p" in
             let "vs" := "go" ("n" - 1, "it") in
             Inr ("v", "vs")
         end }>.

Example eval_fib (candidate : val_term) (fuel : nat) (n : Z) :=
  eval_term_to_int_list fuel <{ take (n, candidate) }>.

Compute (eval_fib fib_it 100 50).
Compute (eval_fib fib_it_dcont 100 50).
