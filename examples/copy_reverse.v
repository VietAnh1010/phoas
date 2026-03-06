From Stdlib Require Import List String ZArith.
From shift_reset.lib Require sum.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
From examples.lib Require Import list.
From examples.stdlib Require Import lazy queue.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example copy_dcont :=
  <{ fun "xs" =>
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => Inl ()
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "r" := shift (fun "k" => let "r" := "k" "xs'" in Inr ("x", "r")) in
             "go" "r"
         end
       in
       reset "go" "xs" }>.

Example copy :=
  <{ fix "go" "xs" :=
       match "xs" with
       | Inl _ => Inl ()
       | Inr "p" =>
           let ("x", "xs'") := "p" in
           let "r" := "go" "xs'" in
           Inr ("x", "r")
       end }>.

Example reverse_dcont :=
  <{ fun "xs" =>
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => Inl ()
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "r" := control (fun "k" => let "r" := "k" "xs'" in Inr ("x", "r")) in
             "go" "r"
         end
       in
       prompt "go" "xs" }>.

Example reverse :=
  <{ fun "xs" =>
       let fix "go" "args" :=
         let ("xs", "acc") := "args" in
         match "xs" with
         | Inl _ => "acc"
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             "go" ("xs'", Inr ("x", "acc"))
         end
       in
       "go" ("xs", Inl ()) }>.

Example reverse_while :=
  <{ fun "xs" =>
       let "in" := ref "xs" in
       let "out" := ref (Inl ()) in
       try
         (while true do
            (match !"in" with
             | Inl _ => raise exception "Exit" ()
             | Inr "p" =>
                 let ("x", "xs'") := "p" in
                 "in" <- "xs'";
                 "out" <- Inr ("x", !"out")
             end));;
       (fun '("Exit" _) =>
          let "r" := !"out" in
          {TVBuiltin1 "ref_free" "in"};
          {TVBuiltin1 "ref_free" "out"};
          "r") }>.

Example reverse_queue :=
  <{ fun "xs" =>
       let "Lazy" := Lazy in
       let "Queue" := Queue in
       let fix "go_snoc" "args" :=
         let ("q", "xs") := "args" in
         match "xs" with
         | Inl _ => "q"
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "q'" := "Queue".`"snoc" ("q", "x") in
             "go_snoc" ("q'", "xs'")
         end
       in
       let fix "go_uncons" "args" :=
         let ("q", "acc") := "args" in
         let "b" := "Queue".`"is_empty" "q" in
         if "b" then "acc"
         else
           let "p" := "Queue".`"uncons" "q" in
           let ("x", "q'") := "p" in
           "go_uncons" ("q'", Inr ("x", "acc"))
       in
       let "q" := "go_snoc" ("Queue".`"empty", "xs") in
       "go_uncons" ("q", Inl ()) }>.

Definition eval_fun (candidate : val_term) (fuel : nat) (xs : list Z) :=
  eval_term_to_list_int fuel <{ candidate {list_int_to_val_term xs} }>.

Time Compute (eval_fun copy 1010 (range 0 1000)).
Time Compute (eval_fun copy_dcont 2003 (range 0 1000)).
Time Compute (eval_fun reverse 1010 (range 0 1000)).
Time Compute (eval_fun reverse_dcont 2003 (range 0 1000)).
Time Compute (eval_fun reverse_while 1010 (range 0 1000)).
Time Compute (eval_fun reverse_queue 1010 (range 0 1000)).
