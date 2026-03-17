From Stdlib Require Import List String ZArith.
From shift_reset.lib Require sum.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
From examples Require Import common.
From examples.stdlib Require Import list.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example copy_dcont :=
  <{ fun "xs" =>
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => Inl ()
         | Inr ("x", "xs'") =>
             let "r" := shift (fun "k" => Inr ("x", by "k" "xs'")) in
             "go" "r"
         end
       in
       reset "go" "xs" }>.

Example copy :=
  <{ fix "go" "xs" :=
       match "xs" with
       | Inl _ => Inl ()
       | Inr ("x", "xs'") => Inr ("x", by "go" "xs'")
       end }>.

Example reverse_dcont :=
  <{ fun "xs" =>
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => Inl ()
         | Inr ("x", "xs'") =>
             let "r" := control (fun "k" => let "r" := "k" "xs'" in Inr ("x", "r")) in
             "go" "r"
         end
       in
       prompt "go" "xs" }>.

Example reverse :=
  <{ fun "xs" =>
       let fix "go" ("xs", "acc") :=
         match "xs" with
         | Inl _ => "acc"
         | Inr ("x", "xs'") => "go" ("xs'", Inr ("x", "acc"))
         end
       in
       "go" ("xs", Inl ()) }>.

Example reverse_while :=
  <{ fun "xs" =>
       let "List" := List in
       let "in" := ref "xs" in
       let "out" := ref (Inl ()) in
       let _ :=
         while not by "List".`"is_empty" !"in" do
           let ("x", "xs'") := "List".`"ne_uncons" !"in" in
           "in" <- "xs'";
           "out" <- Inr ("x", !"out")
       in
       !"out" }>.

Example reverse_taba :=
  <{ fun "xs" =>
       let fix "go" "xs_t" :=
         match "xs_t" with
         | Inl _ => ("xs", Inl ())
         | Inr (_, "xs_t'") =>
             let (Inr ("x", "xs_b"), "r") := "go" "xs_t'" in
             ("xs_b", Inr ("x", "r"))
         end
       in
       snd (by "go" "xs") }>.

Definition eval_fun (candidate : val_term) (fuel : nat) (xs : list Z) :=
  eval_term_to_list_int fuel <{ candidate {list_int_to_val_term xs} }>.

Time Compute (eval_fun copy 1010 (range 0 1000)).
Time Compute (eval_fun copy_dcont 2003 (range 0 1000)).
Time Compute (eval_fun reverse 1010 (range 0 1000)).
Time Compute (eval_fun reverse_dcont 2003 (range 0 1000)).
Time Compute (eval_fun reverse_while 1010 (range 0 1000)).
Time Compute (eval_fun reverse_taba 1010 (range 0 1000)).
