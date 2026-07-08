From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce val.
From examples Require Import common.
From examples.stdlib Require Import delayed_list delayed_tree queue stack.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Fixpoint level n :=
  match n with
  | O => <{ Inl 0 }>
  | S n' => let t := level n' in <{ Inr (t, t) }>
  end.

Example iter :=
  <{ fun ("f", "t") =>
       let fix "go" "t" :=
         match "t" with
         | Inl "x" => "f" "x"
         | Inr ("l", "r") => "go" "l"; "go" "r"
         end
       in
       "go" "t" }>.

Example persistent_it :=
  <{ fun "t" =>
       let "f" "x" := shift (fun "k" => Inr ("x", "k")) in
       fun () => reset (iter ("f", "t"); Inl ()) }>.

Example ephemeral_it :=
  <{ fun "t" =>
       let "r" := ref () in
       let "f" "x" := shift (fun "k" => "r" <- "k"; Inr "x") in
       let _ := "r" <- fun () => reset (iter ("f", "t"); Inl ()) in
       fun () => !"r" () }>.

Definition eval_persistent_it (fuel : nat) (t : val_term) :=
  eval_term_to_list_int fuel <{ (by DelayedList).`"to_list" (by persistent_it t) }>.

Definition eval_ephemeral_it (fuel : nat) (t : val_term) :=
  eval_term_to_list_int fuel
  <{ let fix "to_list" "it" :=
       match by "it" () with
       | Inl _ => Inl ()
       | Inr "x" => Inr ("x", by "to_list" "it")
       end
     in
     "to_list" (by ephemeral_it t) }>.

Time Compute (eval_persistent_it 100 (level 5)).
Time Compute (eval_ephemeral_it 100 (level 5)).
