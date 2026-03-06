From Stdlib Require Import List String ZArith.
From shift_reset.lib Require sum.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
From examples.lib Require Import list.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example append_dcont_aux :=
  <{ fun "xs" =>
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => shift (fun "k" => "k")
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "r" := "go" "xs'" in
             Inr ("x", "r")
         end
       in
       reset "go" "xs" }>.

Example append_dcont :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let "k" := append_dcont_aux "xs" in
       "k" "ys" }>.

Example append :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => "ys"
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "r" := "go" "xs'" in
             Inr ("x", "r")
         end
       in
       "go" "xs" }>.

Definition eval_append (candidate : val_term) (fuel : nat) (xs ys : list Z) :=
  eval_term_to_list_int fuel <{ candidate ({list_int_to_val_term xs}, {list_int_to_val_term ys}) }>.

Compute (eval_term 3 <{ append_dcont_aux {list_int_to_val_term []} }>).
Compute (eval_term 4 <{ append_dcont_aux {list_int_to_val_term [1]} }>).
Compute (eval_term 5 <{ append_dcont_aux {list_int_to_val_term [1; 2]} }>).

Compute (eval_append append 2 [] [69]).
Compute (eval_append append 3 [1] [69]).
Compute (eval_append append 4 [1; 2] [69]).
Compute (eval_append append_dcont 4 [] [69]).
Compute (eval_append append_dcont 5 [1] [69]).
Compute (eval_append append_dcont 6 [1; 2] [69]).
Time Compute (sum.map (@List.length _) (eval_append append 12800 (range 0 12710) [])).
Time Compute (sum.map (@List.length _) (eval_append append_dcont 12800 (range 0 12710) [])).
