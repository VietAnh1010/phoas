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

Example append_dcont_aux :=
  <{ fun "xs" =>
       let fix "go" "xs" :=
         match "xs" with
         | [] => shift (fun "k" => "k")
         | "x" :: "xs'" =>
             let "r" := "go" "xs'" in
             "x" :: "r"
         end
       in
       reset ("go" "xs") }>.

Example append_dcont :=
  <{ fun ("xs", "ys") => by (append_dcont_aux "xs") "ys" }>.

Example append :=
  <{ (by List).`"append" }>.

Definition eval_append (candidate : expr) (fuel : nat) (xs ys : list Z) :=
  eval_comp_to_list_int fuel <{ candidate ({list_int_to_expr xs}, {list_int_to_expr ys}) }>.

Compute (eval_comp 3 <{ append_dcont_aux {list_int_to_expr []} }>).
Compute (eval_comp 4 <{ append_dcont_aux {list_int_to_expr [1]} }>).
Compute (eval_comp 5 <{ append_dcont_aux {list_int_to_expr [1; 2]} }>).

Compute (eval_append append 3 [] [69]).
Compute (eval_append append 4 [1] [69]).
Compute (eval_append append 5 [1; 2] [69]).
Compute (eval_append append_dcont 4 [] [69]).
Compute (eval_append append_dcont 5 [1] [69]).
Compute (eval_append append_dcont 6 [1; 2] [69]).
Time Compute (sum.map (@List.length _) (eval_append append 12800 (range 0 12710) [])).
Time Compute (sum.map (@List.length _) (eval_append append_dcont 12800 (range 0 12710) [])).
