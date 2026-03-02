From Stdlib Require Import List String ZArith.
From shift_reset.lib Require sum.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
From examples.lib Require Import list.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Definition range (s e : Z) :=
  let fix go s l :=
    match l with
    | O => []
    | S l' => s :: go (s + 1) l'
    end
  in
  go s (Z.to_nat (e - s)).

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
  <{ fix "go" "args" :=
       let ("xs", "ys") := "args" in
       match "xs" with
       | Inl _ => "ys"
       | Inr "p" =>
           let ("x", "xs'") := "p" in
           let "r" := "go" ("xs'", "ys") in
           Inr ("x", "r")
       end }>.

Example append_curry_aux :=
  <{ fix "go" "xs" "ys" :=
       match "xs" with
       | Inl _ => "ys"
       | Inr "p" =>
           let ("x", "xs'") := "p" in
           let "k" := "go" "xs'" in
           let "r" := "k" "ys" in
           Inr ("x", "r")
       end }>.

Example append_curry :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let "k" := append_curry_aux "xs" in
       "k" "ys" }>.

Definition eval_append (candidate : val_term) (fuel : nat) (xs ys : list Z) :=
  eval_term_to_int_list fuel <{ candidate ({int_list_to_val_term xs}, {int_list_to_val_term ys}) }>.

Compute (eval_term 3 <{ append_dcont_aux {int_list_to_val_term []} }>).
Compute (eval_term 4 <{ append_dcont_aux {int_list_to_val_term [1]} }>).
Compute (eval_term 5 <{ append_dcont_aux {int_list_to_val_term [1; 2]} }>).

Compute (eval_append append 2 [] [69]).
Compute (eval_append append 3 [1] [69]).
Compute (eval_append append 4 [1; 2] [69]).
Compute (eval_append append_dcont 4 [] [69]).
Compute (eval_append append_dcont 5 [1] [69]).
Compute (eval_append append_dcont 6 [1; 2] [69]).
Compute (eval_append append_curry 4 [] [69]).
Compute (eval_append append_curry 5 [1] [69]).
Compute (eval_append append_curry 6 [1; 2] [69]).
Time Compute (sum.map (@List.length _) (eval_append append 12800 (range 0 12710) [])).
Time Compute (sum.map (@List.length _) (eval_append append_dcont 12800 (range 0 12710) [])).
Time Compute (sum.map (@List.length _) (eval_append append_curry 12800 (range 0 12710) [])).
