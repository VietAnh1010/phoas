From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce val.
From examples Require Import common.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example prefixes_cont :=
  <{ fun "xs" =>
       let fix "go" ("xs", "k") :=
         Inr (
             by "k" (Inl ()),
             by (match "xs" with
                 | Inl _ => Inl ()
                 | Inr ("x", "xs'") => "go" ("xs'", fun "t" => "k" (Inr ("x", "t")))
                 end))
       in
       "go" ("xs", fun "t" => "t") }>.

Example prefixes_dcont :=
  <{ fun "xs" =>
       let fix "go" "xs" :=
         control0
           (fun "k" =>
              Inr (
                  by "k" (Inl ()),
                  by (match "xs" with
                      | Inl _ => Inl ()
                      | Inr ("x", "xs'") => prompt0 let "t" := "go" "xs'" in "k" (Inr ("x", "t"))
                      end)))
       in
       prompt0 "go" "xs" }>.

Definition eval_prefixes (candidate : val_term) (fuel : nat) (xs : list Z) :=
  deep_eval_term_to_list val_to_list_int fuel <{ candidate {list_int_to_val_term xs} }>.

Time Compute (eval_prefixes prefixes_cont 100 []).
Time Compute (eval_prefixes prefixes_cont 100 [0]).
Time Compute (eval_prefixes prefixes_cont 100 [0; 1]).
Time Compute (eval_prefixes prefixes_cont 100 [0; 1; 2]).

Time Compute (eval_prefixes prefixes_dcont 100 []).
Time Compute (eval_prefixes prefixes_dcont 100 [0]).
Time Compute (eval_prefixes prefixes_dcont 100 [0; 1]).
Time Compute (eval_prefixes prefixes_dcont 100 [0; 1; 2]).
