From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter error.
From examples.lib Require Import list.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example zip_reverse_r :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => ("ys", Inl ())
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "p" := "go" "xs'" in
             let ("ys_r", "r") := "p" in
             match "ys_r" with
             | Inl _ => "p"
             | Inr "p" =>
                 let ("y", "ys_r'") := "p" in
                 ("ys_r'", Inr (("x", "y"), "r"))
             end
         end
       in
       let "p" := "go" "xs" in
       snd "p" }>.

Example zip_reverse_r' :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let fix "go" "args" :=
         let ("ys", "k") := "args" in
         match "ys" with
         | Inl _ => "k"
         | Inr "p" =>
             let ("y", "ys'") := "p" in
             "go" ("ys'", fun "xs" =>
                            match "xs" with
                            | Inl _ => Inl ()
                            | Inr "p" =>
                                let ("x", "xs'") := "p" in
                                let "r" := "k" "xs'" in
                                Inr (("x", "y"), "r")
                            end)
         end
       in
       let "k" := "go" ("ys", fun _ => Inl ()) in
       "k" "xs" }>.

Definition eval_zip_reverse_r (candidate : val_term) (fuel : nat) (xs ys : list Z) :=
  eval_term_to_list
    (fun v => match v with
              | VPair (VInt z1) (VInt z2) => inr (z1, z2)
              | _ => inl (Reflect_failure v)
              end)
    fuel <{ candidate ({list_int_to_val_term xs}, {list_int_to_val_term ys}) }>.

Compute (eval_zip_reverse_r zip_reverse_r 100 [1; 2] [3; 4]).
Compute (eval_zip_reverse_r zip_reverse_r' 100 [1; 2] [3; 4]).
