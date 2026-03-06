From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter error.
From examples.lib Require Import list.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example convolve_cont :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let fix "go" "args" :=
         let ("ys", "k") := "args" in
         match "ys" with
         | Inl _ => "k" "xs"
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
       "go" ("ys", fun _ => Inl ()) }>.

Example convolve_dcont :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let fix "go" "ys" :=
         match "ys" with
         | Inl _ => fun _ => Inl ()
         | Inr "p" =>
             let ("y", "ys'") := "p" in
             let "r" :=
               control (fun "k" =>
                          let "k" := "k" "ys'" in
                          fun "xs" =>
                            match "xs" with
                            | Inl _ => Inl ()
                            | Inr "p" =>
                                let ("x", "xs'") := "p" in
                                let "r" := "k" "xs'" in
                                Inr (("x", "y"), "r")
                            end)
             in
             "go" "r"
         end
       in
       let "k" := prompt "go" "ys" in
       "k" "xs" }>.

Example convolve :=
  <{ fun "args" =>
       let ("xs", "ys") := "args" in
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => ("ys", Inl ())
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "p" := "go" "xs'" in
             let ("ys_b", "r") := "p" in
             match "ys_b" with
             | Inl _ => "p"
             | Inr "p" =>
                 let ("y", "ys_b'") := "p" in
                 ("ys_b'", Inr (("x", "y"), "r"))
             end
         end
       in
       let "p" := "go" "xs" in
       snd "p" }>.

Definition eval_convolve (candidate : val_term) (fuel : nat) (xs ys : list Z) :=
  eval_term_to_list_prod_int_int fuel <{ candidate ({list_int_to_val_term xs}, {list_int_to_val_term ys}) }>.

Compute (eval_convolve convolve 100 [1; 2] [3; 4]).
Compute (eval_convolve convolve_cont 100 [1; 2] [3; 4]).
Compute (eval_convolve convolve_dcont 100 [1; 2; 3; 4] [70; 69; 68; 67; 66]).
