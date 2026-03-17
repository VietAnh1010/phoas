From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter error.
From examples Require Import common.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example convolve_cont :=
  <{ fun ("xs", "ys") =>
       let fix "go" ("ys", "k") :=
         match "ys" with
         | Inl _ => "k" "xs"
         | Inr ("y", "ys'") =>
             "go" ("ys'", fun "xs" =>
                            match "xs" with
                            | Inl _ => Inl ()
                            | Inr ("x", "xs'") => Inr (("x", "y"), by "k" "xs'")
                            end)
         end
       in
       "go" ("ys", fun _ => Inl ()) }>.

Example convolve_dcont :=
  <{ fun ("xs", "ys") =>
       let fix "go" "ys" :=
         match "ys" with
         | Inl _ => fun _ => Inl ()
         | Inr ("y", "ys'") =>
             let "r" :=
               control
                 (fun "k" =>
                    let "k" := "k" "ys'" in
                    fun "xs" =>
                      match "xs" with
                      | Inl _ => Inl ()
                      | Inr ("x", "xs'") => Inr (("x", "y"), by "k" "xs'")
                      end)
             in
             "go" "r"
         end
       in
       (by prompt "go" "ys") "xs" }>.

Example convolve :=
  <{ fun ("xs", "ys") =>
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => ("ys", Inl ())
         | Inr ("x", "xs'") =>
             let (("ys_b", "r") as "p") := "go" "xs'" in
             match "ys_b" with
             | Inl _ => "p"
             | Inr ("y", "ys_b'") => ("ys_b'", Inr (("x", "y"), "r"))
             end
         end
       in
       snd (by "go" "xs") }>.

Definition eval_convolve (candidate : val_term) (fuel : nat) (xs ys : list Z) :=
  eval_term_to_list_prod_int_int fuel <{ candidate ({list_int_to_val_term xs}, {list_int_to_val_term ys}) }>.

Compute (eval_convolve convolve 100 [1; 2] [3; 4]).
Compute (eval_convolve convolve_cont 100 [1; 2] [3; 4]).
Compute (eval_convolve convolve 100 [1; 2; 3; 4] [70; 69; 68; 67; 66]).
Compute (eval_convolve convolve_cont 100 [1; 2; 3; 4] [70; 69; 68; 67; 66]).
Compute (eval_convolve convolve_dcont 100 [1; 2; 3; 4] [70; 69; 68; 67; 66]).
