From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter error.
From examples Require Import common.
From examples.stdlib Require Import list.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example is_palindrome_cont :=
  <{ fun "xs" =>
       let "List" := List in
       let fix "go" `("xs", "ys", "k") :=
         match "xs" with
         | Inl _ => "k" "ys"
         | Inr (_, "xs'") =>
             let (Inr ("y", "ys'")) := "ys" in
             match "xs'" with
             | Inl _ => "k" "ys'"
             | Inr (_, "xs''") => "go" `("xs''", "ys'", fun (Inr ("y'", "ys_b")) => "y" = "y'" && by "k" "ys_b")
             end
         end
       in
       "go" `("xs", "xs", fun _ => true) }>.

Example is_palindrome_exception :=
  <{ fun "xs" =>
       let "List" := List in
       let fix "go" ("xs", "ys") :=
         match "xs" with
         | Inl _ => "ys"
         | Inr (_, "xs'") =>
             let (Inr ("y", "ys'")) := "ys" in
             match "xs'" with
             | Inl _ => "ys'"
             | Inr (_, "xs''") =>
                 let (Inr ("y'", "ys_b")) := "go" ("xs''", "ys'") in
                 if "y" = "y'" then "ys_b" else raise false
             end
         end
       in
       try "go" ("xs", "xs"); true;; (fun false => false) }>.

Definition eval_is_palindrome (candidate : val_term) (fuel : nat) (xs : list Z) :=
  eval_term fuel <{ candidate {list_int_to_val_term xs} }>.

Definition test_is_palindrome (candidate : val_term) (fuel : nat) (xs : list Z) (t : term) :=
  eval_is_palindrome candidate fuel xs = eval_term 1 t.

Compute (eq_refl : test_is_palindrome is_palindrome_cont 100 [] <{ true }>).
Compute (eq_refl : test_is_palindrome is_palindrome_cont 100 [1; 2; 2; 1] <{ true }>).
Compute (eq_refl : test_is_palindrome is_palindrome_cont 100 [1; 2; 1; 2; 1] <{ true }>).
Compute (eq_refl : test_is_palindrome is_palindrome_cont 100 [1; 2; 1; 3; 3; 1; 2; 0] <{ false }>).

Compute (eq_refl : test_is_palindrome is_palindrome_exception 100 [] <{ true }>).
Compute (eq_refl : test_is_palindrome is_palindrome_exception 100 [1; 2; 2; 1] <{ true }>).
Compute (eq_refl : test_is_palindrome is_palindrome_exception 100 [1; 2; 1; 2; 1] <{ true }>).
Compute (eq_refl : test_is_palindrome is_palindrome_exception 100 [1; 2; 1; 3; 3; 1; 2; 0] <{ false }>).
