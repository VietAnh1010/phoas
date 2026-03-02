From Stdlib Require Import Ascii String ZArith List.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example fail :=
  <{ fun _ => shift0 (fun _ => {TVString "no"}) }>.

Example flip :=
  <{ fun _ => shift0 (fun "k" => "k" true; "k" false) }>.

Example ndfa :=
  <{ fix "ndfa" "args" :=
       let ("r", "l") := "args" in
       match "r" with
       | `"Char" "c" =>
           match "l" with
           | Inl _ => fail ()
           | Inr "l" =>
               let ("h", "t") := "l" in
               if "h" = "c" then "t" else fail ()
           end
       | `"Concat" "p" =>
           let ("r1", "r2") := "p" in
           let "l" := "ndfa" ("r1", "l") in
           "ndfa" ("r2", "l")
       | `"Union" "p" =>
           let ("r1", "r2") := "p" in
           let "b" := flip () in
           if "b" then "ndfa" ("r1", "l") else "ndfa" ("r2", "l")
       | `"Star" "r'" =>
           let "b" := flip () in
           if "b" then "l" else
             let "l" := "ndfa" ("r'", "l") in
             "ndfa" ("r", "l")
       end }>.

Example accept :=
  <{ fun "args" =>
       let "counter" := ref 0 in
       let "answer" :=
         prompt0
           (reset0
              let "l" := ndfa "args" in
              "counter" <- !"counter" + 1;
              match "l" with
              | Inl _ => control0 (fun _ => {TVString "yes"})
              | Inr _ => {TVString "no"}
              end)
       in
       "answer", !"counter" }>.

Fixpoint term_of_list (xs : list Z) :=
  match xs with
  | [] => <{ Inl () }>
  | x :: xs' => <{ Inr (x, {term_of_list xs'}) }>
  end.

Inductive regex : Type :=
| Char : Z -> regex
| Concat : regex -> regex -> regex
| Union : regex -> regex -> regex
| Star : regex -> regex.

Fixpoint term_of_regex (r : regex) :=
  match r with
  | Char c => <{ `"Char" c }>
  | Concat r1 r2 => <{ `"Concat" ({term_of_regex r1}, {term_of_regex r2}) }>
  | Union r1 r2 => <{ `"Union" ({term_of_regex r1}, {term_of_regex r2}) }>
  | Star r' => <{ `"Star" {term_of_regex r'} }>
  end.

Module Examples.
  Example regex_1 := Concat (Char 67) (Char 69).
  Example list_1_1 := [0].
  Example list_1_2 := [67; 69].
  Compute (eq_refl : eval_term 1000 <{ accept ({term_of_regex regex_1}, {term_of_list list_1_1}) }> = inr (VPair (VString "no") (VInt 0))).
  Compute (eq_refl : eval_term 1000 <{ accept ({term_of_regex regex_1}, {term_of_list list_1_2}) }> = inr (VPair (VString "yes") (VInt 1))).

  Example regex_2 := Star (Concat (Char 7) (Char 12)).
  Example list_2_1 : list Z := [].
  Example list_2_2 := [7].
  Example list_2_3 := [7; 12].
  Example list_2_4 := [7; 12; 7].
  Example list_2_5 := [7; 12; 7; 12].
  Compute (eval_term 1000 <{ accept ({term_of_regex regex_2}, {term_of_list list_2_1}) }>).
  Compute (eval_term 1000 <{ accept ({term_of_regex regex_2}, {term_of_list list_2_2}) }>).
  Compute (eval_term 1000 <{ accept ({term_of_regex regex_2}, {term_of_list list_2_3}) }>).
  Compute (eval_term 1000 <{ accept ({term_of_regex regex_2}, {term_of_list list_2_4}) }>).
  Compute (eval_term 1000 <{ accept ({term_of_regex regex_2}, {term_of_list list_2_5}) }>).
End Examples.
