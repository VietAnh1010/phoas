From Stdlib Require Import Ascii List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
From examples Require Import common.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example fail :=
  <{ fun _ => shift0 (fun _ => {TVString "no"}) }>.

Example flip :=
  <{ fun _ => shift0 (fun "k" => "k" true; "k" false) }>.

Example ndfa :=
  <{ fix "go" ("r", "l") :=
       match "r" with
       | `"Char" "c" =>
           match "l" with
           | Inl _ => fail ()
           | Inr ("h", "t") => if "h" = "c" then "t" else fail ()
           end
       | `"Concat" ("r1", "r2") =>
           let "l" := "go" ("r1", "l") in
           "go" ("r2", "l")
       | `"Union" ("r1", "r2") =>
           let "b" := flip () in
           if "b" then "go" ("r1", "l") else "go" ("r2", "l")
       | `"Star" "r'" =>
           let "b" := flip () in
           if "b" then "l" else
             let "l" := "go" ("r'", "l") in
             "go" ("r", "l")
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

Inductive regex (A : Type) : Type :=
| Char : A -> regex A
| Concat : regex A -> regex A -> regex A
| Union : regex A -> regex A -> regex A
| Star : regex A -> regex A.

Arguments Char {A} _.
Arguments Concat {A} _ _.
Arguments Union {A} _ _.
Arguments Star {A} _.

Fixpoint regex_int_to_val_term (r : regex Z) : val_term :=
  match r with
  | Char c => <{ `"Char" c }>
  | Concat r1 r2 => <{ `"Concat" ({regex_int_to_val_term r1}, {regex_int_to_val_term r2}) }>
  | Union r1 r2 => <{ `"Union" ({regex_int_to_val_term r1}, {regex_int_to_val_term r2}) }>
  | Star r' => <{ `"Star" {regex_int_to_val_term r'} }>
  end.

Definition eval_accept (fuel : nat) (r : regex Z) (l : list Z) :=
  eval_term fuel <{ accept ({regex_int_to_val_term r}, {list_int_to_val_term l}) }>.

Definition test_accept (fuel : nat) (r : regex Z) (l : list Z) (t : term) :=
  eval_accept fuel r l = eval_term 1 t.

Module Tests.
  Example regex_1 := Concat (Char 67) (Char 69).
  Example list_1_1 := [0].
  Example list_1_2 := [67; 69].
  Compute (eq_refl : test_accept 1000 regex_1 list_1_1 <{ {TVString "no"}, 0 }>).
  Compute (eq_refl : test_accept 1000 regex_1 list_1_2 <{ {TVString "yes"}, 1 }>).

  Example regex_2 := Star (Concat (Char 7) (Char 12)).
  Example list_2_1 : list Z := [].
  Example list_2_2 := [7].
  Example list_2_3 := [7; 12].
  Example list_2_4 := [7; 12; 7].
  Example list_2_5 := [7; 12; 7; 12].
  Compute (eval_accept 1000 regex_2 list_2_1).
  Compute (eval_accept 1000 regex_2 list_2_2).
  Compute (eval_accept 1000 regex_2 list_2_3).
  Compute (eval_accept 1000 regex_2 list_2_4).
  Compute (eval_accept 1000 regex_2 list_2_5).
End Tests.
