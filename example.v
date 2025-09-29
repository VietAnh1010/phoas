From Stdlib Require Import Extraction List String ZArith.
Import ListNotations.

From shift_reset.core Require Import syntax syntax_notation.
From shift_reset.interpreter Require Import interpreter.
Import Coerce.

Open Scope string_scope.
Open Scope Z_scope.

Example ex1 :=
  <{ let "f" :=
       reset
         let "x" := 6 * 9 in
         let "y" := shift "k" "k" in
         "x" * "y"
     in
     "f" 10 }>.

Compute (eval_term 2 ex1).

Example append_aux :=
  <{ fix "append_aux" "xs" :=
       match "xs" with
       | Inl _ => shift "k" "k"
       | Inr "xs" =>
           let ("x", "xs'") := "xs" in
           let "r" := "append_aux" "xs'" in
           let "r" := ("x", "r") in
           Inr "r"
       end }>.

Example append :=
  <{ let "append_aux" := append_aux in
     fun "xs" => reset "append_aux" "xs" }>.

Fixpoint encode (xs : list Z) :=
  match xs with
  | [] => <{ Inl () }>
  | x :: xs' => <{ let "xs'" := {encode xs'} in
                   let "xs" := (x, "xs'") in
                   Inr "xs" }>
  end.

Example append1 xs :=
  <{ let "append" := append in
     let "xs" := xs in
     "append" "xs" }>.

Example append2 xs ys :=
  <{ let "append" := append in
     let "xs" := xs in
     let "ys" := ys in
     let "append1" := "append" "xs" in
     "append1" "ys" }>.

Compute (eval_term 3 (append1 (encode []))).
Compute (eval_term 4 (append1 (encode [1]))).
Compute (eval_term 3 (append2 (encode []) (encode [1]))).
Compute (eval_term 4 (append2 (encode [1]) (encode [2]))).

Fixpoint sequence start len : list Z :=
  match len with
  | O => []
  | S len' => start :: sequence (start + 1) len'
  end.

Example append_direct :=
  <{ fix "append_direct" "xs" "ys" :=
       match "xs" with
       | Inl _ => "ys"
       | Inr "xs" =>
           let ("x", "xs'") := "xs" in
           let "append_direct1" := "append_direct" "xs'" in
           let "r" := "append_direct1" "ys" in
           let "r" := ("x", "r") in
           Inr "r"
       end }>.

Example append_direct1 xs :=
  <{ let "append_direct" := append_direct in
     let "xs" := xs in
     "append_direct" "xs" }>.

Example append_direct2 xs ys :=
  <{ let "append_direct" := append_direct in
     let "xs" := xs in
     let "ys" := ys in
     let "append_direct1" := "append_direct" "xs" in
     "append_direct1" "ys" }>.

Compute (eval_term 2 (append_direct1 (encode []))).
Compute (eval_term 2 (append_direct1 (encode [1]))).
Compute (eval_term 2 (append_direct2 (encode []) (encode [1]))).
Compute (eval_term 3 (append_direct2 (encode [1]) (encode [2]))).

Time Compute (eval_term 2000 (encode (sequence 0 1000))).
Time Compute (eval_term_kont 2000 (encode (sequence 0 1000)) KNil).

Example either :=
  <{ fun "x" "y" => shift "k" let _ := "k" "x" in "k" "y" }>.

Example ex2 :=
  <{ let "either" := either in
     let "result" := ref false in
     let _ :=
       reset
         let "either1" := "either" true in
         let "p" := "either1" false in
         let "q" := "either1" false in
         let "not_p" := not "p" in
         let "not_q" := not "q" in
         let "c1" := "p" || "q" in
         let "c2" := "p" || "not_q" in
         let "c3" := "not_p" || "not_q" in
         let "r" := "c1" && "c2" in
         let "r" := "r" && "c3" in
         if "r" then "result" <- true else ()
     in !"result" }>.

Compute (eval_term 6 ex2).

Example choice :=
  <{ fun "xs" =>
       shift "k"
         let fix "go" "xs" :=
           match "xs" with
           | Inl _ => ()
           | Inr "xs" =>
               let ("x", "xs'") := "xs" in
               let _ := "k" "x" in
               "go" "xs'"
           end
         in "go" "xs" }>.

Example sum xs :=
  <{ let "choice" := choice in
     let "xs" := xs in
     let "result" := ref 0 in
     let _ :=
       reset
         let "x" := "choice" "xs" in
         let "r" := !"result" in
         let "r" := "r" + "x" in
         "result" <- "r"
     in !"result" }>.

Compute (run_term 3 (sum (encode []))).
Compute (run_term 4 (sum (encode [1]))).
Compute (run_term 5 (sum (encode [1; 2]))).

Time Compute (run_term 1000 (sum (encode (sequence 0 500)))).
