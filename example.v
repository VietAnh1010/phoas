From Stdlib Require Import Extraction List String ZArith.
Import ListNotations.

From shift_reset.core Require Import syntax syntax_notation.
From shift_reset.interpreter Require Import interpreter.
Import Coerce.

Open Scope string_scope.
Open Scope Z_scope.

Example ex1 :=
  <{ let "f" =
         reset begin
           let "x" = 6 * 9 in
           let "y" = (shift "k" => "k") in
           "x" * "y"
         end
     in
     "f" 10 }>.

Compute (eval_term 2 ex1).

Example append_aux :=
  <{ fix "append_aux" "xs" =>
       match "xs" with
       | Inl {BAnon} => shift "k" => "k"
       | Inr "xs" =>
           let "x", "xs'" = "xs" in
           let "r" = "append_aux" "xs'" in
           let "r" = "x", "r" in
           Inr "r"
       end }>.

Example append :=
  <{ let "append_aux" = {append_aux} in
     fun "xs" => reset "append_aux" "xs" }>.

Fixpoint encode (xs : list Z) :=
  match xs with
  | [] => <{ Inl () }>
  | x :: xs' =>
      <{ let "xs'" = {encode xs'} in
         let "xs" = {x}, "xs'" in
         Inr "xs" }>
  end.

Example append1 xs :=
  <{ let "append" = {append} in
     let "xs" = {xs} in
     "append" "xs" }>.

Example append2 xs ys :=
  <{ let "append" = {append} in
     let "xs" = {xs} in
     let "ys" = {ys} in
     let "append1" = "append" "xs" in
     "append1" "ys" }>.

Compute (eval_term 3 (append1 (encode []))).
Compute (eval_term 4 (append1 (encode [1]))).
Compute (eval_term 3 (append2 (encode []) (encode [1]))).
Compute (eval_term 4 (append2 (encode [1]) (encode [2]))).

Fixpoint sequence start len : list Z :=
  match len with
  | O => []
  | S len' => start :: sequence (Z.succ start) len'
  end.

Example append_direct :=
  <{ fix "append_direct" "xs" "ys" =>
       match "xs" with
       | Inl {BAnon} => "ys"
       | Inr "xs" =>
           let "x", "xs'" = "xs" in
           let "append_direct1" = "append_direct" "xs'" in
           let "r" = "append_direct1" "ys" in
           let "r" = "x", "r" in
           Inr "r"
       end }>.

Example append_direct1 xs :=
  <{ let "append_direct" = {append_direct} in
     let "xs" = {xs} in
     "append_direct" "xs" }>.

Example append_direct2 xs ys :=
  <{ let "append_direct" = {append_direct} in
     let "xs" = {xs} in
     let "ys" = {ys} in
     let "append_direct1" = "append_direct" "xs" in
     "append_direct1" "ys" }>.

Compute (eval_term 2 (append_direct1 (encode []))).
Compute (eval_term 2 (append_direct1 (encode [1]))).
Compute (eval_term 2 (append_direct2 (encode []) (encode [1]))).
Compute (eval_term 3 (append_direct2 (encode [1]) (encode [2]))).

Time Compute (eval_term 2000 (encode (sequence 0 1000))).
Time Compute (eval_term_kont 2000 (encode (sequence 0 1000)) KNil).
