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

Fixpoint term_of_list (xs : list Z) :=
  match xs with
  | [] => <{ Inl () }>
  | x :: xs' => <{ let "xs'" := {term_of_list xs'} in
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

Compute (eval_term 3 (append1 (term_of_list []))).
Compute (eval_term 4 (append1 (term_of_list [1]))).
Compute (eval_term 3 (append2 (term_of_list []) (term_of_list [1]))).
Compute (eval_term 4 (append2 (term_of_list [1]) (term_of_list [2]))).

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

Compute (eval_term 2 (append_direct1 (term_of_list []))).
Compute (eval_term 2 (append_direct1 (term_of_list [1]))).
Compute (eval_term 3 (append_direct2 (term_of_list []) (term_of_list [1]))).
Compute (eval_term 5 (append_direct2 (term_of_list [1]) (term_of_list [2]))).

Time Compute (eval_term 2000 (term_of_list (sequence 0 1000))).

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

Compute (run_term 3 (sum (term_of_list []))).
Compute (run_term 4 (sum (term_of_list [1]))).
Compute (run_term 5 (sum (term_of_list [1; 2]))).

Time Compute (run_term 503 (sum (term_of_list (sequence 0 500)))).

Example yield :=
  <{ fun "x" => shift "k" (let "p" := ("x", "k") in Inr "p") }>.

Example walk_aux :=
  <{ let "yield" := yield in
     fix "walk_aux" "t" :=
       match "t" with
       | Inl "x" => "yield" "x"
       | Inr "p" =>
           let ("l", "r") := "p" in
           let _ := "walk_aux" "l" in
           "walk_aux" "r"
       end }>.

Example walk  :=
  <{ let "walk_aux" := walk_aux in
     fun "t" => reset (let _ := "walk_aux" "t" in Inl ()) }>.

Example sum_tree :=
  <{ let "walk" := walk in
     fun "t" =>
       let fix "go" "r" :=
         match "r" with
         | Inl _ => 0
         | Inr "p" =>
             let ("x", "r") := "p" in
             let "r" := "r" () in
             let "r" := "go" "r" in
             "x" + "r"
         end
       in
       let "r" := "walk" "t" in
       "go" "r" }>.

Inductive tree (A : Type) :=
| Leaf : A -> tree A
| Node : tree A -> tree A -> tree A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint term_of_tree (t : tree Z) :=
  match t with
  | Leaf x => <{ Inl x }>
  | Node l r => <{ let "l" := {term_of_tree l} in
                   let "r" := {term_of_tree r} in
                   let "p" := ("l", "r") in
                   Inr "p" }>
  end.

Example sum_tree1 t :=
  <{ let "sum_tree" := sum_tree in
     let "t" := {term_of_tree t} in
     "sum_tree" "t" }>.

Compute (eval_term 100 (sum_tree1 (Leaf 0))).
Compute (eval_term 100 (sum_tree1 (Node (Leaf 0) (Leaf 1)))).

Example copy :=
  <{ fix "copy" "xs" :=
       match "xs" with
       | Inl _ => Inl ()
       | Inr "xs" =>
           let ("x", "xs'") := "xs" in
           let "xs" :=
             shift "k"
               let "xs'" := "k" "xs'" in
               let "xs" := ("x", "xs'") in
               Inr "xs"
           in
           "copy" "xs"
       end }>.

Example reverse :=
  <{ fix "reverse" "xs" :=
       match "xs" with
       | Inl _ => Inl ()
       | Inr "xs" =>
           let ("x", "xs'") := "xs" in
           let "xs" :=
             control "k"
               let "xs'" := "k" "xs'" in
               let "xs" := ("x", "xs'") in
               Inr "xs"
           in
           "reverse" "xs"
       end }>.

Example copy1 xs :=
  <{ let "copy" := copy in
     let "xs" := xs in
     reset ("copy" "xs") }>.

Example reverse1 xs :=
  <{ let "reverse" := reverse in
     let "xs" := xs in
     prompt ("reverse" "xs") }>.

Time Compute (eval_term 10000 (copy1 (term_of_list (sequence 0 4000)))).
Time Compute (eval_term 10000 (reverse1 (term_of_list (sequence 0 4000)))).
