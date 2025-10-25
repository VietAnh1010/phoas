From Stdlib Require Import Extraction List String QArith Qcanon ZArith.
Import ListNotations.

From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope term_scope.

Example arith1 := <{ 1 + 2 * 3 }>.
Compute (eval_term 1 arith1).

Example arith2 := <{ 1 + 6 / 6 }>.
Compute (eval_term 1 arith2).

Example cmp1 := <{ 4 + 2 < 6 + 9 }>.
Compute (eval_term 1 cmp1).

Example cmp2 := <{ true < true }>.
Compute (eval_term 1 cmp2).

Example cmp3 := <{ (4, 2) < (6, 9) }>.
Compute (eval_term 1 cmp3).

Example arith3 := <{ {Q2Qc (4 # 6)} + {Q2Qc (4 # 5)} }>.
Compute (eval_term 1 arith3).

Example ex1 :=
  <{ let "f" :=
       reset
         let "x" := 6 * 9 in
         let "y" := shift (fun "k" => "k") in
         "x" * "y"
     in
     "f" 10 }>.

Print ex1.
Compute (eval_term 2 ex1).

Example append_aux :=
  <{ fix "append_aux" "xs" :=
       match "xs" with
       | Inl _ => shift (fun "k" => "k")
       | Inr "xs" =>
           let ("x", "xs'") := "xs" in
           let "r" := "append_aux" "xs'" in
           Inr ("x", "r")
       end }>.

Example append :=
  <{ fun "xs" => reset (append_aux "xs") }>.

Fixpoint term_of_list (xs : list Z) :=
  match xs with
  | [] => <{ Inl () }>
  | x :: xs' => <{ Inr (x, {term_of_list xs'}) }>
  end.

Example append1 xs :=
  <{ let "append" := append in "append" xs }>.

Example append2 xs ys :=
  <{ let "append" := {append1 xs} in "append" ys }>.

Compute (eval_term 3 (append1 (term_of_list []))).
Compute (eval_term 4 (append1 (term_of_list [1]))).
Compute (eval_term 5 (append1 (term_of_list [1; 2]))).
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
           let "append_direct" := "append_direct" "xs'" in
           let "r" := "append_direct" "ys" in
           Inr ("x", "r")
       end }>.

Example append_direct1 xs :=
  <{ let "append_direct" := append_direct in "append_direct" xs }>.

Example append_direct2 xs ys :=
  <{ let "append_direct" := {append_direct1 xs} in "append_direct" ys }>.

Compute (eval_term 2 (append_direct1 (term_of_list []))).
Compute (eval_term 2 (append_direct1 (term_of_list [1]))).
Compute (eval_term 3 (append_direct2 (term_of_list []) (term_of_list [1]))).
Compute (eval_term 5 (append_direct2 (term_of_list [1]) (term_of_list [2]))).

Example either :=
  <{ fun "x" "y" => shift (fun "k" => "k" "x"; "k" "y") }>.

Example ex2 :=
  <{ let "result" := ref false in
     reset
       (let "either1" := either true in
        let "p" := "either1" false in
        let "q" := "either1" false in
        if ("p" || "q") && ("p" || not "q") && (not "p" || not "q") then "result" <- true else ());
     let "answer" := !"result" || "crash" in
     free "result"; "answer" }>.

Print ex2.
Compute (run_term 8 ex2).

Example choice :=
  <{ fun "xs" =>
       shift
         (fun "k" =>
            let fix "go" "xs" :=
              match "xs" with
              | Inl _ => ()
              | Inr "xs" =>
                  let ("x", "xs'") := "xs" in
                  "k" "x";
                  "go" "xs'"
              end
            in "go" "xs") }>.

Example sum xs :=
  <{ let "result" := ref 0 in
     reset (let "x" := choice xs in "result" <- "x" + !"result");
     let "answer" := !"result" in
     free "result"; "answer" }>.

Compute (eval_term 3 (sum (term_of_list []))).
Compute (eval_term 5 (sum (term_of_list [1]))).
Compute (eval_term 7 (sum (term_of_list [1; 2]))).

Time Compute (eval_term 20000 (sum (term_of_list (sequence 0 5000)))).

Example yield :=
  <{ fun "x" => shift (fun "k" => Inr ("x", "k")) }>.

Example walk_aux :=
  <{ fix "walk_aux" "t" :=
       match "t" with
       | Inl "x" => yield "x"
       | Inr "p" =>
           (let ("l", "r") := "p" in
            "walk_aux" "l";
            "walk_aux" "r")
       end }>.

Example walk :=
  <{ fun "t" => reset (walk_aux "t"; Inl ()) }>.

Example sum_tree :=
  <{ fun "t" =>
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
       let "r" := walk "t" in
       "go" "r" }>.

Inductive tree (A : Type) :=
| Leaf : A -> tree A
| Node : tree A -> tree A -> tree A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint term_of_tree (t : tree Z) : val_term :=
  match t with
  | Leaf x => <{ Inl x }>
  | Node l r => <{ Inr ({term_of_tree l}, {term_of_tree r}) }>
  end.

Example sum_tree1 t :=
  <{ let "sum_tree" := sum_tree in
     "sum_tree" {term_of_tree t} }>.

Compute (eval_term 100 (sum_tree1 (Leaf 0))).
Compute (eval_term 100 (sum_tree1 (Node (Leaf 0) (Leaf 1)))).

Example copy :=
  <{ fix "copy" "xs" :=
       match "xs" with
       | Inl _ => Inl ()
       | Inr "xs" =>
           let ("x", "xs'") := "xs" in
           let "xs" :=
             shift
               (fun "k" =>
                  let "xs'" := "k" "xs'" in
                  Inr ("x", "xs'"))
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
             control
               (fun "k" =>
                  let "xs'" := "k" "xs'" in
                  Inr ("x", "xs'"))
           in
           "reverse" "xs"
       end }>.

Example copy1 xs :=
  <{ let "copy" := copy in reset ("copy" xs) }>.

Example reverse1 xs :=
  <{ let "reverse" := reverse in prompt ("reverse" xs) }>.

Time Compute (eval_term 3000 (copy1 (term_of_list (sequence 0 1000)))).
Time Compute (eval_term 3000 (reverse1 (term_of_list (sequence 0 1000)))).

Example unhandled_exception :=
  <{ raise (exception "Segfault" 139) }>.

Example handle_exception (tag : string) :=
  <{ let "r" := ref false in
     try
       (raise (exception tag 10));;
     (fun '("Segfault" "code") =>
        let _ := "r" <- "code" = 10 in
        !"r");
     (fun '("StackOverflow" _) => false);
     (fun "exn" => raise "exn") }>.

Print handle_exception.

Compute (eval_term 1 unhandled_exception).
Compute (eval_term 1 (handle_exception "Segfault")).
Compute (eval_term 1 (handle_exception "StackOverflow")).
Compute (eval_term 1 (handle_exception "Exception")).

Example unhandled_effect :=
  <{ handle
       perform (effect "Effect0" 0);;;
     (fun '("Effect1" _), _ => ());
     (fun '("Effect2" _), _ => ()) }>.

Compute (eval_term 1 unhandled_effect).

Example print :=
  <{ fun "x" => "stdout" <- ("x", !"stdout") }>.

Example basic_exn_eff :=
  <{ let "stdout" := ref () in
     let "print" := print in
     (handle
        ((handle
            (try
               (let "eff0" := effect "Effect0" 0 in
                let "eff1" := effect "Effect1" 1 in
                let "exn" := exception "Exception" () in
                perform "eff0";
                "print" "eff0";
                perform "eff1";
                "print" "eff1";
                raise "exn";
                "print" "exn");;
             (fun '("RuntimeException" "x") => "print" "x");
             (fun '("Exception" _ as "exn") => "print" "exn"));;;
          (fun '("Effect1" "x"), "k" => "print" "x"; "k" ());
          (fun '("Effect2" _ as "eff"), _ => "print" "eff"));
         let "eff2" := effect "Effect2" 2 in
         perform "eff2";
         "print" "eff2";
         let "final_msg" := 69 in
         "print" "final_msg");;;
      (fun '("Effect0" "x"), "k" => "print" "x"; "k" ());
      (fun '("Effect2" _ as "eff"), "k" => "print" "eff"; "k" ()));
     !"stdout" }>.

Compute (eval_term 10 basic_exn_eff).

(*Extraction Language Scheme.*)
(*Extraction "interpreter.ml" run_term.*)
Recursive Extraction run_term.
