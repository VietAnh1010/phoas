From Stdlib Require Import List String QArith Qcanon ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
From examples Require Import common.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope term_scope.

Example arith1 := <{ 1 + 2 * 3 }>.
Compute (eval_term 1 arith1).

Example arith2 := <{ 1 + 6 / 6 }>.
Compute (eval_term 1 arith2).

Example arith3 := <{ {Q2Qc (4 # 6)} + {Q2Qc (4 # 5)} }>.
Compute (eval_term 1 arith3).

Example arith4 := <{ 10 / 0 }>.
Compute (eval_term 1 arith4).

Example arith5 := <{ 10 mod 0 }>.
Compute (eval_term 1 arith5).

Example arith6 := <{ {Q2Qc (6 # 9)} / {0%Qc} }>.
Compute (eval_term 1 arith6).

Example cmp1 := <{ 4 + 2 < 6 + 9 }>.
Compute (eval_term 1 cmp1).

Example cmp2 := <{ true < true }>.
Compute (eval_term 1 cmp2).

Example cmp3 := <{ (4, 2) < (6, 9) }>.
Compute (eval_term 1 cmp3).

Example ex1 :=
  <{ let "f" :=
       reset
         let "x" := 6 * 9 in
         let "y" := shift (fun "k" => "k") in
         "x" * "y"
     in
     "f" 10 }>.

Compute (eval_term 2 ex1).

Definition ref_free := TVBuiltin1 "ref_free".

Example either :=
  <{ fun "x" "y" => shift (fun "k" => "k" "x"; "k" "y") }>.

Example ex2 :=
  <{ let "result" := ref false in
     reset
       (let "either1" := either true in
        let "p" := "either1" false in
        let "q" := "either1" false in
        if ("p" || "q") && ("p" || not "q") && (not "p" || not "q")
        then "result" <- true else ());
     let "answer" := !"result" || "crash" in
     {ref_free "result"}; "answer" }>.

Compute (eval_term 5 ex2).

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
     reset let "x" := choice xs in "result" <- "x" + !"result";
     let "answer" := !"result" in
     {ref_free "result"}; "answer" }>.

Compute (eval_term 3 (sum (list_int_to_val_term []))).
Compute (eval_term 4 (sum (list_int_to_val_term [1]))).
Compute (eval_term 5 (sum (list_int_to_val_term [1; 2]))).
Time Compute (eval_term 5005 (sum (list_int_to_val_term (range 0 5000)))).

Example yield :=
  <{ fun "x" => shift (fun "k" => Inr ("x", "k")) }>.

Example walk_aux :=
  <{ fix "walk_aux" "t" :=
       match "t" with
       | Inl "x" => yield "x"
       | Inr "p" =>
           let ("l", "r") := "p" in
           let _ := "walk_aux" "l" in
           let _ := "walk_aux" "r" in
           ()
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
  <{ let "sum_tree" := sum_tree in "sum_tree" {term_of_tree t} }>.

Compute (eval_term 100 (sum_tree1 (Leaf 0))).
Compute (eval_term 100 (sum_tree1 (Node (Leaf 0) (Leaf 1)))).

Fixpoint make_balanced_tree3 (n : nat) : val_term :=
  match n with
  | O => <{ `"Leaf" {Z.of_nat n} }>
  | S n' =>
      let t := make_balanced_tree3 n' in
      <{ `"Node" `(t, {Z.of_nat n}, t) }>
  end.

Example bfs :=
  <{ fix "bfs" "t" :=
       match "t" with
       | `"Leaf" "x" =>
           control
             (fun "k" =>
                let "xs" := "k" () in
                Inr ("x", "xs"))
       | `"Node" "p" =>
           let `("l", "x", "r") := "p" in
           control
             (fun "k" =>
                let "xs" := "k" () in
                "bfs" "l";
                "bfs" "r";
                Inr ("x", "xs"))
       end }>.

Example bfs1 t :=
  <{ prompt (bfs t; Inl ()) }>.

Compute (eval_term_to_list_int 100 (bfs1 (make_balanced_tree3 0))).
Compute (eval_term_to_list_int 100 (bfs1 (make_balanced_tree3 1))).
Compute (eval_term_to_list_int 100 (bfs1 (make_balanced_tree3 2))).
Compute (eval_term_to_list_int 100 (bfs1 (make_balanced_tree3 3))).

Example dfs :=
  <{ fix "dfs" "t" :=
       match "t" with
       | `"Leaf" "x" =>
           shift
             (fun "k" =>
                let "xs" := "k" () in
                Inr ("x", "xs"))
       | `"Node" "p" =>
           let `("l", "x", "r") := "p" in
           shift
             (fun "k" =>
                let "xs" := "k" () in
                "dfs" "l";
                "dfs" "r";
                Inr ("x", "xs"))
       end }>.

Example dfs1 t :=
  <{ reset (dfs t; Inl ()) }>.

Compute (eval_term_to_list_int 100 (dfs1 (make_balanced_tree3 0))).
Compute (eval_term_to_list_int 100 (dfs1 (make_balanced_tree3 1))).
Compute (eval_term_to_list_int 100 (dfs1 (make_balanced_tree3 2))).
Compute (eval_term_to_list_int 100 (dfs1 (make_balanced_tree3 3))).

Example unhandled_exception :=
  <{ raise `"Segfault" 139 }>.

Example handle_exception (tag : string) :=
  <{ let "r" := ref false in
     try
       raise `tag 10;;
     (fun `"Segfault" "code" =>
        let _ := "r" <- "code" = 10 in
        !"r");
     (fun `"StackOverflow" _ => false);
     (fun "exn" => raise "exn") }>.

Compute (eval_term 1 unhandled_exception).
Compute (eval_term 1 (handle_exception "Segfault")).
Compute (eval_term 1 (handle_exception "StackOverflow")).
Compute (eval_term 1 (handle_exception "Exception")).

Example unhandled_effect :=
  <{ handle
       perform `"Effect0" ();;;
     (fun `"Effect1" _ _ => ());
     (fun `"Effect2" _ _ => ()) }>.

Compute (eval_term 1 unhandled_effect).

Example print :=
  <{ fun "x" => "stdout" <- ("x", !"stdout") }>.

Example basic_exn_eff :=
  <{ let "stdout" := ref () in
     let "print" := print in
     (handle
        ((handle
            (try
               (let "eff0" := `"Effect0" 0 in
                let "eff1" := `"Effect1" 1 in
                let "exn" := `"Exception" () in
                perform "eff0";
                "print" "eff0";
                perform "eff1";
                "print" "eff1";
                raise "exn";
                "print" "exn");;
             (fun `"RuntimeException" "x" => "print" "x");
             (fun `"Exception" "x" => "print" (`"Exception" "x")));;;
          (fun `"Effect1" "x" "k" => "print" "x"; "k" ());
          (fun `"Effect2" "x" _ => "print" (`"Effect2" "x")));
         let "eff2" := `"Effect2" 2 in
         perform "eff2";
         "print" "eff2";
         let "final_msg" := 69 in
         "print" "final_msg");;;
      (fun `"Effect0" "x" "k" => "print" "x"; "k" ());
      (fun `"Effect2" "x" "k" => "print" (`"Effect2" "x"); "k" ()));
     !"stdout" }>.

Compute (eval_term 4 basic_exn_eff).

Example collatz k :=
  <{ let fix "collatz_len" "n" :=
       if "n" = 1 then 1 else
         (by
            if "n" mod 2 = 0
            then "collatz_len" ("n" / 2)
            else "collatz_len" (3 * "n" + 1)) + 1
     in
     let "max_len" := ref 0 in
     let "n_of_max_len" := ref 0 in
     let _ :=
       for "i" from 1 upto k do
         let "len" := "collatz_len" "i" in
         if "len" > !"max_len" then
           "max_len" <- "len";
           "n_of_max_len" <- "i"
         else ()
     in
     !"n_of_max_len", !"max_len" }>.

Time Compute (eval_term 150 (collatz 500)).

Example eval_ltr :=
  <{ fix "eval" "e" :=
       match "e" with
       | `"Num" "n" => "n"
       | `"Add" `{"lhs"; "rhs"} => by "eval" "lhs" + by "eval" "rhs"
       | `"Mul" `{"lhs"; "rhs"} => by "eval" "lhs" * by "eval" "rhs"
       | _ => raise `"Failure" "e"
       end }>.

Example eval_ltr_input1 :=
  <{ `"Add" `{"lhs" := `"Num" 2; "rhs" := `"Mul" `{"lhs" := `"Num" 3; "rhs" := `"Num" 4}} }>.

Example eval_ltr_input2 :=
  <{ `"Sub" `{"lhs" := `"Num" 6; "rhs" := `"Num" 9} }>.

Compute (eval_term 10 <{ eval_ltr eval_ltr_input1 }>).
Compute (eval_term 10 <{ eval_ltr eval_ltr_input2 }>).

Example loop :=
  <{ let "stdout" := ref () in
     let "clock" := ref 0 in
     let "print" := print in
     let "f" _ :=
       let _ := "print" !"clock" in
       let _ := "clock" <- !"clock" + 1 in
       let "f" := perform `"Foo" () in
       "f" ()
     in
     handle "f" ();;; (fun `"Foo" _ "k" => "k" "f") }>.

Compute (run_term 10 loop).

Example even :=
  <{ fix "odd" "x" := if "x" = 0 then false else "even" ("x" - 1)
     with "even" "x" := if "x" = 0 then true else "odd" ("x" - 1)
     for "even" }>.

Compute (eval_term 100 <{ even 50 }>).
Compute (eval_term 100 <{ even 49 }>).
Compute (eval_term 100 <{ even (-1) }>).

Example send_recv_protocol :=
  <{ fun "k" =>
       let fix "send" "args" :=
         let ("k", "v") := "args" in
         (shallow handle "k" "v";;;
          (fun `"Send" "n" "k" => "recv" `("n", "k", ()));
          (fun `"Recv" _ _ => raise `"Protocol_violation" ()))
       with "recv" "args" :=
         let `("n", "k", "v") := "args" in
         (shallow handle "k" "v";;;
          (fun `"Recv" _ "k" => "send" ("k", "n"));
          (fun `"Send" _ _ => raise `"Protocol_violation" ()))
       in "send" ("k", ()) }>.

Example run_send_recv1 :=
  <{ let "stdout" := ref () in
     let "print" := print in
     send_recv_protocol
       (fun _ =>
          let "eff" := `"Send" 42 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          let "eff" := `"Recv" () in
          let _ := "print" "eff" in
          let "n" := perform "eff" in
          let _ := "print" "n" in
          let "eff" := `"Send" 43 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          let "eff" := `"Recv" () in
          let _ := "print" "eff" in
          let "n" := perform "eff" in
          let _ := "print" "n" in
          ());
     !"stdout" }>.

Compute (eval_term 9 run_send_recv1).

Example run_send_recv2 :=
  <{ let "stdout" := ref () in
     let "print" := print in
     send_recv_protocol
       (fun _ =>
          let "eff" := `"Send" 0 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          let "eff" := `"Send" 1 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          ());
     !"stdout" }>.

Compute (eval_term 6 run_send_recv2).

Example nat_iterator n :=
  <{ let "seed" := ref n in
     fun _ =>
       let "x" := !"seed" in
       let _ := "seed" <- "x" + 1 in
       "x" }>.

Example map_iterator f it :=
  <{ fun _ => let "x" := it () in f "x" }>.

Example zip_with_iterator f it1 it2 :=
  <{ fun _ =>
       let "x" := it1 () in
       let "y" := it2 () in
       f ("x", "y") }>.

Example delta_iterator p it :=
  <{ let "prev" := ref p in
     fun _ =>
       let "x" := it () in
       let "y" := !"prev" in
       let _ := "prev" <- "x" in
       "x" - "y" }>.

Example delta_n :=
  <{ fix "delta_n" "args" :=
       let ("it", "n") := "args" in
       if "n" = 0 then
         "it"
       else
         let "it" := "delta_n" ("it", "n" - 1) in
         let "p" := "it" () in
         {delta_iterator "p" "it"} }>.

Example run_delta_n it n k :=
  <{ let "it" := it in
     let "it" := delta_n ("it", n) in
     let "r" := ref () in
     let _ :=
       for "i" from 0 upto k do
         let "v" := "it" () in
         "r" <- ("v", !"r")
     in
     !"r" }>.

Compute (eval_term 10 (run_delta_n (nat_iterator 0) 0 5)).
Compute (eval_term 10 (run_delta_n (nat_iterator 0) 1 5)).
Compute (eval_term 10 (run_delta_n (nat_iterator 0) 2 5)).

Example square_iterator n :=
  <{ let "it" := {nat_iterator n} in
     let "f" "x" := "x" * "x" in
     {map_iterator "f" "it"} }>.

Compute (eval_term 10 (run_delta_n (square_iterator 0) 0 5)).
Compute (eval_term 10 (run_delta_n (square_iterator 0) 1 5)).
Compute (eval_term 10 (run_delta_n (square_iterator 0) 2 5)).
Compute (eval_term 10 (run_delta_n (square_iterator 0) 3 5)).

Example cube_iterator n :=
  <{ let "it" := {nat_iterator n} in
     let "f" "x" := "x" * "x" * "x" in
     {map_iterator "f" "it"} }>.

Compute (eval_term 10 (run_delta_n (cube_iterator 0) 0 5)).
Compute (eval_term 10 (run_delta_n (cube_iterator 0) 1 5)).
Compute (eval_term 10 (run_delta_n (cube_iterator 0) 2 5)).
Compute (eval_term 10 (run_delta_n (cube_iterator 0) 3 5)).
Compute (eval_term 15 (run_delta_n (cube_iterator 0) 4 5)).

Example x3_x2_iterator n :=
  <{ let "it1" := {cube_iterator n} in
     let "it2" := {square_iterator n} in
     let "f" "args" := let ("x", "y") := "args" in "x" + "y" in
     {zip_with_iterator "f" "it1" "it2"} }>.

Compute (eval_term 10 (run_delta_n (x3_x2_iterator 0) 0 5)).
Compute (eval_term 10 (run_delta_n (x3_x2_iterator 0) 1 5)).
Compute (eval_term 10 (run_delta_n (x3_x2_iterator 0) 2 5)).
Compute (eval_term 15 (run_delta_n (x3_x2_iterator 0) 3 5)).
Compute (eval_term 15 (run_delta_n (x3_x2_iterator 0) 4 5)).

Example array_make := TVBuiltin2 "array_make".

Example counting_sort_lt_10 xs :=
  <{ let "ref_xs" := ref xs in
     let "arr_fs" := `[| 0; 0; 0; 0; 0; 0; 0; 0; 0; 0 |] in
     (try
        (while true do
           (match !"ref_xs" with
            | Inl _ => raise `"Exit" ()
            | Inr ("x", "xs'") =>
                "arr_fs".["x"] <- "arr_fs".["x"] + 1;
                "ref_xs" <- "xs'"
            end));;
      (fun `"Exit" _ => ()));
     (for "i" from 9 downto 0 do
        (for _ from ("arr_fs".["i"]) downto 1 do
           "ref_xs" <- Inr ("i", !"ref_xs")));
     !"ref_xs" }>.

Compute (eval_term_to_list_int 11 (counting_sort_lt_10 (list_int_to_val_term []))).
Compute (eval_term_to_list_int 11 (counting_sort_lt_10 (list_int_to_val_term [0]))).
Compute (eval_term_to_list_int 11 (counting_sort_lt_10 (list_int_to_val_term [0; 9; 1]))).
Compute (eval_term_to_list_int 11 (counting_sort_lt_10 (list_int_to_val_term [8; 7; 0; 9; 1]))).
Compute (eval_term_to_list_int 11 (counting_sort_lt_10 (list_int_to_val_term [8; 7; 0; 7; 9; 1; 7]))).

Example compare_int :=
  <{ fun ("x", "y") => if "x" < "y" then `"Lt" () else if "x" = "y" then `"Eq" () else `"Gt" () }>.

Example partition x xs :=
  <{ let fix "go" "xs" :=
       match "xs" with
       | Inl _ => Inl ()
       | Inr ("x", "xs'") =>
           match by compare_int (x, "x") with
           | `"Lt" _ => let "r" := "go" "xs'" in Inr ("x", "r")
           | `"Eq" _ => shift0 (fun "k" => let "r" := reset0 let "r" := "go" "xs'" in "k" "r" in Inr ("x", "r"))
           | `"Gt" _ => shift0 (fun "k" => shift0 (fun "k'" => let "r" := reset0 let "r" := reset0 let "r" := "go" "xs'" in "k" "r" in "k'" "r"
                                                               in Inr ("x", "r")))
           end
       end
     in reset0 reset0 "go" xs }>.

Compute (eval_term_to_list_int 20 <{ {partition 1 (list_int_to_val_term [4; 1; 3; 5; 2; 3])} }>).
Compute (eval_term_to_list_int 20 <{ {partition 2 (list_int_to_val_term [4; 1; 3; 5; 2; 3])} }>).
Compute (eval_term_to_list_int 20 <{ {partition 3 (list_int_to_val_term [4; 1; 3; 5; 2; 3])} }>).

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlChar ExtrOcamlNativeString.
(*From Stdlib Require Import ExtrOcamlNatInt ExtrOcamlZInt.
Print LoadPath.*)

Extraction Language OCaml.
(*Extraction "interpreter.ml" run_term.*)
Recursive Extraction run_term.
