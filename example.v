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

Fixpoint list_of_val (l : val) : option (list val) :=
  match l with
  | VInl Vtt => Some []
  | VInr (VPair v t) => option.map (cons v) (list_of_val t)
  | _ => None
  end.

Definition list_eval_term (n : nat) (t : term) : option (list val) :=
  match eval_term n t with
  | inl _ => None
  | inr l => list_of_val l
  end.

Example append1 xs :=
  <{ let "append" := append in "append" xs }>.

Example append2 xs ys :=
  <{ let "append" := {append1 xs} in "append" ys }>.

Compute (eval_term 3 (append1 (term_of_list []))).
Compute (eval_term 4 (append1 (term_of_list [1]))).
Compute (eval_term 5 (append1 (term_of_list [1; 2]))).
Compute (list_eval_term 3 (append2 (term_of_list []) (term_of_list [1]))).
Compute (list_eval_term 4 (append2 (term_of_list [1]) (term_of_list [2]))).

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
Compute (eval_term 2 (append_direct2 (term_of_list []) (term_of_list [1]))).
Compute (eval_term 3 (append_direct2 (term_of_list [1]) (term_of_list [2]))).

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
                  let _ := "k" "x" in
                  "go" "xs'"
              end
            in "go" "xs") }>.

Example sum xs :=
  <{ let "result" := ref 0 in
     reset (let "x" := choice xs in "result" <- "x" + !"result");
     let "answer" := !"result" in
     {ref_free "result"}; "answer" }>.

Compute (eval_term 3 (sum (term_of_list []))).
Compute (eval_term 4 (sum (term_of_list [1]))).
Compute (eval_term 5 (sum (term_of_list [1; 2]))).
Time Compute (eval_term 5005 (sum (term_of_list (sequence 0 5000)))).

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

Compute (list_eval_term 100 (bfs1 (make_balanced_tree3 0))).
Compute (list_eval_term 100 (bfs1 (make_balanced_tree3 1))).
Compute (list_eval_term 100 (bfs1 (make_balanced_tree3 2))).
Compute (list_eval_term 100 (bfs1 (make_balanced_tree3 3))).

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

Compute (list_eval_term 100 (dfs1 (make_balanced_tree3 0))).
Compute (list_eval_term 100 (dfs1 (make_balanced_tree3 1))).
Compute (list_eval_term 100 (dfs1 (make_balanced_tree3 2))).
Compute (list_eval_term 100 (dfs1 (make_balanced_tree3 3))).

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

Example reverse_while :=
  <{ fun "xs" =>
       let "in" := ref "xs" in
       let "out" := ref (Inl ()) in
       try
         (while true do
            (match !"in" with
             | Inl _ => raise exception "Exit" ()
             | Inr "xs" =>
                 let ("x", "xs'") := "xs" in
                 "in" <- "xs'";
                 "out" <- Inr ("x", !"out")
             end));;
       (fun '("Exit" _) => !"out") }>.

Example copy1 xs :=
  <{ let "copy" := copy in reset ("copy" xs) }>.

Example reverse1 xs :=
  <{ let "reverse" := reverse in prompt ("reverse" xs) }>.

Example reverse_while1 xs :=
  <{ let "reverse_while" := reverse_while in "reverse_while" xs }>.

Time Compute (list_eval_term 2010 (copy1 (term_of_list (sequence 0 1000)))).
Time Compute (list_eval_term 2010 (reverse1 (term_of_list (sequence 0 1000)))).
Time Compute (list_eval_term 1010 (reverse_while1 (term_of_list (sequence 0 1000)))).

Example unhandled_exception :=
  <{ raise exception "Segfault" 139 }>.

Example handle_exception (tag : string) :=
  <{ let "r" := ref false in
     try
       raise exception tag 10;;
     (fun '("Segfault" "code") =>
        let _ := "r" <- "code" = 10 in
        !"r");
     (fun '("StackOverflow" _) => false);
     (fun "exn" => raise "exn") }>.

Compute (eval_term 1 unhandled_exception).
Compute (eval_term 1 (handle_exception "Segfault")).
Compute (eval_term 1 (handle_exception "StackOverflow")).
Compute (eval_term 1 (handle_exception "Exception")).

Example unhandled_effect :=
  <{ handle
       perform effect "Effect0" ();;;
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
             (fun '("Exception" "x") => "print" (exception "Exception" "x")));;;
          (fun '("Effect1" "x"), "k" => "print" "x"; "k" ());
          (fun '("Effect2" "x"), _ => "print" (effect "Effect2" "x")));
         let "eff2" := effect "Effect2" 2 in
         perform "eff2";
         "print" "eff2";
         let "final_msg" := 69 in
         "print" "final_msg");;;
      (fun '("Effect0" "x"), "k" => "print" "x"; "k" ());
      (fun '("Effect2" "x"), "k" => "print" (effect "Effect2" "x"); "k" ()));
     !"stdout" }>.

Compute (eval_term 4 basic_exn_eff).

Example variant :=
  <{ let "v" := `"Variant1" (6, 9) in
     match "v" with
     | `"Variant1" "p" => let ("x", "y") := "p" in ("v", "x" + "y")
     | `"Variant2" _ => raise exception "Failure" ()
     end }>.

Compute (eval_term 1 variant).

Example record :=
  <{ let "x" := `{"fst" := 1 ; "snd" := 2} in
     `{"fst" := "x".("fst"); "snd" := "x".("fst") + "x".("snd")} }>.

Compute (eval_term 1 record).

Example collatz k :=
  <{ let fix "collatz_len" "n" :=
       if "n" = 1 then 1 else
         if "n" mod 2 = 0 then let "r" := "collatz_len" ("n" / 2) in 1 + "r"
         else let "r" := "collatz_len" (3 * "n" + 1) in 1 + "r"
     in
     let "max_len" := ref 0 in
     let "n_of_max_len" := ref 0 in
     let "i" := ref 1 in
     (while (!"i" <= k) do
        let "len" := "collatz_len" (!"i") in
        (if "len" > !"max_len" then
           "max_len" <- "len";
           "n_of_max_len" <- !"i"
         else ());
        "i" <- !"i" + 1);
     !"n_of_max_len", !"max_len" }>.

Time Compute (eval_term 1000 (collatz 500)).

Example eval_ltr :=
  <{ fix "eval" "e" :=
       match "e" with
       | `"Num" "n" => "n"
       | `"Add" "p" =>
           let "r1" := "eval" ("p".("lhs")) in
           let "r2" := "eval" ("p".("rhs")) in
           "r1" + "r2"
       | `"Mul" "p" =>
           let "r1" := "eval" ("p".("lhs")) in
           let "r2" := "eval" ("p".("rhs")) in
           "r1" * "r2"
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
       let _ := "print" (!"clock") in
       let _ := "clock" <- !"clock" + 1 in
       let "f" := perform effect "Foo" () in
       "f" ()
     in
     handle "f" ();;; (fun '("Foo" _), "k" => "k" "f") }>.

Compute (run_term 10 loop).

Example tuple1 := <{ `(1, 2, 3, 4, 5) }>.
Example use_tuple1 := <{ let `("a", "b", "c", "d", "e") := tuple1 in "a" + "b" + "c" + "d" + "e" }>.

Compute (eval_term 1 use_tuple1).

Example even :=
  let odd := <{ if "x" = 0 then false else "even" ("x" - 1) }> in
  let even := <{ if "x" = 0 then true else "odd" ("x" - 1) }> in
  <{ fix "odd" "x" := odd with "even" "x" := even for "even" }>.

Compute (eval_term 100 <{ even 50 }>).
Compute (eval_term 100 <{ even 49 }>).
Compute (eval_term 100 <{ even (-1) }>).

Example send_recv_protocol :=
  let send :=
    <{ let ("k", "v") := "args" in
       shallow handle
         "k" "v";;;
       (fun '("Send" "n"), "k" => "recv" `("n", "k", ()));
       (fun '("Recv" _), _ => raise exception "Protocol_violation" ()) }>
  in
  let recv :=
    <{ let `("n", "k", "v") := "args" in
       shallow handle
         "k" "v";;;
       (fun '("Recv" _), "k" => "send" ("k", "n"));
       (fun '("Send" _), _ => raise exception "Protocol_violation" ()) }>
  in
  <{ fun "k" => let fix "send" "args" := send with "recv" "args" := recv in "send" ("k", ()) }>.

Example run_send_recv1 :=
  <{ let "stdout" := ref () in
     let "print" := print in
     send_recv_protocol
       (fun _ =>
          let "eff" := effect "Send" 42 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          let "eff" := effect "Recv" () in
          let _ := "print" "eff" in
          let "n" := perform "eff" in
          let _ := "print" "n" in
          let "eff" := effect "Send" 43 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          let "eff" := effect "Recv" () in
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
          let "eff" := effect "Send" 0 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          let "eff" := effect "Send" 1 in
          let _ := "print" "eff" in
          let _ := perform "eff" in
          ());
     !"stdout" }>.

Compute (eval_term 6 run_send_recv2).

Example atomically :=
  <{ fun "f" =>
       let "comp" :=
         handle
           (try
              ("f" (); fun _ => ());;
            (fun "exn" =>
               "print" "exn";
               (fun "rb" => "rb" (); raise "exn")));;;
         (fun '("Update" "p"), "k" =>
            "print" (effect "Update" "p");
            (fun "rb" =>
               let ("r", "v") := "p" in
               let "old_v" := !"r" in
               "r" <- "v";
               let "k" := "k" () in
               "k" (fun _ => "r" <- "old_v"; "rb" ())))
       in
       "comp" (fun _ => ()) }>.

Example update :=
  <{ fun "p" => perform effect "Update" "p" }>.

Definition int_to_string := TVBuiltin1 "int_to_string".

Example run_transaction :=
  <{ let "stdout" := ref () in
     let "print" := print in
     let "atomically" := atomically in
     let "update" := update in
     let "result" :=
       "atomically"
         (fun _ =>
            let "r" := ref 10 in
            "print" ({TVString "T0: "} ++ {int_to_string <{ !"r" }>});
            try
              ("atomically"
                 (fun _ =>
                    "update" ("r", 20);
                    "update" ("r", 21);
                    "print" ({TVString "T1, before abort: "} ++ {int_to_string <{ !"r" }>});
                    raise (exception "Result" !"r");
                    "print" ({TVString "T1, after abort: "} ++  {int_to_string <{ !"r" }>});
                    "update" ("r", 30)));;
            (fun '("Result" "v") =>
               "print" ({TVString "T0, T1 aborted: "} ++  {int_to_string "v"});
               "print" ({TVString "T0: "} ++ {int_to_string <{ !"r" }>})))
     in
     !"stdout" }>.

Compute run_transaction.
Compute (eval_term 10 run_transaction).

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
     let "i" := ref 0 in
     let "r" := ref () in
     while (!"i" < k) do
       (let "v" := "it" () in
        "r" <- ("v", !"r");
        "i" <- !"i" + 1);
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

Example make_lazy :=
  <{ fun "g" => ref (`"Delayed" "g") }>.

Example pure_lazy :=
  <{ fun "a" => ref (`"Evaluated" "a") }>.

Example get_lazy :=
  <{ fun "t" =>
       match !"t" with
       | `"Delayed" "g" =>
           let "a" := "g" () in
           let _ := "t" <- `"Evaluated" "a" in
           "a"
       | `"Evaluated" "a" => "a"
       end }>.

Example lazy_module t :=
  <{ let "make_lazy" := make_lazy in
     let "pure_lazy" := pure_lazy in
     let "get_lazy" := get_lazy in
     t }>.

Example nil_stream :=
  <{ "pure_lazy" (Inl ()) }>.

Example empty_queue :=
  <{ `("nil_stream", Inl (), "nil_stream") }>.

Example is_empty_queue :=
  <{ fun "q" =>
       let `("f", _, _) := "q" in
       let "f" := "get_lazy" "f" in
       match "f" with
       | Inl _ => true
       | Inr _ => false
       end }>.

Example rotate_queue :=
  <{ fix "rotate_queue" "q" :=
       let `("f", "r", "a") := "q" in
       let "f" := "get_lazy" "f" in
       match "f" with
       | Inl _ =>
           match "r" with
           | Inl _ => raise exception "Failure" ()
           | Inr "p" => "pure_lazy" (Inr (fst "p", "a"))
           end
       | Inr "p" =>
           let ("x", "f") := "p" in
           match "r" with
           | Inl _ => raise exception "Failure" ()
           | Inr "p" =>
               let ("y", "r") := "p" in
               let "a" := "pure_lazy" (Inr ("y", "a")) in
               let "t" _ :=
                 let "q" := "rotate_queue" `("f", "r", "a") in
                 Inr ("x", "q")
               in
               "make_lazy" "t"
           end
       end }>.

Example exec_queue :=
  <{ fun "q" =>
       let `("f", "r", "s") := "q" in
       let "s" := "get_lazy" "s" in
       match "s" with
       | Inl _ =>
           let "f'" := "rotate_queue" `("f", "r", "nil_stream") in
           `("f'", Inl (), "f'")
       | Inr "p" => `("f", "r", snd "p")
       end }>.

Example snoc_queue :=
  <{ fun "args" =>
       let ("y", "q") := "args" in
       let `("f", "r", "s") := "q" in
       "exec_queue" `("f", Inr ("y", "r"), "s") }>.

Example head_queue :=
  <{ fun "q" =>
       let `("f", _, _) := "q" in
       let "f" := "get_lazy" "f" in
       match "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => fst "p"
       end }>.

Example tail_queue :=
  <{ fun "q" =>
       let `("f", "r", "s") := "q" in
       let "f" := "get_lazy" "f" in
       match "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => "exec_queue" `(snd "p", "r", "s")
       end }>.

Example queue_module t :=
  lazy_module
    <{ let "nil_stream" := nil_stream in
       let "empty_queue" := empty_queue in
       let "is_empty_queue" := is_empty_queue in
       let "rotate_queue" := rotate_queue in
       let "exec_queue" := exec_queue in
       let "snoc_queue" := snoc_queue in
       let "head_queue" := head_queue in
       let "tail_queue" := tail_queue in
       t }>.

Example use_queue xs t :=
  <{ let "ref_xs" := ref xs in
     let "ref_q" := ref "empty_queue" in
     let _ :=
       try
         (while true do
            (match !"ref_xs" with
             | Inl _ => raise exception "Exit" ()
             | Inr "p" =>
                 let ("x", "xs'") := "p" in
                 let "q" := "snoc_queue" ("x", !"ref_q") in
                 "ref_q" <- "q";
                 "ref_xs" <- "xs'"
             end));;
       (fun '("Exit" _) => ())
     in t }>.

Example queue_display xs :=
  queue_module (use_queue xs <{ !"ref_q" }>).

Example queue_reverse xs :=
  queue_module
    (use_queue xs
     <{ let _ := "ref_xs" <- Inl () in
        let _ :=
          try
            (while true do
               (let "q" := !"ref_q" in
                let "mt" := "is_empty_queue" "q" in
                if "mt" then
                  raise exception "Exit" ()
                else
                  let "x" := "head_queue" "q" in
                  let "q" := "tail_queue" "q" in
                  "ref_xs" <- Inr ("x", !"ref_xs");
                  "ref_q" <- "q"));;
          (fun '("Exit" _) => ())
        in
        !"ref_xs" }>).

Compute (eval_term 100 (queue_display (term_of_list (sequence 0 20)))).
Compute (list_eval_term 2000 (queue_reverse (term_of_list (sequence 0 1000)))).

Extraction Language OCaml.
(*Extraction "interpreter.ml" run_term.*)
Recursive Extraction run_term.
