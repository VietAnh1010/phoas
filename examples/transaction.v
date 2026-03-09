From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.
From examples Require Import common.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example get := <{ fun "r" => perform effect "Get" "r" }>.
Example set := <{ fun "args" => perform effect "Set" "args" }>.

Example atomically :=
  <{ fun "f" =>
       let "k" :=
         (handle
            (try
               (let "x" := "f" () in
                fun _ => "x");;
             (fun "e" => fun "rb" => "rb" (); raise "e"));;;
          (fun '("Get" "r"), "k" => "k" !"r");
          (fun '("Set" "p"), "k" => fun "rb" =>
             let ("r", "v") := "p" in
             let "old_v" := !"r" in
             "r" <- "v";
             let "k" := "k" () in
             "k" (fun _ => "r" <- "old_v"; "rb" ())))
       in
       "k" (fun _ => ()) }>.

Example ex1 :=
  <{ let "stdout" := ref (Inl ()) in
     let "print" "v" := "stdout" <- Inr ("v", !"stdout") in
     atomically
       (fun _ =>
          let "r" := ref 10 in
          let "v" := get "r" in
          "print" "v";
          try
            (atomically
               (fun _ =>
                  set ("r", 20);
                  set ("r", 21);
                  let "v" := get "r" in
                  "print" "v";
                  let "v" := get "r" in
                  raise (exception "Result" "v");
                  let "v" := get "r" in
                  "print" "v";
                  set ("r", 30)));;
          (fun '("Result" "v") =>
             "print" "v";
             let "v" := get "r" in
             "print" "v"));
     !"stdout" }>.

Compute (eval_term_to_list_int 100 <{ ex1 }>).
