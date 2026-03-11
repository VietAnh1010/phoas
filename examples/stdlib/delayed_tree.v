From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

Example DelayedTree :=
  <{ let "fold" "args" :=
       let `("z", "f", "t") := "args" in
       let fix "go" "t" _ :=
         let "t" := "t" () in
         match "t" with
         | Inl _ => "z"
         | Inr "t" =>
             let `("x", "t1", "t2") := "t" in
             "f" `("x", by "go" "t1", by "go" "t2")
         end
       in
       "go" "t"
     in
     let "iter" "args" :=
       let ("f", "t") := "args" in
       let fix "go" "t" :=
         let "t" := "t" () in
         match "t" with
         | Inl _ => ()
         | Inr "t" =>
             let `("x", "t1", "t2") := "t" in
             let _ := "f" "x" in
             let _ := "go" "t1" in
             "go" "t2"
         end
       in
       "go" "t"
     in
     `{ "fold"
      ; "iter" } }>.
