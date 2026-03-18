From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope string_scope.
Local Open Scope term_scope.

Example DelayedTree :=
  <{ let "fold" `("f", "z", "t") :=
       let fix "go" "t" _ :=
         let "t" := "t" () in
         match "t" with
         | Inl _ => "z"
         | Inr `("x", "t1", "t2") => "f" `("x", by "go" "t1", by "go" "t2")
         end
       in
       "go" "t"
     in
     let "iter" ("f", "t") :=
       let fix "go" "t" :=
         let "t" := "t" () in
         match "t" with
         | Inl _ => ()
         | Inr `("x", "t1", "t2") => "f" "x"; "go" "t1"; "go" "t2"
         end
       in
       "go" "t"
     in
     let "map" ("f", "t") :=
       let fix "go" "t" _ :=
         let "t" := "t" () in
         match "t" with
         | Inl _ => Inl ()
         | Inr `("x", "t1", "t2") =>
             let "y" := "f" "x" in
             Inr `("y", by "go" "t1", by "go" "t2")
         end
       in
       "go" "t"
     in
     `{ "fold"
      ; "iter"
      ; "map" } }>.
