From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

Example DelayedTree :=
  <{ let "fold" `("z", "f", "t") :=
       let fix "go" "t" _ :=
         match "t" () with
         | Inl _ => "z"
         | Inr `("x", "t1", "t2") => "f" `("x", by "go" "t1", by "go" "t2")
         end
       in
       "go" "t"
     in
     let "iter" ("f", "t") :=
       let fix "go" "t" :=
         match "t" () with
         | Inl _ => ()
         | Inr `("x", "t1", "t2") => "f" "x"; "go" "t1"; "go" "t2"
         end
       in
       "go" "t"
     in
     `{ "fold"
      ; "iter" } }>.
