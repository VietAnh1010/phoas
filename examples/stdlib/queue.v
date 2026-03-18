From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Queue :=
  <{ let "create" _ :=
       let "first" := ref (Inl ()) in
       `{"length" := ref 0; "first"; "last" := ref "first"}
     in
     let "is_empty" "q" := !"q".`"length" = 0 in
     let "push" ("x", "q") :=
       let _ := "q".`"length" <- !"q".`"length" + 1 in
       let "next" := ref (Inl ()) in
       let _ := !"q".`"last" <- Inr `{"content" := "x"; "next"} in
       "q".`"last" <- "next"
     in
     let "pop" "q" :=
       match !"q".`"first" with
       | Inl _ => raise `"Empty" ()
       | Inr `{"content"; "next"} =>
           let _ := "q".`"length" <- !"q".`"length" - 1 in
           let "cell" := !"next" in
           let _ := "q".`"first" <- "cell" in
           let _ := if "cell" = Inl () then "q".`"last" <- "q".`"first" else () in
           "content"
       end
     in
     let "peek" "q" :=
       match !"q".`"first" with
       | Inl _ => raise `"Empty" ()
       | Inr `{"content"; .._} => "content"
       end
     in
     let "length" "q" := !"q".`"length" in
     let "clear" "q" :=
       let _ := "q".`"length" <- 0 in
       let _ := "q".`"first" <- Inl () in
       "q".`"last" <- "q".`"first"
     in
     let "copy" "q" :=
       let "first" := ref (Inl ()) in
       let fix "go" ("curr", "q_curr") :=
         match !"q_curr" with
         | Inl _ => `{"length" := ref !"q".`"length"; "first"; "last" := ref "curr"}
         | Inr `{"content"; "next" := "q_next"} =>
             let "next" := ref (Inl ()) in
             let _ := "curr" <- Inr `{"content"; "next"} in
             "go" ("next", "q_next")
         end
       in
       "go" ("first", "q".`"first")
     in
     let "iter" ("f", "q") :=
       let fix "go" "curr" :=
         match !"curr" with
         | Inl _ => ()
         | Inr `{"content"; "next"} => "f" "content"; "go" "next"
         end
       in
       "go" "q".`"first"
     in
     `{ "create"
      ; "is_empty"
      ; "push"
      ; "pop"
      ; "peek"
      ; "length"
      ; "clear"
      ; "copy"
      ; "iter" } }>.
