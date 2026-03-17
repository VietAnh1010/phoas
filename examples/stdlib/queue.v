From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Queue :=
  <{ let "create" _ :=
       let "q" := `{"length" := ref 0; "head" := ref (); "tail" := ref ()} in
       let _ := "q".`"tail" <- "q".`"head" in
       "q"
     in
     let "is_empty" "q" := !"q".`"length" = 0 in
     let "push" ("x", "q") :=
       let "node" := `{"content" := "x"; "next" := ref ()} in
       let _ := "q".`"length" <- !"q".`"length" + 1 in
       let _ := !"q".`"tail" <- "node" in
       "q".`"tail" <- "node".`"next"
     in
     let "pop" "q" :=
       if !"q".`"length" = 0 then raise `"Empty" ()
       else
         let "node" := !"q".`"head" in
         "q".`"length" <- !"q".`"length" - 1;
         "q".`"head" <- !"node".`"next";
         if !"q".`"length" = 0 then "q".`"tail" <- "q".`"head" else ();
         "node".`"content"
     in
     let "peek" "q" :=
       if !"q".`"length" = 0 then raise `"Empty" ()
       else !"q".`"head".`"content"
     in
     let "length" "q" := !"q".`"length" in
     let "clear" "q" :=
       let _ := "q".`"length" <- 0 in
       let _ := "q".`"head" <- () in
       "q".`"tail" <- "q".`"head"
     in
     `{ "create"
      ; "is_empty"
      ; "push"
      ; "pop"
      ; "peek"
      ; "length"
      ; "clear" } }>.
