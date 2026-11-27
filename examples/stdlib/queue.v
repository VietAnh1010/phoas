From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Queue :=
  <{ let "create" () :=
       let "first" := ref `"Nil" in
       `{"length" := ref 0; "first"; "last" := ref "first"}
     in
     let "is_empty" "q" := !"q".`"length" = 0 in
     let "push" ("x", "q") :=
       "q".`"length" <- !"q".`"length" + 1;
       let "next" := ref `"Nil" in
       !"q".`"last" <- `"Cons" ("x", "next");
       "q".`"last" <- "next"
     in
     let "pop" "q" :=
       match !"q".`"first" with
       | `"Nil" => raise `"Empty"
       | `"Cons" ("x", "next") =>
           "q".`"length" <- !"q".`"length" - 1;
           let "cell" := !"next" in
           "q".`"first" <- "cell";
           (if "cell" = `"Nil" then "q".`"last" <- "q".`"first" else ());
           "x"
       end
     in
     let "peek" "q" :=
       match !"q".`"first" with
       | `"Nil" => raise `"Empty"
       | `"Cons" ("x", _) => "x"
       end
     in
     let "length" "q" := !"q".`"length" in
     let "clear" "q" :=
       "q".`"length" <- 0;
       "q".`"first" <- `"Nil";
       "q".`"last" <- "q".`"first"
     in
     let "copy" "q" :=
       let "first" := ref `"Nil" in
       let fix "go" ("curr", "q_curr") :=
         match !"q_curr" with
         | `"Nil" => `{"length" := ref !"q".`"length"; "first"; "last" := ref "curr"}
         | `"Cons" ("x", "q_next") =>
             let "next" := ref `"Nil" in
             "curr" <- `"Cons" ("x", "next");
             "go" ("next", "q_next")
         end
       in
       "go" ("first", "q".`"first")
     in
     let "iter" ("f", "q") :=
       let fix "go" "curr" :=
         match !"curr" with
         | `"Nil" => ()
         | `"Cons" ("x", "next") => "f" "x"; "go" "next"
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
