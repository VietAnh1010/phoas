From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Stack :=
  <{ let "create" _ :=
       `{"length" := ref 0; "contents" := ref []}
     in
     let "is_empty" "s" := !"s".`"length" = 0 in
     let "push" ("x", "s") :=
       let _ := "s".`"length" <- !"s".`"length" + 1 in
       "s".`"contents" <- "x" :: !"s".`"contents"
     in
     let "pop" "s" :=
       match !"s".`"contents" with
       | [] => raise (`"Empty" ())
       | "x" :: "xs" =>
           let _ := "s".`"length" <- !"s".`"length" - 1 in
           let _ := "s".`"contents" <- "xs" in
           "x"
       end
     in
     let "peek" "s" :=
       match !"s".`"contents" with
       | [] => raise (`"Empty" ())
       | "x" :: _ => "x"
       end
     in
     let "length" "s" := !"s".`"length" in
     let "clear" "s" :=
       let _ := "s".`"length" <- 0 in
       "s".`"contents" <- []
     in
     let "copy" "s" :=
       `{"length" := ref !"s".`"length"; "contents" := ref !"s".`"contents"}
     in
     let "iter" ("f", "s") :=
       let fix "go" "xs" :=
         match "xs" with
         | [] => ()
         | "x" :: "xs'" => "f" "x"; "go" "xs'"
         end
       in
       "go" !"s".`"contents"
     in
     `{ "create"
      ; "is_empty"
      ; "push"
      ; "pop"
      ; "peek"
      ; "length"
      ; "clear" } }>.
