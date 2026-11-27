From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Stack :=
  <{ let "create" () :=
       `{"length" := ref 0; "contents" := ref []}
     in
     let "is_empty" "s" := !"s".`"length" = 0 in
     let "push" ("x", "s") :=
       "s".`"length" <- !"s".`"length" + 1;
       "s".`"contents" <- "x" :: !"s".`"contents"
     in
     let "pop" "s" :=
       match !"s".`"contents" with
       | [] => raise `"Empty"
       | "x" :: "xs" =>
           "s".`"length" <- !"s".`"length" - 1;
           "s".`"contents" <- "xs";
           "x"
       end
     in
     let "peek" "s" :=
       match !"s".`"contents" with
       | [] => raise `"Empty"
       | "x" :: _ => "x"
       end
     in
     let "length" "s" := !"s".`"length" in
     let "clear" "s" :=
       "s".`"length" <- 0;
       "s".`"contents" <- []
     in
     let "copy" "s" :=
       `{"length" := ref !"s".`"length"; "contents" := ref !"s".`"contents"}
     in
     `{ "create"
      ; "is_empty"
      ; "push"
      ; "pop"
      ; "peek"
      ; "length"
      ; "clear"
      ; "copy" } }>.
