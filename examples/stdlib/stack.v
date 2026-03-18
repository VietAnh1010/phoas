From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Stack :=
  <{ let "create" _ :=
       `{"length" := ref 0; "contents" := ref (Inl ())}
     in
     let "is_empty" "s" := !"s".`"length" = 0 in
     let "push" ("x", "s") :=
       let _ := "s".`"length" <- !"s".`"length" + 1 in
       "s".`"contents" <- Inr ("x", !"s".`"contents")
     in
     let "pop" "s" :=
       match !"s".`"contents" with
       | Inl _ => raise `"Empty" ()
       | Inr ("x", "xs") =>
           let _ := "s".`"length" <- !"s".`"length" - 1 in
           let _ := "s".`"contents" <- "xs" in
           "x"
       end
     in
     let "peek" "s" :=
       match !"s".`"contents" with
       | Inl _ => raise `"Empty" ()
       | Inr ("x", _) => "x"
       end
     in
     let "length" "s" := !"s".`"length" in
     let "clear" "s" :=
       let _ := "s".`"length" <- 0 in
       "s".`"contents" <- Inl ()
     in
     `{ "create"
      ; "is_empty"
      ; "push"
      ; "pop"
      ; "peek"
      ; "length"
      ; "clear" } }>.
