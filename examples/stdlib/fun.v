From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope string_scope.
Local Open Scope term_scope.

Example Fun :=
  <{ let "id" "x" := "x" in
     let "const" "x" _ := "x" in
     let "compose" ("f", "g") "x" :=
       let "r" := "g" "x" in
       "f" "r"
     in
     let "flip" "f" ("x", "y") := "f" ("y", "x") in
     `{ "id"
      ; "const"
      ; "compose"
      ; "flip" } }>.
