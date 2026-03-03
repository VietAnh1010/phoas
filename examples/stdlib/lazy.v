From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

Example Lazy :=
  <{ let "pure" "a" := ref (`"Evaluated" "a") in
     let "make" "g" := ref (`"Delayed" "g") in
     let "get" "t" :=
       match !"t" with
       | `"Delayed" "g" =>
           let "a" := "g" () in
           let _ := "t" <- `"Evaluated" "a" in
           "a"
       | `"Evaluated" "a" => "a"
       end
     in
     let "map" "args" :=
       let ("f", "t") := "args" in
       "make" (fun _ => let "r" := "get" "t" in "f" "r")
     in
     let "bind" "args" :=
       let ("f", "t") := "args" in
       "make" (fun _ =>
                 let "r" := "get" "t" in
                 let "r" := "f" "r" in
                 "get" "r")
     in
     `{ "make" := "make"
      ; "pure" := "pure"
      ; "get" := "get"
      ; "map" := "map"
      ; "bind" := "bind" } }>.
