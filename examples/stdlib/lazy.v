From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope string_scope.
Local Open Scope term_scope.

Example Lazy :=
  <{ let "pure" "a" := ref (`"Evaluated" "a") in
     let "make" "g" := ref (`"Delayed" "g") in
     let "get" "t" :=
       match !"t" with
       | `"Delayed" "g" =>
           let "a" := "g" () in
           "t" <- `"Evaluated" "a";
           "a"
       | `"Evaluated" "a" => "a"
       end
     in
     let "map" ("f", "t") :=
       "make" (fun () => let "a" := "get" "t" in "f" "a")
     in
     let "bind" ("t", "f") :=
       "make"
         (fun () =>
            let "a" := "get" "t" in
            let "r" := "f" "a" in
            "get" "r")
     in
     `{ "pure"
      ; "make"
      ; "get"
      ; "map"
      ; "bind" } }>.
