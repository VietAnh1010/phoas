From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example List :=
  <{ let "is_empty" "xs" :=
       match "xs" with
       | [] => true
       | _ :: _ => false
       end
     in
     let "ne_head" "xs" :=
       match "xs" with
       | [] => raise `"Empty"
       | "x" :: _ => "x"
       end
     in
     let "ne_tail" "xs" :=
       match "xs" with
       | [] => raise `"Empty"
       | _ :: "xs'" => "xs'"
       end
     in
     let "ne_uncons" "xs" :=
       match "xs" with
       | [] => raise `"Empty"
       | "x" :: "xs'" => ("x", "xs'")
       end
     in
     let "iter" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | [] => ()
         | "x" :: "xs'" => "f" "x"; "go" "xs'"
         end
       in
       "go" "xs"
     in
     let "fold_right" `("f", "z", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | [] => "z"
         | "x" :: "xs'" =>
             let "r" := "go" "xs'" in
             "f" ("x", "r")
         end
       in
       "go" "xs"
     in
     let "fold_left" `("f", "z", "xs") :=
       let fix "go" ("acc", "xs") :=
         match "xs" with
         | [] => "acc"
         | "x" :: "xs'" =>
             let "acc" := "f" ("acc", "x") in
             "go" ("acc", "xs'")
         end
       in
       "go" ("z", "xs")
     in
     let "map" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | [] => []
         | "x" :: "xs'" =>
             let "y" := "f" "x" in
             let "r" := "go" "xs'" in
             "y" :: "r"
         end
       in
       "go" "xs"
     in
     let "filter" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | [] => []
         | "x" :: "xs'" =>
             let "b" := "f" "x" in
             if "b" then
               let "r" := "go" "xs'" in
               "x" :: "r"
             else "go" "xs'"
         end
       in
       "go" "xs"
     in
     let "filter_map" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | [] => []
         | "x" :: "xs'" =>
             let "o" := "f" "x" in
             match "o" with
             | Inl () => "go" "xs'"
             | Inr "y" =>
                 let "r" := "go" "xs'" in
                 "y" :: "r"
             end
         end
       in
       "go" "xs"
     in
     let "append" ("xs", "ys") :=
       let fix "go" "xs" :=
         match "xs" with
         | [] => "ys"
         | "x" :: "xs'" => "x" :: by ("go" "xs'")
         end
       in
       "go" "xs"
     in
     let fix "reverse_append" ("xs", "ys") :=
       match "xs" with
       | [] => "ys"
       | "x" :: "xs'" => "reverse_append" ("xs'", "x" :: "ys")
       end
     in
     let "reverse" "xs" := "reverse_append" ("xs", []) in
     let "length" "xs" :=
       let fix "go" ("acc", "xs") :=
         match "xs" with
         | [] => "acc"
         | _ :: "xs'" => "go" ("acc" + 1, "xs'")
         end
       in
       "go" (0, "xs")
     in
     let "map2" `("f", "xs", "ys") :=
       let fix "go" ("xs", "ys") :=
         match "xs" with
         | [] => []
         | "x" :: "xs'" =>
             match "ys" with
             | [] => []
             | "y" :: "ys'" =>
                 let "z" := "f" ("x", "y") in
                 let "r" := "go" ("xs'", "ys'") in
                 "z" :: "r"
             end
         end
       in
       "go" ("xs", "ys")
     in
     let fix "zip" ("xs", "ys") :=
       match "xs" with
       | [] => []
       | "x" :: "xs'" =>
           match "ys" with
           | [] => []
           | "y" :: "ys'" => ("x", "y") :: by ("zip" ("xs'", "ys'"))
           end
       end
     in
     `{ "is_empty"
      ; "ne_head"
      ; "ne_tail"
      ; "ne_uncons"
      ; "iter"
      ; "fold_right"
      ; "fold_left"
      ; "map"
      ; "filter"
      ; "filter_map"
      ; "append"
      ; "reverse_append"
      ; "reverse"
      ; "length"
      ; "map2"
      ; "zip" } }>.
