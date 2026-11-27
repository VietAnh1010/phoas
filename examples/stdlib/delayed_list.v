From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example DelayedList :=
  <{ let "empty" () := `"Nil" in
     let fix "take_aux" ("n", "xs") :=
       if "n" = 0 then "empty"
       else
         fun () =>
           let "xs" := "xs" () in
           match "xs" with
           | `"Nil" => `"Nil"
           | `"Cons" ("x", "xs'") => `"Cons" ("x", by ("take_aux" ("n" - 1, "xs'")))
           end
     in
     let "take" ("n", "xs") :=
       if "n" < 0 then raise (`"Invalid_argument" ('"DelayedList.take", "n"))
       else "take_aux" ("n", "xs")
     in
     let "map" ("f", "xs") :=
       let fix "go" "xs" () :=
         let "xs" := "xs" () in
         match "xs" with
         | `"Nil" => `"Nil"
         | `"Cons" ("x", "xs'") =>
             let "y" := "f" "x" in
             `"Cons" ("y", by ("go" "xs'"))
         end
       in
       "go" "xs"
     in
     let "map2" `("f", "xs", "ys") :=
       let fix "go" ("xs", "ys") () :=
         let "xs" := "xs" () in
         match "xs" with
         | `"Nil" => `"Nil"
         | `"Cons" ("x", "xs'") =>
             let "ys" := "ys" () in
             match "ys" with
             | `"Nil" => `"Nil"
             | `"Cons" ("y", "ys'") =>
                 let "z" := "f" ("x", "y") in
                 `"Cons" ("z", by ("go" ("xs'", "ys'")))
             end
         end
       in
       "go" ("xs", "ys")
     in
     let "iter" ("f", "xs") :=
       let fix "go" "xs" :=
         let "xs" := "xs" () in
         match "xs" with
         | `"Nil" => ()
         | `"Cons" ("x", "xs'") => "f" "x"; "go" "xs'"
         end
       in
       "go" "xs"
     in
     let fix "to_list" "xs" :=
       let "xs" := "xs" () in
       match "xs" with
       | `"Nil" => []
       | `"Cons" ("x", "xs'") =>
           let "r" := "to_list" "xs'" in
           "x" :: "r"
       end
     in
     `{ "empty"
      ; "take"
      ; "map"
      ; "map2"
      ; "iter"
      ; "to_list" } }>.
