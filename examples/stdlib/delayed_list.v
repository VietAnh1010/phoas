From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example DelayedList :=
  <{ let "empty" _ := Inl () in
     let fix "take_aux" ("n", "xs") :=
       if "n" = 0 then "empty"
       else
         fun _ =>
           match "xs" () with
           | Inl _ => Inl ()
           | Inr ("x", "xs'") => Inr ("x", by "take_aux" ("n" - 1, "xs'"))
           end
     in
     let "take" "args" :=
       if fst "args" < 0 then raise `"Invalid_argument" {TVString "DelayedList.take"}
       else "take_aux" "args"
     in
     let "map" ("f", "xs") :=
       let fix "go" "xs" _ :=
         match "xs" () with
         | Inl _ => Inl ()
         | Inr ("x", "xs'") =>
             let "y" := "f" "x" in
             Inr ("y", by "go" "xs'")
         end
       in
       "go" "xs"
     in
     let "iter" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" () with
         | Inl _ => ()
         | Inr ("x", "xs'") => "f" "x"; "go" "xs'"
         end
       in
       "go" "xs"
     in
     let fix "to_list" "xs" :=
       match "xs" () with
       | Inl _ => Inl ()
       | Inr ("x", "xs'") =>
           let "r" := "to_list" "xs'" in
           Inr ("x", "r")
       end
     in
     `{ "empty"
      ; "take"
      ; "map"
      ; "iter"
      ; "to_list" } }>.
