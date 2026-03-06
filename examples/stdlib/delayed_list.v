From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example DelayedList :=
  <{ let "iter" "args" :=
       let ("f", "xs") := "args" in
       let fix "go" "xs" :=
         let "xs" := "xs" () in
         match "xs" with
         | Inl _ => ()
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let _ := "f" "x" in
             "go" "xs'"
         end
       in
       "go" "xs"
     in
     let "map" "args" :=
       let ("f", "xs") := "args" in
       let fix "go" "xs" _ :=
         let "xs" := "xs" () in
         match "xs" with
         | Inl _ => Inl ()
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "y" := "f" "x" in
             let "r" := "go" "xs'" in
             Inr ("y", "r")
         end
       in
       "go" "xs"
     in
     let fix "take_aux" "args" _ :=
       let ("n", "xs") := "args" in
       if "n" = 0 then Inl ()
       else
         let "xs" := "xs" () in
         match "xs" with
         | Inl _ => Inl ()
         | Inr "p" =>
             let ("x", "xs'") := "p" in
             let "r" := "take_aux" ("n" - 1, "xs'") in
             Inr ("x", "r")
         end
     in
     let "take" "args" :=
       if fst "args" < 0 then raise exception "Invalid_argument" {TVString "DelayedList.take"}
       else "take_aux" "args"
     in
     let fix "to_list" "xs" :=
       let "xs" := "xs" () in
       match "xs" with
       | Inl _ => Inl ()
       | Inr "p" =>
           let ("x", "xs'") := "p" in
           let "r" := "to_list" "xs'" in
           Inr ("x", "r")
       end
     in
     `{ "iter"
      ; "map"
      ; "take"
      ; "to_list" } }>.
