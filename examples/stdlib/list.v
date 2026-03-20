From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example List :=
  <{ let "is_empty" "xs" :=
       match "xs" with
       | Inl _ => true
       | Inr _ => false
       end
     in
     let "ne_head" "xs" :=
       match "xs" with
       | Inl _ => raise `"Empty" ()
       | Inr ("x", _) => "x"
       end
     in
     let "ne_tail" "xs" :=
       match "xs" with
       | Inl _ => raise `"Empty" ()
       | Inr (_, "xs'") => "xs'"
       end
     in
     let "ne_uncons" "xs" :=
       match "xs" with
       | Inl _ => raise `"Empty" ()
       | Inr "p" => "p"
       end
     in
     let "iter" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => ()
         | Inr ("x", "xs'") => "f" "x"; "go" "xs'"
         end
       in
       "go" "xs"
     in
     let "foldr" `("f", "z", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => "z"
         | Inr ("x", "xs'") =>
             let "r" := "go" "xs'" in
             "f" ("x", "r")
         end
       in
       "go" "xs"
     in
     let "foldl" `("f", "z", "xs") :=
       let fix "go" ("acc", "xs") :=
         match "xs" with
         | Inl _ => "z"
         | Inr ("x", "xs'") =>
             let "acc'" := "f" ("acc", "x") in
             "go" ("acc'", "xs'")
         end
       in
       "go" ("z", "xs")
     in
     let "map" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => Inl ()
         | Inr ("x", "xs'") =>
             let "y" := "f" "x" in
             let "r" := "go" "xs'" in
             Inr ("y", "r")
         end
       in
       "go" "xs"
     in
     let "filter" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => Inl ()
         | Inr ("x", "xs'") =>
             let "b" := "f" "x" in
             if "b" then
               let "r" := "go" "xs'" in
               Inr ("x", "r")
             else "go" "xs'"
         end
       in
       "go" "xs"
     in
     let "filter_map" ("f", "xs") :=
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => Inl ()
         | Inr ("x", "xs'") =>
             let "o" := "f" "x" in
             match "o" with
             | Inl _ => "go" "xs'"
             | Inr "y" =>
                 let "r" := "go" "xs'" in
                 Inr ("y", "r")
             end
         end
       in
       "go" "xs"
     in
     let "append" ("xs", "ys") :=
       let fix "go" "xs" :=
         match "xs" with
         | Inl _ => "ys"
         | Inr ("x", "xs'") => Inr ("x", by "go" "xs'")
         end
       in
       "go" "xs"
     in
     let "reverse" "xs" :=
       let fix "go" ("acc", "xs") :=
         match "xs" with
         | Inl _ => "acc"
         | Inr ("x", "xs'") => "go" (Inr ("x", "acc"), "xs'")
         end
       in
       "go" (Inl (), "xs")
     in
     let "length" "xs" :=
       let fix "go" ("acc", "xs") :=
         match "xs" with
         | Inl _ => "acc"
         | Inr (_, "xs'") => "go" ("acc" + 1, "xs'")
         end
       in
       "go" "xs"
     in
     let "map2" `("f", "xs", "ys") :=
       let fix "go" "args" :=
         match "args" with
         | Inr ("x", "xs"), Inr ("y", "ys") =>
             let "z" := "f" ("x", "y") in
             let "r" := "go" ("xs", "ys") in
             Inr ("z", "r")
         | _ => Inl ()
         end
       in
       "go" ("xs", "ys")
     in
     let fix "zip" "args" :=
       match "args" with
       | Inr ("x", "xs"), Inr ("y", "ys") => Inr (("x", "y"), by "zip" ("xs", "ys"))
       | _ => Inl ()
       end
     in
     `{ "is_empty"
      ; "ne_head"
      ; "ne_tail"
      ; "ne_uncons"
      ; "iter"
      ; "foldr"
      ; "foldl"
      ; "map"
      ; "filter"
      ; "filter_map"
      ; "append"
      ; "reverse"
      ; "length"
      ; "map2"
      ; "zip" } }>.
