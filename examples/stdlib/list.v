From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

Example List :=
  <{ let "is_empty" "xs" :=
       match "xs" with
       | Inl _ => true
       | Inr _ => false
       end
     in
     let "ne_head" "xs" :=
       match "xs" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => fst "p"
       end
     in
     let "ne_tail" "xs" :=
       match "xs" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => snd "p"
       end
     in
     let "ne_uncons" "xs" :=
       match "xs" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => "p"
       end
     in
     let "iter" "args" :=
       let ("f", "xs") := "args" in
       let fix "go" "xs" :=
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
     `{ "is_empty"
      ; "ne_head"
      ; "ne_tail"
      ; "ne_uncons"
      ; "iter" } }>.
