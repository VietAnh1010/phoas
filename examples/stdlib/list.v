From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

Example List :=
  <{ let "ne_tail" "xs" :=
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
     `{ "ne_tail"
      ; "ne_uncons" } }>.
