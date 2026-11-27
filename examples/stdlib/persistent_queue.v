From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope string_scope.
Local Open Scope term_scope.

(** Require Lazy. *)
Example PersistentQueue :=
  <{ let "empty" :=
       let "f" := "Lazy".`"pure" `"Nil" in
       `("f", [], "f")
     in
     let "is_empty" `("f", _, _) :=
       match by ("Lazy".`"get" "f") with
       | `"Nil" => true
       | `"Cons" _ => false
       end
     in
     let fix "rotate" `("f", "y" :: "r", "s") :=
       let "s" := "Lazy".`"pure" (`"Cons" ("y", "s")) in
       match by ("Lazy".`"get" "f") with
       | `"Nil" => "s"
       | `"Cons" ("x", "f'") =>
           "Lazy".`"make" (fun () => `"Cons" ("x", by ("rotate" `("f'", "r", "s"))))
       end
     in
     let "exec" `("f", "r", "s") :=
       match by ("Lazy".`"get" "s") with
       | `"Nil" =>
           let "f" := "rotate" `("f", "r", "s") in
           `("f", [], "f")
       | `"Cons" (_, "s'") => `("f", "r", "s'")
       end
     in
     let "snoc" (`("f", "r", "s"), "x") :=
       "exec" `("f", "x" :: "r", "s")
     in
     let "ne_head" `("f", _, _) :=
       match by ("Lazy".`"get" "f") with
       | `"Nil" => raise `"Empty"
       | `"Cons" ("x", _) => "x"
       end
     in
     let "ne_tail" `("f", "r", "s") :=
       match by ("Lazy".`"get" "f") with
       | `"Nil" => raise `"Empty"
       | `"Cons" (_, "f'") => "exec" `("f'", "r", "s")
       end
     in
     let "ne_uncons" `("f", "r", "s") :=
       match by ("Lazy".`"get" "f") with
       | `"Nil" => raise `"Empty"
       | `"Cons" ("x", "f'") => ("x", by ("exec" `("f'", "r", "s")))
       end
     in
     `{ "empty"
      ; "is_empty"
      ; "snoc"
      ; "ne_head"
      ; "ne_tail"
      ; "ne_uncons" } }>.
