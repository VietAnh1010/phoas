From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

(** Require Lazy List. *)
Example Queue :=
  <{ let "empty" :=
       let "f" := "Lazy".`"pure" (Inl ()) in
       `("f", Inl (), "f")
     in
     let "is_empty" "q" :=
       let `("f", _, _) := "q" in
       match by "Lazy".`"get" "f" with
       | Inl _ => true
       | Inr _ => false
       end
     in
     let fix "rotate" "q" :=
       let `("f", "r", "s") := "q" in
       match by "Lazy".`"get" "f" with
       | Inl _ => "Lazy".`"pure" (Inr (by "List".`"ne_head" "r", "s"))
       | Inr "p" =>
           let ("x", "f") := "p" in
           let ("y", "r") := by "List".`"ne_uncons" "r" in
           "Lazy".`"make" (fun _ => Inr ("x", by "rotate" `("f", "r", by "Lazy".`"pure" (Inr ("y", "s")))))
       end
     in
     let "exec" "q" :=
       let `("f", "r", "s") := "q" in
       let "s" := "Lazy".`"get" "s" in
       match "s" with
       | Inl _ =>
           let "f" := "rotate" "q" in
           `("f", Inl (), "f")
       | Inr "p" => `("f", "r", snd "p")
       end
     in
     let "snoc" "args" :=
       let ("q", "x") := "args" in
       let `("f", "r", "s") := "q" in
       "exec" `("f", Inr ("x", "r"), "s")
     in
     let "head" "q" :=
       let `("f", _, _) := "q" in
       match by "Lazy".`"get" "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => fst "p"
       end
     in
     let "tail" "q" :=
       let `("f", "r", "s") := "q" in
       match by "Lazy".`"get" "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => "exec" `(snd "p", "r", "s")
       end
     in
     let "uncons" "q" :=
       let `("f", "r", "s") := "q" in
       match by "Lazy".`"get" "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" =>
           let ("x", "f") := "p" in
           ("x", by "exec" `("f", "r", "s"))
       end
     in
     `{ "empty"
      ; "is_empty"
      ; "snoc"
      ; "head"
      ; "tail"
      ; "uncons" } }>.
