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
       let "f" := "Lazy".`"get" "f" in
       match "f" with
       | Inl _ => true
       | Inr _ => false
       end
     in
     let fix "rotate" "q" :=
       let `("f", "r", "s") := "q" in
       let "f" := "Lazy".`"get" "f" in
       match "f" with
       | Inl _ =>
           let "y" := "List".`"ne_head" "r" in
           "Lazy".`"pure" (Inr ("y", "s"))
       | Inr "p" =>
           let ("x", "f") := "p" in
           let "p" := "List".`"ne_uncons" "r" in
           let ("y", "r") := "p" in
           "Lazy".`"make"
             (fun _ =>
                let "s" := "Lazy".`"pure" (Inr ("y", "s")) in
                let "s" := "rotate" `("f", "r", "s") in
                Inr ("x", "s"))
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
       let "f" := "Lazy".`"get" "f" in
       match "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => fst "p"
       end
     in
     let "tail" "q" :=
       let `("f", "r", "s") := "q" in
       let "f" := "Lazy".`"get" "f" in
       match "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" => "exec" `(snd "p", "r", "s")
       end
     in
     let "uncons" "q" :=
       let `("f", "r", "s") := "q" in
       let "f" := "Lazy".`"get" "f" in
       match "f" with
       | Inl _ => raise exception "Empty" ()
       | Inr "p" =>
           let ("x", "f") := "p" in
           let "q" := "exec" `("f", "r", "s") in
           ("x", "q")
       end
     in
     `{ "empty"
      ; "is_empty"
      ; "snoc"
      ; "head"
      ; "tail"
      ; "uncons" } }>.
