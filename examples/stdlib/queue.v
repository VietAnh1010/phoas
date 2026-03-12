From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

(** Require Lazy. *)
Example Queue :=
  <{ let "empty" :=
       let "f" := "Lazy".`"pure" (Inl ()) in
       `("f", Inl (), "f")
     in
     let "is_empty" `("f", _, _) :=
       match "Lazy".`"get" "f" with
       | Inl _ => true
       | Inr _ => false
       end
     in
     let fix "rotate" `("f", Inr ("y", "r"), "s") :=
       let "s" := "Lazy".`"pure" (Inr ("y", "s")) in
       match "Lazy".`"get" "f" with
       | Inl _ => "s"
       | Inr ("x", "f") => "Lazy".`"make" (fun _ => Inr ("x", by "rotate" `("f", "r", "s")))
       end
     in
     let "exec" `("f", "r", "s") :=
       match "Lazy".`"get" "s" with
       | Inl _ =>
           let "f" := "rotate" "q" in
           `("f", Inl (), "f")
       | Inr "p" => `("f", "r", snd "p")
       end
     in
     let "snoc" (`("f", "r", "s"), "x") :=
       "exec" `("f", Inr ("x", "r"), "s")
     in
     let "head" `("f", _, _) :=
       match "Lazy".`"get" "f" with
       | Inl _ => raise `"Empty" ()
       | Inr "p" => fst "p"
       end
     in
     let "tail" `("f", "r", "s") :=
       match "Lazy".`"get" "f" with
       | Inl _ => raise `"Empty" ()
       | Inr "p" => "exec" `(snd "p", "r", "s")
       end
     in
     let "uncons" `("f", "r", "s") :=
       match "Lazy".`"get" "f" with
       | Inl _ => raise `"Empty" ()
       | Inr ("x", "f") => ("x", by "exec" `("f", "r", "s"))
       end
     in
     `{ "empty"
      ; "is_empty"
      ; "snoc"
      ; "head"
      ; "tail"
      ; "uncons" } }>.
