From Stdlib Require Import List String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce val.
From examples Require Import common.
From examples.stdlib Require Import queue.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example fork := <{ fun "f" => perform (`"Fork" "f") }>.
Example yield := <{ fun _ => perform (`"Yield" ()) }>.

Example run :=
  <{ fun "f" =>
       let "Queue" := Queue in
       let "q" := "Queue".`"create" () in
       let "enq" "k" := "Queue".`"push" ("k", "q") in
       let "deq" _ :=
         if by "Queue".`"is_empty" "q" then ()
         else (by "Queue".`"pop" "q") ()
       in
       let fix "go" "f" :=
         handle
           (let _ := try ("f" ()) with
                     | _ => ()
                     end in
            "deq" ())
         with
         | (`"Yield" _) "k" => "enq" "k"; "deq" ()
         | (`"Fork" "f") "k" => "enq" "k"; "go" "f"
         end
       in
       "go" "f" }>.
