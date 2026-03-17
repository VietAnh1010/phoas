From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.
From shift_reset.interpreter Require Import interpreter.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example get := <{ fun _ => shift (fun "k" => fun "s" => (by "k" "s") "s") }>.
Example put := <{ fun "s" => shift (fun "k" => fun _ => (by "k" ()) "s") }>.

Example eval_state :=
  <{ fun ("m", "s") => (by reset let "v" := "m" () in fun "s" => ("v", "s")) "s" }>.

Example ex1 :=
  <{ fun _ =>
       let "v1" := get () in
       let _ := put ("v1" + 10) in
       let "v2" := get () in
       let _ := put ("v2" * 2) in
       let "v3" := get () in
       `("v1", "v2", "v3") }>.

Compute (eq_refl : eval_term 100 <{ eval_state (ex1, 5) }> = eval_term 1 <{ `(5, 15, 30), 30 }>).
